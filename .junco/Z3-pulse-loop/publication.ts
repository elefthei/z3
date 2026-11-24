import { execFile } from 'node:child_process';
import { lstat, open, readFile, realpath, rename, unlink } from 'node:fs/promises';
import { basename, dirname, isAbsolute, join } from 'node:path';
import { homedir } from 'node:os';
import { createHash, randomUUID } from 'node:crypto';
import { StateConflict, type Paths } from './state.ts';

const official = 'https://github.com/Z3Prover/z3.git', fork = 'https://github.com/elefthei/z3.git';
export const branchName = 'feat/fstar-proofs-junco';
const prBranch = 'feat/junco-fstar', master = 'refs/heads/master';
const start = '<!-- pulse-verified-claims:start -->', end = '<!-- pulse-verified-claims:end -->';
export const emptyBlock = `${start}\n## Verified claims\n\nNo formal claims published yet.\n${end}`;
export const digest = (b: Buffer | string) => createHash('sha256').update(b).digest('hex');
export function check(ok: unknown, reason: string): asserts ok { if (!ok) throw new StateConflict(reason); }
export function oid(value: string) { check(/^[0-9a-f]{40}$/.test(value), 'Invalid immutable Git revision'); return value; }
export function parts(body: string) {
  const at = body.indexOf(start), to = body.indexOf(end);
  check(at >= 0 && at === body.lastIndexOf(start) && to > at && to === body.lastIndexOf(end), 'Ambiguous managed claims block');
  return { prefix: body.slice(0,at), block: body.slice(at,to + end.length), suffix: body.slice(to + end.length) };
}
export type Pull = { number: number; html_url: string; state: string; merged: boolean; draft: boolean; user: {login:string}; head: {ref:string;sha:string;repo:{id:number;full_name:string}}; base: {ref:string;repo:{id:number;full_name:string;default_branch:string}}; body: string };
type Api = (pr: number, body?: string, signal?: AbortSignal) => Promise<Pull>;
const hostEnv = { HOME: homedir(), PATH:'/usr/local/bin:/usr/bin:/bin', LC_ALL:'C', GH_PROMPT_DISABLED:'1', GH_HOST:'github.com', GIT_TERMINAL_PROMPT:'0', GIT_NO_REPLACE_OBJECTS:'1', GIT_CONFIG_NOSYSTEM:'1' };
function cmd(cwd:string, exe:string, args:string[], input?: Buffer|string, signal?: AbortSignal, env:NodeJS.ProcessEnv=hostEnv): Promise<Buffer> {
  const {promise,resolve,reject}=Promise.withResolvers<Buffer>();
  const child=execFile(exe,args,{cwd,env,signal,encoding:'buffer',timeout:180_000,maxBuffer:32*1024*1024},(err,out)=>err ? reject(new StateConflict(`${basename(exe)} operation failed (${err.code ?? err.name}); private evidence preserved`)) : resolve(out));
  child.stdin!.on('error',()=>{}); child.stdin!.end(input);
  return promise;
}
const api:Api=async (n, body, signal)=>{
  const endpoint=`repos/Z3Prover/z3/pulls/${n}`;
  const args=body===undefined?['api',endpoint]:['api','--method','PATCH',endpoint,'--input','-'];
  return JSON.parse((await cmd(homedir(),'/usr/bin/gh',args,body===undefined?undefined:JSON.stringify({body}),signal)).toString());
};
export async function atomicJson(path:string, value:unknown) {
  const tmp=join(dirname(path),`.pulse-${randomUUID()}`), fd=await open(tmp,'wx',0o600);
  try { await fd.writeFile(JSON.stringify(value)+'\n'); await fd.sync(); } finally { await fd.close(); }
  try { await rename(tmp,path); const dir=await open(dirname(path),'r'); try { await dir.sync(); } finally { await dir.close(); } }
  catch(e) { await unlink(tmp).catch(()=>{}); throw e; }
}
export type Binding = {version:1; pr:number|null; branch?:typeof branchName; seed:string; head:string; upstream:string; state:string; block:string; iteration:number};
export type Parent = {H:string; M:string; P:string};
export class Publisher {
  readonly url:string;
  private readonly headRef:string;
  private constructor(readonly pr:number|null, readonly repo:string, readonly state:string, private readonly trunk:string, private readonly fork:string, private readonly api?:Api) {
    check(pr===null ? !api : Number.isSafeInteger(pr) && pr>0 && api,'Invalid publication destination');
    this.url=pr===null?'https://github.com/elefthei/z3':`https://github.com/Z3Prover/z3/pull/${pr}`;
    this.headRef=`refs/heads/${pr===null?branchName:prBranch}`;
  }
  commitUrl(id:string) { return `${this.url}/${this.pr===null?'commit':'commits'}/${oid(id)}`; }
  checkBlock(pr:Pull|null, expected:string) {
    check(this.pr===null ? pr===null && expected==='' : pr?.number===this.pr && parts(pr.body).block===expected,'Observed publication target or managed claims block changed');
    return expected;
  }
  static async live(pr:number,p:Paths) {
    check(Number.isSafeInteger(pr)&&pr>0,'Invalid PR number');return this.liveBound(pr,p);
  }
  static liveBranch(p:Paths) { return this.liveBound(null,p); }
  private static async liveBound(pr:number|null,p:Paths) {
    const campaign=pr===null?'fstar-proofs-junco':`pr-${pr}`;
    check(p.state===`/btrfs/Z3-pulse-loop-${campaign}` && basename(p.repo)===`${campaign}-publisher` && dirname(dirname(p.repo))===join(homedir(),'.local/state') && /^z3-pulse-ops\.[A-Za-z0-9]+$/.test(basename(dirname(p.repo))), 'Wrong live publisher or campaign state');
    for(const path of [dirname(p.repo),p.repo,join(p.repo,'.git'),...(pr===null?[p.state]:[])]) {
      const s=await lstat(path).catch((e:NodeJS.ErrnoException)=>{if(path!==p.state || e.code!=='ENOENT')throw e;});
      if(!s) {check(await realpath(dirname(path))===dirname(path),'Campaign state parent must be canonical');continue;}
      check(s.isDirectory() && s.uid===process.getuid!() && !(s.mode&0o077) && await realpath(path)===path,'Publisher and state paths must be private and operator-owned');
    }
    check((await cmd(p.repo,'/usr/bin/gh',['api','user','--jq','.login'])).toString().trim()==='elefthei','Expected active operator elefthei');
    const upstream=JSON.parse((await cmd(p.repo,'/usr/bin/gh',['api','repos/Z3Prover/z3','--jq','{id,default_branch}'])).toString());
    check(upstream.id===32944298 && upstream.default_branch==='master','Official repo or default branch changed');
    if(pr===null) {
      const dest=JSON.parse((await cmd(p.repo,'/usr/bin/gh',['api','repos/elefthei/z3','--jq','{id,full_name,fork,source:.source.id,push:.permissions.push}'])).toString());
      check(dest.id===1426345895 && dest.full_name==='elefthei/z3' && dest.fork===true && dest.source===upstream.id && dest.push===true,'Wrong fork identity, network or push authority');
    }
    return new Publisher(pr,p.repo,p.state,official,fork,pr===null?undefined:api);
  }
  get isFixture() { return this.trunk!==official; }
  // Fixtures can substitute local repositories and an in-process API, never a second network target.
  static async fixture(pr:number,p:Paths,trunk:string,fork:string,api:Api) {
    check(Number.isSafeInteger(pr)&&pr>0,'Invalid PR number');return this.fixtureBound(pr,p,trunk,fork,api);
  }
  static fixtureBranch(p:Paths,trunk:string,fork:string) { return this.fixtureBound(null,p,trunk,fork); }
  private static async fixtureBound(pr:number|null,p:Paths,trunk:string,fork:string,api?:Api) {
    for(const dir of [trunk,fork]) check(isAbsolute(dir) && await realpath(dir)===dir,'Fixture needs literal local repositories');
    return new Publisher(pr,p.repo,p.state,trunk,fork,api);
  }
  async git(args:string[], cwd=this.repo, input?:Buffer|string, signal?:AbortSignal) {
    const net=this.trunk===official;
    const options=['-c','core.hooksPath=/dev/null','-c','core.fsmonitor=false','-c','rerere.enabled=false','-c','gc.auto=0','-c','commit.gpgSign=false','-c','rebase.autoStash=false','-c','rebase.updateRefs=false','-c','credential.helper=','-c','protocol.allow=never','-c','protocol.file.allow=always'];
    if(net) options.push('-c','protocol.https.allow=always','-c','credential.https://github.com.helper=!gh auth git-credential');
    if(net && this.pr===null) options.push('-c','http.followRedirects=false');
    return cmd(cwd,'/usr/bin/git',[...options,...args],input,signal,{...hostEnv,GIT_CONFIG_GLOBAL:'/dev/null'});
  }
  async text(args:string[], cwd=this.repo, signal?:AbortSignal) { return (await this.git(args,cwd,undefined,signal)).toString().trimEnd(); }
  async pull(signal?:AbortSignal,body?:string) {
    check(this.pr!==null && this.api,'Branch-only publication has no pull request');
    const p=await this.api(this.pr,body,signal);
    check(p.base.repo.default_branch==='master','Official default branch changed');
    check(p.number===this.pr && p.html_url===this.url && p.state==='open' && p.merged===false && !p.draft && p.user.login==='elefthei' && p.base.repo.id===32944298 && p.base.repo.full_name==='Z3Prover/z3' && p.base.ref==='master' && p.head.repo.id===1426345895 && p.head.repo.full_name==='elefthei/z3' && `refs/heads/${p.head.ref}`===this.headRef && typeof p.body==='string','PR authority, base, head or state changed'); oid(p.head.sha); return p;
  }
  private async checkTransport(signal?:AbortSignal) {
    if(this.pr!==null) return;
    // A literal push URL can still be redirected by repository-local Git configuration.
    const keys=(await this.text(['config','--name-only','--list'],this.repo,signal)).split('\n');
    check(!keys.some(k=>k.startsWith('url.') || k.startsWith(`remote.${this.fork}.`) || k.startsWith(`remote.${this.trunk}.`)),'Publisher configuration redirects a bound Git destination');
  }
  async observed(signal?:AbortSignal) {
    await this.checkTransport(signal);
    const resolveRef=async(url:string,ref:string)=>{const row=await this.text(['ls-remote','--refs',url,ref],this.repo,signal); const [id,name]=row.split('\t'); check(name===ref,'Missing or ambiguous public ref'); return oid(id!);};
    const [H,M,pr]=await Promise.all([resolveRef(this.fork,this.headRef),resolveRef(this.trunk,master),this.pr===null?null:this.pull(signal)]);
    check(pr===null || H===pr.head.sha,'Fork ref and PR head disagree'); return {H,M,pr,checkedAt:new Date().toISOString()};
  }
  get bindingFile(){return join(this.repo,'.git','pulse-binding.json');}
  async binding():Promise<Binding> {
    const s=await lstat(this.bindingFile); check(s.isFile() && s.uid===process.getuid!() && !(s.mode&0o077) && s.nlink===1,'Untrusted publisher binding');
    const b=JSON.parse(await readFile(this.bindingFile,'utf8')) as Binding;
    check(b.version===1 && b.pr===this.pr && b.state===this.state && Number.isSafeInteger(b.iteration) && b.iteration>=0,'Invalid publisher binding');
    check(this.pr===null ? b.branch===branchName && b.block==='' : b.branch===undefined && parts(b.block).block===b.block,'Wrong bound destination or claims block');
    oid(b.head);oid(b.upstream);oid(b.seed);return b;
  }
  async parent(expected:string,signal?:AbortSignal):Promise<Parent> {
    check(await this.text(['rev-parse','--show-toplevel','--absolute-git-dir'])===`${this.repo}\n${join(this.repo,'.git')}`,'Publisher checkout identity changed');
    for(const path of ['rebase-merge','rebase-apply','MERGE_HEAD','CHERRY_PICK_HEAD','REVERT_HEAD']) {
      const present=await lstat(join(this.repo,'.git',path)).then(()=>true,(e:NodeJS.ErrnoException)=>{if(e.code!=='ENOENT')throw e;return false;});
      check(!present,'Unfinished Git operation in publisher; preserve the checkout');
    }
    const {H,M}=await this.observed(signal); check(H===oid(expected),'Fork head changed outside publisher');
    for(const [url,ref,id] of [[this.trunk,master,M],[this.fork,this.headRef,H]] as const){await this.git(['fetch','--no-tags','--no-recurse-submodules','--',url,ref],this.repo,undefined,signal);check(await this.text(['rev-parse','FETCH_HEAD'])===id,'Public ref moved during fetch');}
    const base=await this.text(['merge-base',H,M]); check(base!==H && !await this.text(['rev-list','--merges',`${base}..${H}`]),'Empty or nonlinear feature history');
    check(!await this.text(['status','--porcelain=v1','--ignored','--untracked-files=all']), 'Dirty publisher checkout');
    await this.git(['switch','--no-overwrite-ignore','--detach',H]);
    await this.git(['rebase','--no-autostash','--no-update-refs','--no-fork-point',M],this.repo,undefined,signal);
    const P=oid(await this.text(['rev-parse','HEAD'])); await this.git(['merge-base','--is-ancestor',M,P]);
    check(await this.text(['rev-list','--count',`${base}..${H}`])===await this.text(['rev-list','--count',`${M}..${P}`]),'Rebase dropped feature commits');
    const ref=`refs/pulse/parents/${H}/${M}`; const retained=await this.text(['for-each-ref','--format=%(objectname)',ref]);
    if(retained) {check(await this.text(['rev-parse',`${retained}^{tree}`])===await this.text(['rev-parse',`${P}^{tree}`]),'Rebased parent differs from retained object'); await this.git(['switch','--no-overwrite-ignore','--detach',retained]);}
    else await this.git(['update-ref',ref,P,'']);
    return {H,M,P:retained||P};
  }
  async push(C:string,H:string,signal?:AbortSignal) {
    await this.checkTransport(signal);
    await this.git(['push','--no-follow-tags','--recurse-submodules=no',`--force-with-lease=${this.headRef}:${oid(H)}`,'--',this.fork,`${oid(C)}:${this.headRef}`],this.repo,undefined,signal);
  }
  // Operator bootstrap only. The running supervisor never learns a cursor from an unbound fork.
  async initialize(expected:string,signal?:AbortSignal) {
    const bound=await lstat(this.bindingFile).then(()=>true,(e:NodeJS.ErrnoException)=>{if(e.code!=='ENOENT')throw e;return false;});
    check(!bound,'Existing publisher binding must be reconciled, not recreated');
    check(await this.text(['rev-parse','HEAD'])===oid(expected),'Bootstrap clone does not match confirmed implementation');
    if(this.trunk===official) for(const key of ['user.name','user.email']) {
      const value=(await cmd(homedir(),'/usr/bin/git',['config','--get',key])).toString().trimEnd();
      check(value && !/[\r\n]/.test(value),'Invalid operator Git identity');
      await this.git(['config','--local',key,value]);
    }
    let block='';
    if(this.pr!==null) {block=parts((await this.pull(signal)).body).block;check(block.replaceAll('\r\n','\n')===emptyBlock,'Initial claims require evidence reconciliation');}
    const {H,M,P}=await this.parent(expected,signal);
    const binding:Binding={version:1,pr:this.pr,...(this.pr===null?{branch:branchName} as const:{}),seed:P,head:H,upstream:M,state:this.state,block,iteration:0};
    const file=await open(this.bindingFile,'wx',0o600); try {await file.writeFile(JSON.stringify(binding)+'\n'); await file.sync();} finally {await file.close();}
    return this.binding();
  }
}
