import { lstat, mkdir, mkdtemp, readFile, readdir, realpath } from 'node:fs/promises';
import { basename, dirname, join } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { evaluatorIdentity, regress, validateScope } from './evaluation.ts';
import { Publisher, type Parent, atomicJson, check, digest, oid } from './publication.ts';
import { current, type Paths } from './state.ts';
import { recoveryLemma } from './recovery-verify.ts';

export type Recovery = Parent & {pr:number|null;evaluator:string;out:string;dir:string;file:string;line:number;name:string;source:string;diagnostic:string};
const exists=(path:string)=>lstat(path).then(()=>true,(e:NodeJS.ErrnoException)=>{if(e.code!=='ENOENT')throw e;return false;});
async function bytes(path:string){check(await realpath(path)===path && (await lstat(path)).isFile(),'Recovery evidence path is aliased or not a file');return readFile(path);}
const json=async(path:string)=>JSON.parse((await bytes(path)).toString());
const evidenceRoot=(p:Paths,t:Parent)=>join(p.state,'proof-recovery',oid(t.H),oid(t.M),oid(t.P));

/** Parse only a strict compiler obligation in a named, implemented lemma. Infrastructure errors are not proofs. */
export function proofDiagnostic(log:string, sourceFor:(module:string)=>string) {
  const plain=log.replace(/\x1b\[[0-9;]*[A-Za-z]/g,'');
  const fatal=[...plain.matchAll(/^\s*\|?\s*F\* verification failed: (Z3[A-Za-z0-9_]+\.fst)\s*$/gm)];
  const errors=[...plain.matchAll(/^\* Error (\d+) at (Z3[A-Za-z0-9_]+\.fst)\((\d+),\d+-\d+,\d+\):\s*$/gm)];
  check(fatal.length===1 && errors.length===1 && fatal[0]![1]===errors[0]![2] && fatal[0]!.index!>errors[0]!.index!,'Not one strict F* proof failure in a registered checker module');
  const m=errors[0]!,module=m[2]!,source=sourceFor(module),line=Number(m[3]),lines=source.split('\n');
  check(line>0 && line<=lines.length,'Compiler error range outside source');
  const error=plain.slice(m.index!+m[0].length,fatal[0]!.index),goal=/^\s*- Failed to prove:\s*([^\r\n]{1,512})\s*$/m.exec(error)?.[1];
  check(goal && /^[\x20-\x7e]+$/.test(goal) && !/https?:|\/home\/|\/btrfs\//.test(goal),'Compiler did not identify a printable proof obligation');
  let i=line-1;for(;i>=0 && !/^(?:let(?:\s+rec)?|and)\s+([A-Za-z_][\w']*)\b/.test(lines[i]!);i--){/* walk to the enclosing implementation */}
  const decl=/^(?:let(?:\s+rec)?|and)\s+([A-Za-z_][\w']*)\b/.exec(lines[i]??'');
  check(decl && /:\s*(?:FStar\.Pervasives\.)?Lemma\b/.test(lines.slice(i,line).join('\n')),'Failed obligation is not in a named Lemma implementation');
  const name=module.slice(0,-4)+'.'+decl[1];
  check(error.split('\n').some(s=>s.startsWith(name+', profiled FStarC.TypeChecker.Tc.process_one_decl:')),'Compiler declaration name does not match failed source range');
  const diagnostic=`F* Error ${m[1]} at ${module}:${line}; failed to prove: ${goal.trim()}${error.includes('The SMT query timed out')?' (SMT query timed out)':''}`;
  const file='fstar/'+module;
  return {file,line,name,source:recoveryLemma(source,file,name,line),diagnostic};
}

/** Persist only a local pointer; publication must still park on the failed rebased baseline. */
export async function rememberRebaseFailure(p:Paths,t:Parent,out:string){
  const root=evidenceRoot(p,t); await mkdir(root,{recursive:true,mode:0o700});check(await realpath(root)===root,'Aliased recovery directory');
  await atomicJson(join(root,'rebase-failure.json'),{...t,out});
}
async function failure(pub:Publisher,out:string,parent:string,upstream:string,identity:string){
  const build=await json(join(out,'build.json')), sourceDir=join(out,'source');
  check(build.sha===parent && build.source_sha===parent && build.tree===await pub.text(['rev-parse',`${parent}^{tree}`]) && build.evaluator===identity && Number.isInteger(build.exit_code) && build.exit_code>0,'Not a failed clean-parent build for this evaluator');
  check(await pub.text(['rev-parse','HEAD','HEAD^{tree}'],sourceDir)===`${parent}\n${build.tree}` && !await pub.text(['status','--porcelain','-uno'],sourceDir),'Failed build source changed');
  const id=await json(join(out,'evaluator.json'));check(digest(JSON.stringify(id))===identity && id.parent===parent && id.upstream===upstream && id.policy==='upstream-pr-v1','Recovery verifier identity changed');
  const log=await bytes(join(out,'build.log'));check(digest(log)===build.build_log_sha256,'Retained failed build log changed');
  const text=log.toString();const file=/^\* Error \d+ at (Z3[A-Za-z0-9_]+\.fst)\(/m.exec(text.replace(/\x1b\[[0-9;]*[A-Za-z]/g,''))?.[1];check(file,'Parent build failed outside a named F* proof');
  const source=await pub.git(['cat-file','blob',`${parent}:fstar/${file}`]);check(source.equals(await bytes(join(sourceDir,'fstar',file))),'Failed source bytes differ from immutable parent');
  const manifest=JSON.parse(await pub.text(['cat-file','blob',`${parent}:fstar/tools/checker_modules.json`]));
  const scope=await json(join(out,'scope-ocaml.json'));validateScope(scope,manifest.modules,manifest.tests,parent,id.fstar);check(scope.selected_modules.includes(file),'Unselected proof module');
  return proofDiagnostic(text,n=>{check(n===file,'Ambiguous failure output');return source.toString();});
}
export async function ensureNoRecovery(p:Paths,t:Parent){
  const root=evidenceRoot(p,t);
  if(await exists(root)){
    check(await realpath(root)===root,'Aliased recovery workspace');
    check(!(await readdir(root)).some(n=>/^[0-9a-f]{64}$/.test(n)),'Pending private proof review; refusing to start another cycle');
  }
}
export async function recoveryInput(p:Paths,pub:Publisher,t:Parent,out:string|undefined,signal?:AbortSignal):Promise<Recovery|null>{
  signal?.throwIfAborted();check(p.repo===pub.repo && p.state===pub.state && p.reviewedUpstream===t.M,'Unbound proof recovery');current(p);
  // Do not run another evaluator fingerprint or select an agent on the ordinary successful path.
  if(out && (await json(join(out,'build.json'))).exit_code===0)return null;
  await ensureNoRecovery(p,t);
  const bind=await pub.binding();check(bind.head===t.H && bind.pr===pub.pr && bind.seed===p.base && await pub.text(['rev-parse',`refs/pulse/parents/${oid(t.H)}/${oid(t.M)}`])===oid(t.P),'Recovery head/parent does not match publisher binding');
  check(await pub.text(['rev-parse','HEAD'])===t.P,'Publisher did not retain the active rebased parent checkout');
  const id=await evaluatorIdentity({...p,worktree:p.repo},signal),base=join(p.state,'baseline',t.P,id),root=evidenceRoot(p,t),dir=join(root,id);
  let candidates:string[];
  if(out)candidates=[out];else if(await exists(join(root,'rebase-failure.json'))){
    const pointer=await json(join(root,'rebase-failure.json'));check(pointer.H===t.H && pointer.M===t.M && pointer.P===t.P,'Stale publication failure pointer');candidates=[pointer.out];
  }else{
    if(!await exists(base) || await exists(join(base,'complete.json'))) return null;
    candidates=(await readdir(base)).filter(n=>/^attempt-[A-Za-z0-9]+$/.test(n)).sort().map(n=>join(base,n));
  }
  let selected:Recovery|undefined;
  for(const path of candidates){
    check(typeof path==='string' && (dirname(path)===base && /^attempt-[A-Za-z0-9]+$/.test(basename(path)) || /^runs\/[1-9]\d*\/publication\/pair-[A-Za-z0-9]+\/before$/.test(path.slice(p.state.length+1)) && path.startsWith(p.state+'/')), 'Failure outside private baseline or rebased paired verification');
    if(!await exists(join(path,'build.json')))continue;
    const candidate=await failure(pub,path,t.P,t.M,id);
    check(!selected || (selected.file===candidate.file && selected.line===candidate.line && selected.diagnostic===candidate.diagnostic),'Conflicting failed baseline attempts; operator reconciliation required');
    selected={pr:pub.pr,...t,evaluator:id,out:path,dir,...candidate};
  }
  if(!selected)return null;
  check(await pub.text(['rev-parse',`${t.M}:${selected.file}`])===await pub.text(['rev-parse',`${t.P}:${selected.file}`]),'Failing proof differs from official trunk');
  // A failure in an unchanged file can be induced by a changed dependency or solver. Reproduce on M if any non-workflow inputs differ.
  if(await pub.text(['diff','--name-only',t.M,t.P,'--','.',':(exclude).junco/Z3-pulse-loop/**'])){
    await mkdir(root,{recursive:true,mode:0o700});check(await realpath(root)===root,'Aliased upstream reproduction directory');
    const attempt=await mkdtemp(join(root,'upstream-')),w=join(attempt,'input'),e=join(attempt,'build');await mkdir(w,{mode:0o700});
    await pub.git(['init','-q','--template='],w);await pub.git(['fetch','--depth=1','--no-tags',pub.repo,t.M],w,undefined,signal);await pub.git(['switch','--detach','FETCH_HEAD'],w);
    const mp={...p,worktree:w},mid=await evaluatorIdentity(mp,signal);check(!await regress(mp,e,signal),'Official trunk builds: the rebased PR failure is not established upstream');
    const official=await failure(pub,e,t.M,t.M,mid);check(official.name===selected.name && official.diagnostic===selected.diagnostic,'Official trunk does not reproduce the same proof failure');
  }
  const now=await pub.observed(signal);
  pub.checkBlock(now.pr,bind.block);
  check(now.H===t.H && now.M===t.M && isDeepStrictEqual(await pub.binding(),bind),'Publication binding changed during failure diagnosis; no recovery turn');
  return selected;
}
export async function beginRecovery(r:Recovery){
  await mkdir(dirname(r.dir),{recursive:true,mode:0o700});check(await realpath(dirname(r.dir))===dirname(r.dir),'Aliased recovery workspace');
  await mkdir(r.dir,{mode:0o700});const {source,...binding}=r;await atomicJson(join(r.dir,'request.json'),{...binding,sourceSha256:digest(source)});
}
