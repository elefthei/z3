import { execFile } from 'node:child_process';
import { createHash } from 'node:crypto';
import { lstat, mkdir, readFile, realpath, writeFile } from 'node:fs/promises';
import { basename, dirname, join } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { analyze, evaluatorIdentity, must, prCandidateFailure, regress, validatePatch } from './evaluation.ts';
import { check, digest, oid } from './publication.ts';
import type { Recovery } from './recovery.ts';
import type { Paths } from './state.ts';

export type RecoveryResult = { status:'verified'|'rejected'; patch:string; tree:string; out:string; reason:string; tested:number; ciPass:boolean };
const id = '[a-z][A-Za-z0-9_]*';
const binding = /^(let(?: rec)?|and) ([a-z][A-Za-z0-9_]*)(?=[ (:])/;

// A deliberately small source dialect. Never interpret a header inside a comment, string or quoted term.
function codeLines(source:string) {
  check(!/[^\x20-\x7e\n]/.test(source), 'Unsupported proof source encoding');
  let depth=0, start=0;
  const masked = source.replace(/\(\*|\*\)|\/\/[^\n]*|["'`]|[^\n(*"'`/]+|[()*/]/g, (token:string, at:number) => {
    if(token==='(*') { if(depth++===0)start=at; }
    else if(token==='*)') { check(depth>0,'Unbalanced proof comment'); depth--; return '  '; }
    else if(depth && (token.startsWith('//') || token.includes('*)') || token.includes('(*'))) throw new Error('Ambiguous nested proof comment');
    else if(!depth && !token.startsWith('//')) { check(!/["'`]/.test(token),'Unsupported quoted proof syntax'); return token; }
    return ' '.repeat(token.length);
  });
  check(!depth,`Unclosed proof comment at ${start}`);
  check(!/^\s*#(?:line|lang)\b/m.test(masked),'Remapped or extended proof source');
  return masked.split('\n');
}

function locate(source:string,file:string,name:string,line:number) {
  const mod=/^fstar\/(Z3[A-Za-z0-9_]+)\.fst$/.exec(file)?.[1];
  const raw=source.split('\n'), code=codeLines(source);
  check(mod && code[0]?.trimEnd()===`module ${mod}` && Number.isSafeInteger(line) && line>=1 && line<=raw.length,'Invalid proof module or diagnostic range');
  const headers=code.flatMap((s,i)=>s.trim() && s[0]!==' ' ? [i] : []);
  const targets=headers.filter(i=>{const m=binding.exec(code[i]!);return m && name===`${mod}.${m[2]}`;});
  check(targets.length===1,'No unique named implementation');
  const i=targets[0]!, n=headers.indexOf(i), end=headers[n+1]??raw.length;
  let a=n,b=n+1;
  while(a>0 && /^and\b/.test(code[headers[a]!]!))a--;
  while(b<headers.length && /^and\b/.test(code[headers[b]!]!))b++;
  const first=headers[a]!, stop=headers[b]??raw.length;
  check((a===n && b===n+1 ? /^let / : /^let rec /).test(code[first]!), 'Ambiguous recursive proof group');
  for(let k=a;k<b;k++) {
    const x=headers[k]!, y=headers[k+1]??raw.length, member=raw.slice(x,y).join('\n').trimEnd();
    check(member===code.slice(x,y).join('\n').trimEnd() && !/["'`@]|\(\*|\*\)|\/\/|^\s*#\w|\[\s*%/m.test(member),'Ambiguous proof syntax');
    // An `and` in a nested let-rec cannot be treated as the next top-level proof.
    const tail=member.slice(binding.exec(member)?.[0].length ?? 0);
    let lets=0; for(const [w] of tail.matchAll(/\b(let|in|and)\b/g)) {
      check(w!=='and' && (w==='let' ? ++lets : --lets)>=0,'Ambiguous proof binding boundary');
    }
    check(lets===0,'Unclosed local proof binding');
  }
  const text=raw.slice(i,end).join('\n').trimEnd();
  check(text.length<=16_384, 'Proof declaration too large');
  // Only explicit parenthesized binders, a literal Lemma effect and parenthesized clauses.
  let pos=binding.exec(text)![0].length;
  const spaces=()=>{while(pos<text.length && /\s/.test(text[pos]!))pos++;};
  const groups=()=>{spaces();while(text[pos]==='('){let depth=0; do {check(pos<text.length,'Unclosed proof signature');const c=text[pos++]!; if(c==='(')depth++;else if(c===')')depth--;}while(depth);spaces();}};
  groups(); const effect=/^:\s*(?:FStar\.Pervasives\.)?Lemma\b/.exec(text.slice(pos));
  check(effect,'Not an explicit implemented Lemma');pos+=effect[0].length;groups();
  check(text[pos]==='=' && text[pos+1]!=='=' && text.slice(pos+1).trim(), 'Missing unambiguous proof body');
  const body=++pos, beforeLine=text.slice(0,body).split('\n').length+i;
  check(line>=beforeLine && line<=i+text.split('\n').length && code[line-1]!.trim() && (line!==beforeLine || text.slice(body).split('\n',1)[0]!.trim()),'Diagnostic is outside the implementation body');
  const start=i ? raw.slice(0,i).join('\n').length+1 : 0;
  const group=raw.slice(first,stop).join('\n').trimEnd().split('\n');
  return {text,body,start,groupBegin:[first+1,0],groupEnd:[first+group.length,group.at(-1)!.length]};
}

export function recoveryLemma(source:string,file:string,name:string,line:number):string { return locate(source,file,name,line).text; }

function parseAnswer(answer:string):{old:string;replacement:string} {
  check(answer.length<=32_768,'Proof proposal too large');
  const v=JSON.parse(answer);
  // JSON.parse alone silently accepts duplicate keys. Exactly two string keys and two string values are allowed.
  check(v && Object.keys(v).length===2 && typeof v.old==='string' && typeof v.replacement==='string' &&
    [...answer.matchAll(/"(?:\\.|[^"\\])*"/gs)].length===4 && v.old.trim() && v.replacement.trim() && v.old!==v.replacement,'Expected one exact old/replacement string pair');
  return v;
}
const atom=`(?:${id}|-?[0-9]+)`, term=`${atom}(?: +[+-] +${atom})?`;
const assertion=new RegExp(`^assert +\\( *(${term} *(?:>=|<=|==|<>|>|<) *${term}) *\\);`);

/** Pure proposal check. The model supplies no path, executable, patch headers or declarations. */
export function repairProof(source:string,r:Pick<Recovery,'file'|'name'|'line'|'source'>,answer:string) {
  const decl=locate(source,r.file,r.name,r.line);check(decl.text===r.source,'Failed proof source changed');
  const {old,replacement}=parseAnswer(answer), body=decl.text.slice(decl.body), at=body.indexOf(old);
  check(at>=0 && at===body.lastIndexOf(old),'Proof edit is absent or ambiguous within this body');
  const splitsToken=(pos:number)=>pos>0 && pos<body.length && /^(?:[\w']{2}|[!#$%&*+./:<=>?@^|~-]{2})$/.test(body.slice(pos-1,pos+1));
  check(!splitsToken(at) && !splitsToken(at+old.length),'Proof fragment splits a source token');
  const revised=body.slice(0,at)+replacement+body.slice(at+old.length), lines=body.split('\n'), after=revised.split('\n');
  let i=0;while(i<lines.length && lines[i]===after[i])i++;
  const prior=lines[i], next=after[i];check(prior && next,'Proof edit has no statement anchor');
  const indent=/^ +/.exec(prior)?.[0];check(indent,'Proof statement must be indented');
  const annotated=new RegExp(`^( +let +${id}) *: *(?:nat|pos|int|bool)( +=[^=].*)$`).exec(next);
  let extra=0;
  if(!(annotated && prior===annotated[1]+annotated[2])) {
    const parsed=next.startsWith(indent) && assertion.exec(next.slice(indent.length));
    check(parsed,'Only a local scalar ascription or checked arithmetic assertion is allowed');
    const afterAssert=next.slice(indent.length+parsed[0].length);
    if(!afterAssert) {check(after[i+1]===prior,'Assertion must preserve the following statement');extra=1;}
    else check(/^ +/.test(afterAssert) && afterAssert.trimStart()===prior.trimStart(),'Assertion must precede the unchanged statement');
    const names=new Set([...decl.text.matchAll(/(?:\blet +|\(#?)([a-z][A-Za-z0-9_]*)(?= *[:=])/g)].map(m=>m[1]));
    for(const [word] of parsed[1]!.matchAll(/[A-Za-z_][A-Za-z0-9_]*/g))check(names.has(word) && !/^(?:admit|assume|magic|unsafe|unchecked|sorry)/i.test(word),'Assertion operand is not a recognized local binder');
  }
  check(after.length===lines.length+extra && lines.slice(i+1).every((s,j)=>s===after[i+1+extra+j]),'More than one proof edit');
  const begin=decl.start+decl.body+at;
  return source.slice(0,begin)+replacement+source.slice(begin+old.length);
}

// The pinned compiler, not indentation, makes the final top-level/mutual-group boundary decision.
export async function parserRange(p:Pick<Paths,'fstarExe'|'worktree'>,file:string,source:string,begin:number[],end:number[],signal?:AbortSignal) {
  const packet=(qid:string,query:string,args:object)=>JSON.stringify({'query-id':qid,query,args})+'\n';
  const {promise,resolve,reject}=Promise.withResolvers<string>();
  const child=execFile(p.fstarExe,['--ide',basename(file)],{cwd:dirname(join(p.worktree,file)),signal,timeout:60_000,maxBuffer:4*1024*1024,env:{PATH:'/usr/bin:/bin',HOME:p.worktree,LC_ALL:'C'}},(error,out)=>error?reject(error):resolve(out));
  child.stdin!.on('error',()=>{});child.stdin!.end(packet('ranges','segment',{code:source})+packet('done','exit',{}));
  const replies=(await promise).trim().split('\n').map(s=>JSON.parse(s)).filter(v=>v.kind==='response' && v['query-id']==='ranges');
  check(replies.length===1 && replies[0].status==='success' && Array.isArray(replies[0].response.decls) && replies[0].response.decls.filter(({def_range:r}:{def_range:{beg:number[];end:number[]}})=>isDeepStrictEqual(r.beg,begin) && isDeepStrictEqual(r.end,end)).length===1,'F* parser did not confirm the proof declaration range');
}

export async function verifyRecovery(p:Paths,r:Recovery,answer:string,signal?:AbortSignal):Promise<RecoveryResult> {
  const {source,...binding}=r, marker=join(r.dir,'request.json');
  check(p.reviewedUpstream===oid(r.M) && /^[0-9a-f]{64}$/.test(r.evaluator) && r.dir===join(p.state,'proof-recovery',oid(r.H),r.M,oid(r.P),r.evaluator) && /^fstar\/Z3[A-Za-z0-9_]+\.fst$/.test(r.file),'Unbound private proof verifier');
  const stat=await lstat(r.dir), ms=await lstat(marker);
  check(stat.isDirectory() && stat.uid===process.getuid!() && (stat.mode&0o777)===0o700 && await realpath(r.dir)===r.dir && ms.isFile() && ms.nlink===1 && (ms.mode&0o077)===0 && ms.uid===stat.uid && isDeepStrictEqual(JSON.parse(await readFile(marker,'utf8')),{...binding,sourceSha256:digest(source)}),'Missing proof recovery reservation');
  const w=join(r.dir,'candidate'), out=join(r.dir,'after'), patch=join(r.dir,'attempt.patch');
  await mkdir(w,{mode:0o700}); // Exclusive: never replace evidence, even after interruption.
  const git=(cwd:string,...args:string[])=>must(['/usr/bin/git','--no-optional-locks','-c','core.hooksPath=/dev/null','-c','core.fsmonitor=false','-c','gc.auto=0','-c','protocol.allow=never','-c','protocol.file.allow=always','-c','credential.helper=',...args],{cwd,signal});
  const q={...p,worktree:w,state:r.dir};
  const result:RecoveryResult={status:'rejected',patch:'',tree:'',out,reason:'',tested:0,ciPass:false};
  let phase='checking bound source', originalSha256='', candidateSha256='', patchSha256='', evidenceSha256='', detail='', counts:Record<string,number>={};
  try {
    check((await git(p.repo,'rev-parse',`refs/pulse/parents/${r.H}/${r.M}`)).trim()===r.P,'Retained proof parent changed');
    const entry=await git(p.repo,'ls-tree',r.P,'--',r.file);check(entry===await git(p.repo,'ls-tree',r.M,'--',r.file) && /^100644 blob [0-9a-f]{40}\t/.test(entry),'Failing file not inherited unchanged');
    await git(w,'init','--template=','-q'); await git(w,'fetch','--depth=1','--no-tags','--no-recurse-submodules','--',p.repo,r.P);await git(w,'switch','--no-overwrite-ignore','--detach',r.P);
    const path=join(w,r.file), bytes=await readFile(path), full=bytes.toString('utf8');originalSha256=digest(bytes);
    const blob=createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex');
    check(entry===`100644 blob ${blob}\t${r.file}\n` && await realpath(path)===path && bytes.equals(Buffer.from(full)),'Failing proof bytes do not match the immutable blob');
    phase='validating the proof proposal'; const edited=repairProof(full,r,answer), decl=locate(full,r.file,r.name,r.line);
    check(await evaluatorIdentity(q,signal)===r.evaluator,'Proof verifier identity changed');
    await parserRange(q,r.file,full,decl.groupBegin,decl.groupEnd,signal);
    await writeFile(path,edited);candidateSha256=digest(edited);await git(w,'add','--',r.file);
    result.tree=oid((await git(w,'write-tree')).trim());
    check(await git(w,'diff','--cached','--name-only','-z',r.P,'--')===r.file+'\0' && (await git(w,'cat-file','blob',`:${r.file}`))===edited,'Staged proof does not equal the host edit');
    const diff=await git(w,'diff','--cached','--binary','--full-index','--no-ext-diff','--no-textconv',r.P,'--');
    await writeFile(patch,diff,{flag:'wx',mode:0o600});result.patch=patch;patchSha256=digest(diff);
    phase='validating protected candidate';await validatePatch(q,r.P,w);
    phase='running strict candidate evaluation';const built=await regress(q,out,signal);
    phase='checking retained candidate evidence';const after=await analyze(q,out,r.P,signal);
    check(after.buildOk===built && after.sha===r.P && after.tree===result.tree && after.evaluator===r.evaluator,'Recovery analysis does not identify the tested tree');
    result.tested=after.tested;counts=after.counts;evidenceSha256=after.evidenceSha256??'';
    const failure=prCandidateFailure(after);
    if(failure || after.tested!==242)result.reason=failure??'Expected 242 independently attempted cases';
    else {check(/^[0-9a-f]{64}$/.test(evidenceSha256),'Missing native case evidence');result.status='verified';result.ciPass=true;result.reason='Private proof repair passed strict verification and all 242 cases';}
  } catch(error) {detail=error instanceof Error?error.message:String(error);result.reason=`Private proof repair rejected while ${phase}`;}
  await writeFile(join(r.dir,'result.json'),JSON.stringify({...result,pr:r.pr,H:r.H,M:r.M,P:r.P,evaluator:r.evaluator,failedOut:r.out,file:r.file,line:r.line,name:r.name,sourceSha256:digest(source),originalSha256,candidateSha256,patchSha256,evidenceSha256,counts,detail},null,2)+'\n',{flag:'wx',mode:0o600});
  signal?.throwIfAborted();return result;
}
