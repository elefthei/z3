import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { beginRecovery, ensureNoRecovery, type Recovery } from './recovery.ts';
import { parserRange, recoveryLemma, repairProof, verifyRecovery } from './recovery-verify.ts';
import { digest } from './publication.ts';
import { paths } from './state.ts';

export async function checkRecoveryProof() {
  const file='fstar/Z3Repair.fst',name='Z3Repair.step',old='let next = fuel - 1 in';
  const source=`module Z3Repair
(* let step (fuel:nat) : Lemma True = () *)
let untouched (fuel:nat) =
  ${old}
  next
let rec step (fuel:nat)
  : Lemma (requires (fuel >= 0))
          (ensures (fuel == fuel)) (decreases fuel) =
  if fuel = 0 then () else
    ${old}
    sibling next
and sibling (fuel:nat) : Lemma (fuel >= 0) (decreases fuel) =
  if fuel = 0 then () else
    ${old}
    step next
let following = false
`;
  const r={file,name,line:11,source:recoveryLemma(source,file,name,11)}, second={file,name:'Z3Repair.sibling',line:15,source:recoveryLemma(source,file,'Z3Repair.sibling',15)};
  const answer=(old:string,replacement:string)=>JSON.stringify({old,replacement}), annotate=answer(old,'let next : nat = fuel - 1 in');
  const edited=repairProof(source,r,annotate);
  assert.equal(edited,source.replace(r.source,r.source.replace(old,'let next : nat = fuel - 1 in')));
  assert.equal(repairProof(source,second,annotate),source.replace(second.source,second.source.replace(old,'let next : nat = fuel - 1 in')));
  for(const assertion of ['assert (next >= 0);\n    ','assert (fuel - 1 >= 0); ']) {
    assert.equal(repairProof(source,r,answer('sibling next',assertion+'sibling next')),source.replace('    sibling next','    '+assertion+'sibling next'));
  }
  for(const bad of [
    answer(old,'let next = 0 in'), answer('requires (fuel >= 0)','requires True'), answer('ensures (fuel == fuel)','ensures True'),
    answer('decreases fuel','decreases 0'), answer('let following = false','let following = true'), answer('and sibling','and changed'),
    answer('sibling next','admit ()'), answer('sibling next','assume (next >= 0); sibling next'),answer('sibling next','assert (_ >= 0); sibling next'),
    answer('sibling next','assert (FStar.Unsafe.magic () >= 0); sibling next'), answer('sibling next','assert (next >= 0) by (admit ()); sibling next'),
    answer(old,'let next : nat = fuel - 1 in\n#set-options "--lax"'), answer(old,'let next : nat = fuel - 1 in\nlet bogus = ()'),
    answer(old,'let next : nat = fuel - 1 in (*'), answer('sibling next','*)\nand bogus = (); sibling next'),
    answer(old,'let next : nat = fuel - 1 in; pwsh -File evil.ps1'),answer(old,'/bin/sh'),answer('sibling next','assert (false); sibling next'),
    answer('next : nat','next : int'),answer('next','next : nat'), answer(old,old),
    answer('ext = fuel','ext : nat = fuel'),answer('let next = fue','let next : nat = fue'),
    '{"old":"no","old":"let next = fuel - 1 in","replacement":"let next : nat = fuel - 1 in"}',
    JSON.stringify({old,replacement:'let next : nat = fuel - 1 in',path:'fstar/Z3Other.fst'}),'```json\n'+annotate+'\n```',
  ]) assert.throws(()=>repairProof(source,r,bad));
  assert.throws(()=>repairProof(source,{...r,source:r.source+'\n'},annotate));
  for(const [src,n,line] of [
    [source,name,8],[source,name,15],[source,'Z3Repair.untouched',4],[source,'Z3Repair.bogus',2],
    [source.replace('let rec step','(*\nlet rec step').replace('and sibling','*)\nand sibling'),name,12],
    [source.replace('sibling next','"(*"; sibling next'),name,11], [source.replace('sibling next','let rec nested x = x\nand nested2 x = x in sibling next'),name,11],
    [source.replace('let rec step','let rec step2 (fuel:nat) : Lemma True = ()\nand step').replace('and sibling','and step'),name,12],
  ] as const) assert.throws(()=>recoveryLemma(src,file,n,line));
  assert.throws(()=>recoveryLemma(source,'fstar/../fstar/Z3Repair.fst',name,11));

  // Use real immutable Git objects; a malformed proposal must never reach an evaluator or touch its parent.
  const dir=await mkdtemp(join(tmpdir(),'pulse-recovery-proof-'));
  try {
    const repo=join(dir,'publisher'),state=join(dir,'private'),failed=join(dir,'failed');await mkdir(join(repo,'fstar'),{recursive:true});
    await mkdir(failed);await writeFile(join(failed,'build.log'),'preserved');await writeFile(join(repo,file),source);
    if(process.env.FSTAR_EXE) {
      const cfg={worktree:repo,fstarExe:process.env.FSTAR_EXE};
      await parserRange(cfg,file,source,[6,0],[15,'    step next'.length]);
      await assert.rejects(parserRange(cfg,file,source,[6,0],[16,'let following = false'.length]),/parser did not confirm/);
    }
    const git=(...args:string[])=>execFileSync('/usr/bin/git',['-c','core.hooksPath=/dev/null','-c','user.name=Proof fixture','-c','user.email=fixture@localhost',...args],{cwd:repo,env:{PATH:'/usr/bin:/bin',GIT_CONFIG_NOSYSTEM:'1',GIT_CONFIG_GLOBAL:'/dev/null'},encoding:'utf8'}).trim();
    git('init','-q','--template=');git('add','--',file);git('commit','-qm','Proof fixture');const P=git('rev-parse','HEAD'), evaluator='a'.repeat(64);
    git('update-ref',`refs/pulse/parents/${P}/${P}`,P);
    const p={...paths(),repo,state,reviewedUpstream:P};
    const request:Recovery={...r,pr:1,H:P,M:P,P,evaluator,out:failed,dir:join(state,'proof-recovery',P,P,P,evaluator),diagnostic:'Failed to prove: next >= 0'};
    await beginRecovery(request);
    await assert.rejects(ensureNoRecovery(p,request),/Pending private proof review/);
    await assert.rejects(verifyRecovery(p,{...request,source:'different'},annotate),/reservation/);
    await assert.rejects(verifyRecovery(p,{...request,dir:failed},annotate),/Unbound/);
    const result=await verifyRecovery(p,request,answer(old,'assume False'));
    assert.equal(result.status,'rejected');assert.equal(result.tested,0);assert.equal(result.ciPass,false);assert.equal(result.patch,'');
    const stored=JSON.parse(await readFile(join(request.dir,'result.json'),'utf8'));
    assert.equal(stored.originalSha256,digest(source));assert.equal(stored.sourceSha256,digest(r.source));assert.match(stored.detail,/ascription/);
    await assert.rejects(verifyRecovery(p,request,annotate),/EEXIST/);
    assert.equal(git('status','--porcelain'),'');assert.equal(git('rev-parse','HEAD'),P);assert.equal(await readFile(join(failed,'build.log'),'utf8'),'preserved');
  } finally {await rm(dir,{recursive:true,force:true});}
}
