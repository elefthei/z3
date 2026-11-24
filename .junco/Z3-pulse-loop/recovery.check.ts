import assert from 'node:assert/strict';
import { proofDiagnostic } from './recovery.ts';

export function checkRecoveryDiagnostic(){
  const source='module Z3Fixture\nlet untouched = 1\nlet step (x:nat) : Lemma (x >= 0) =\n  let next = x - 1 in\n  assert (next >= 0)\nlet other = true\n';
  const log='* Error 19 at Z3Fixture.fst(5,10-5,14):\n  - Subtyping check failed\n  - Failed to prove: next >= 0\nZ3Fixture.step, profiled FStarC.TypeChecker.Tc.process_one_decl:\t55 ms\n| F* verification failed: Z3Fixture.fst\n';
  const read=(name:string)=>{assert.equal(name,'Z3Fixture.fst');return source;};const d=proofDiagnostic(log,read);
  assert.equal(d.name,'Z3Fixture.step');assert.equal(d.file,'fstar/Z3Fixture.fst');assert.equal(d.line,5);assert.match(d.source,/^let step/);assert.ok(!d.source.includes('let other'));assert.match(d.diagnostic,/next >= 0/);
  for(const invalid of ['CMake: failed to configure',log.replace('Failed to prove:','Command failed:'),log.replace('Z3Fixture.step,','Z3Fixture.other,'),log.replace('(5,10-5,14)','(2,1-2,5)'),log+log]) assert.throws(()=>proofDiagnostic(invalid,read));
}
