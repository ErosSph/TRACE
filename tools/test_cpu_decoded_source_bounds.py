import subprocess
import tempfile
import unittest
from pathlib import Path
import cpu_framework as framework
ROOT=Path(__file__).resolve().parents[1]
HEADER='''From Coq Require Import List ZArith.
Require Import Ex.External.CPUDecodedSourceBounds.
Import ListNotations CPUDecodedSourceBounds CV32E40PReq41Instruction.CV32E40PReq41Instruction.
Local Open Scope Z_scope.
Lemma actual_decode:Decode.decode Decode.RV32I 33521843=Decode.IInstruction(Decode.Add 1 31 31).
Proof. vm_compute;reflexivity. Qed.
Lemma actual_bounds:Forall(fun r=>0<=r<32)(source_registers(Decode.Add 1 31 31)).
Proof. exact(decoded_source_bounds 33521843(Decode.Add 1 31 31)actual_decode). Qed.
'''
class DecodedBoundsTests(unittest.TestCase):
    def check(self,body,ok):
        with tempfile.TemporaryDirectory()as folder:
            path=Path(folder)/'BoundsCheck.v';path.write_text(HEADER+body)
            r=subprocess.run([str(ROOT/'_opam/bin/coqc'),*framework.FLAGS,str(path)],
                cwd=ROOT,capture_output=True,text=True,timeout=120)
            self.assertEqual(r.returncode==0,ok,r.stdout+r.stderr)
            if not ok:self.assertIn('expected to have type',r.stderr)
    def test_real_decode_highest_source_register(self):self.check('Check actual_bounds.\n',True)
    def test_stronger_false_bound_rejected(self):
        self.check('''Goal Forall(fun r=>0<=r<31)(source_registers(Decode.Add 1 31 31)).
Proof. exact actual_bounds. Qed.
''',False)
if __name__=='__main__':unittest.main()
