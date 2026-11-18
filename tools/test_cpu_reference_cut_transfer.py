import subprocess
import tempfile
import unittest
from pathlib import Path
import cpu_framework as framework

ROOT=Path(__file__).resolve().parents[1]
HEADER='''From Coq Require Import List Arith Lia.
Require Import Ex.External.CPUReferenceCutTransfer.
Import ListNotations CPUReferenceCuts.CPUReferenceCuts
 CPUGeneratedJointTemplate.CPUGeneratedJointTemplate CPUReferenceCutTransfer.
Definition step(token state:nat):option nat:=Some(state+token).
Lemma retired:EffectChain step 0 [1] 1.
Proof. econstructor;[reflexivity|constructor]. Qed.
Lemma old_cut:BeforeToken step 0 [1;2;3] 2 3 3.
Proof. split;[reflexivity|];split;[cbn;lia|].
 change(EffectChain step 0 [1;2] 3).
 eapply chain_cons with(b:=1);[reflexivity|].
 eapply chain_cons with(b:=3);[reflexivity|constructor]. Qed.
'''

class CutTransferTests(unittest.TestCase):
    def check(self,body,ok):
        with tempfile.TemporaryDirectory()as folder:
            path=Path(folder)/'CutCheck.v';path.write_text(HEADER+body)
            p=subprocess.run([str(ROOT/'_opam/bin/coqc'),*framework.FLAGS,str(path)],
                cwd=ROOT,capture_output=True,text=True,timeout=120)
            self.assertEqual(p.returncode==0,ok,p.stdout+p.stderr)
            self.assertEqual(path.with_suffix('.vo').exists(),ok)
            if not ok:self.assertIn('expected to have type',p.stderr)

    def test_retire_append_preserves_reference_state(self):
        self.check('''Example restored:BeforeToken step 1 [2;3;4] 1 3 3.
Proof. exact(before_cycle step 0 1 [1] [2;3] [4] 1 3 3 retired old_cut). Qed.
''',True)

    def test_queue_reorder_rejected(self):
        self.check('''Example reordered:BeforeToken step 1 [3;2;4] 1 3 3.
Proof. exact(before_cycle step 0 1 [1] [2;3] [4] 1 3 3 retired old_cut). Qed.
''',False)

    def test_wrong_retired_state_rejected(self):
        self.check('''Example wrong_state:BeforeToken step 0 [2;3;4] 1 3 3.
Proof. exact(before_cycle step 0 1 [1] [2;3] [4] 1 3 3 retired old_cut). Qed.
''',False)

if __name__=='__main__':unittest.main()
