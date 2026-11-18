import subprocess
import tempfile
import unittest
from pathlib import Path
import cpu_framework as framework

ROOT=Path(__file__).resolve().parents[1]
HEADER='''From Coq Require Import List ZArith.
Require Import Ex.External.CPUSelfHoldReference.
Import ListNotations ExtendedSV.ExtendedSV CPUSelfHoldReference.
Local Open Scope Z_scope.
Definition expression:=ECond 32(EVar 1 3%nat)(EVar 32 1%nat)(EVar 32 2%nat).
Definition proc:Process:={|process_kind:=Sequential;
 process_events:=[{|event_edge:=Posedge;event_signal:=0%nat|}];
 process_body:=SAssign true expression(LVar 32 1%nat);process_source_line:=0|}.
Definition p:Program:={|signal_count:=4;processes:=[proc];statement_fuel:=2;lfp_fuel:=1|}.
Definition ev:Event:={|changed_signal:=0%nat;old_value:=0;new_value:=1|}.
Lemma held:norm 32(read_signal(PhaseSemantics p ev [0;8;17;1])1%nat)=8.
Proof.
 change(norm 32(read_signal(PhaseSemantics p ev [0;8;17;1])1%nat)=norm 32(read_signal [0;8;17;1]1%nat)).
 apply(self_hold_value p proc 1%nat expression ev [0;8;17;1]);
 vm_compute;congruence.
Qed.
'''

class SelfHoldTests(unittest.TestCase):
    def check(self,body,ok):
        with tempfile.TemporaryDirectory()as folder:
            path=Path(folder)/'HoldCheck.v';path.write_text(HEADER+body)
            result=subprocess.run([str(ROOT/'_opam/bin/coqc'),*framework.FLAGS,str(path)],
                cwd=ROOT,capture_output=True,text=True,timeout=120)
            self.assertEqual(result.returncode==0,ok,result.stdout+result.stderr)
            if not ok:self.assertIn('expected to have type',result.stderr)

    def test_triggered_self_hold(self):self.check('Check held.\n',True)

    def test_selected_other_branch_not_hold(self):
        self.check('''Goal norm 32(read_signal(PhaseSemantics p ev [0;8;17;0])1%nat)=8.
Proof. exact held. Qed.
''',False)

if __name__=='__main__':unittest.main()
