import subprocess
import tempfile
import unittest
from pathlib import Path
import cpu_framework as framework

ROOT=Path(__file__).resolve().parents[1]
HEADER='''From Coq Require Import List ZArith Lia.
Require Import Ex.External.CPUActualCaptureReference.
Import ListNotations ExtendedSV.ExtendedSV CPUActualSourceCapture.CPUActualSourceCapture
 CPUReferenceCuts.CPUReferenceCuts CPUGeneratedJointTemplate.CPUGeneratedJointTemplate
 CPUActualCaptureReference.
Local Open Scope Z_scope.
Definition proc:Process:={|process_kind:=Sequential;
 process_events:=[{|event_edge:=Posedge;event_signal:=0%nat|}];
 process_body:=SAssign true (EVar 32 2%nat)(LVar 32 1%nat);process_source_line:=0|}.
Definition p:Program:={|signal_count:=4;processes:=[proc];statement_fuel:=2;lfp_fuel:=1|}.
Definition ev:Event:={|changed_signal:=0%nat;old_value:=0;new_value:=1|}.
Definition pre:State:=[0;99;8;17].
Definition step(token state:Z):option Z:=Some(state+token).
Lemma retired:EffectChain step 7 [1] 8.
Proof. econstructor;[reflexivity|constructor]. Qed.
Lemma old_field:FieldAtToken step (fun x=>x) 7 [1;2] 1%nat 2
 (norm 32(read_signal(phase_driven_state p ev pre)2%nat)).
Proof. exists 8;split;[|reflexivity]. split;[reflexivity|].
 split;[cbn;lia|exact retired]. Qed.
Lemma actual_projection:
 norm 32(read_signal(PhaseSemantics p ev pre)1%nat)=
 (if process_matches_states pre(phase_driven_state p ev pre)proc
 then norm 32(eval_expr(phase_driven_state p ev pre)(EVar 32 2%nat))
 else norm 32(read_signal pre 1%nat)).
Proof. vm_compute;reflexivity. Qed.
Lemma selected:capture_source p proc 1%nat(EVar 32 2%nat)ev pre=Some 2%nat.
Proof. vm_compute;reflexivity. Qed.
Lemma moved:FieldAtToken step (fun x=>x) 8 [2;4] 0%nat 2
 (norm 32(read_signal(PhaseSemantics p ev pre)1%nat)).
Proof. exact(captured_token_transfer step (fun x=>x) p proc 1%nat(EVar 32 2%nat)
 ev pre 2%nat 7 8 [1] [2] [4] 0%nat 2 actual_projection selected retired old_field). Qed.
'''

class ActualCaptureReferenceTests(unittest.TestCase):
    def check(self,body,ok):
        with tempfile.TemporaryDirectory()as folder:
            path=Path(folder)/'CaptureReference.v';path.write_text(HEADER+body)
            result=subprocess.run([str(ROOT/'_opam/bin/coqc'),*framework.FLAGS,str(path)],
                cwd=ROOT,capture_output=True,text=True,timeout=120)
            self.assertEqual(result.returncode==0,ok,result.stdout+result.stderr)
            if not ok:self.assertIn('expected to have type',result.stderr)

    def test_copy_retire_and_append(self):
        self.check('Check moved.\n',True)

    def test_wrong_source_value_rejected(self):
        self.check('''Example wrong:FieldAtToken step (fun x=>x) 8 [2;4] 0%nat 2 17.
Proof. exact moved. Qed.
''',False)

    def test_wrong_instruction_identity_rejected(self):
        self.check('''Example wrong:FieldAtToken step (fun x=>x) 8 [2;4] 0%nat 4
 (norm 32(read_signal(PhaseSemantics p ev pre)1%nat)).
Proof. exact moved. Qed.
''',False)

if __name__=='__main__':unittest.main()
