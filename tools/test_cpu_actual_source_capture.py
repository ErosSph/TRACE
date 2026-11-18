"""Native phase-source checks: self hold, trigger, branch, unknown expression."""
import subprocess
import tempfile
import unittest
from pathlib import Path
import cpu_framework as framework

ROOT=Path(__file__).resolve().parents[1]
HEADER='''From Coq Require Import ZArith.
Require Import Ex.External.CPUActualSourceCapture.
Import ExtendedSV.ExtendedSV CPUActualSourceCapture
 ExtendedSVInstructionOrigin.ExtendedSVInstructionOrigin.
'''

class ActualSourceCaptureTests(unittest.TestCase):
    def compile(self,body,ok=True):
        with tempfile.TemporaryDirectory()as folder:
            path=Path(folder)/'CaptureTest.v';path.write_text(HEADER+body)
            p=subprocess.run([str(ROOT/'_opam/bin/coqc'),*framework.FLAGS,str(path)],
                cwd=ROOT,capture_output=True,text=True,timeout=120)
            self.assertEqual(p.returncode==0,ok,p.stdout+p.stderr)
            self.assertEqual(path.with_suffix('.vo').exists(),ok)

    def test_self_copy_is_hold_not_new_capture(self):
        self.compile('''Example self_hold p proc ev pre root:
 capture_source p proc root(EVar 32 root)ev pre=None.
Proof. unfold capture_source;destruct(process_matches_states pre(phase_driven_state p ev pre)proc);
 cbn[copy_source];now rewrite ?PeanoNat.Nat.eqb_refl. Qed.
''')

    def test_actual_trigger_and_selected_branch(self):
        self.compile('''Example copy_branch p proc ev pre:
 process_matches_states pre(phase_driven_state p ev pre)proc=true ->
 capture_source p proc 9(ECond 32(EConst 1 0)(EVar 32 5)(EVar 32 6))ev pre=Some 6.
Proof. intro H;unfold capture_source;rewrite H;reflexivity. Qed.
Example no_trigger p proc ev pre:
 process_matches_states pre(phase_driven_state p ev pre)proc=false ->
 capture_source p proc 9(EVar 32 6)ev pre=None.
Proof. intro H;unfold capture_source;now rewrite H. Qed.
''')

    def test_computed_expression_is_not_guessed_as_copy(self):
        self.compile('''Example unknown p proc ev pre:
 capture_source p proc 9(EBinary 32 BAdd(EVar 32 6)(EConst 32 1))ev pre=None.
Proof. unfold capture_source;destruct(process_matches_states pre(phase_driven_state p ev pre)proc);reflexivity. Qed.
''')
        self.compile('''Example wrong_branch p proc ev pre:
 process_matches_states pre(phase_driven_state p ev pre)proc=true ->
 capture_source p proc 9(ECond 32(EConst 1 0)(EVar 32 5)(EVar 32 6))ev pre=Some 5.
Proof. intro H;unfold capture_source;rewrite H;reflexivity. Qed.
''',False)

if __name__=='__main__':unittest.main()
