import subprocess
import tempfile
import unittest
from pathlib import Path
import cpu_framework as framework

ROOT=Path(__file__).resolve().parents[1]
HEADER='''From Coq Require Import ZArith List.
Require Import Lang.ExtendedSV Ex.External.CPUIndexedSource.
Import ExtendedSV ListNotations.
Local Open Scope Z_scope.
'''

class IndexedSourceTests(unittest.TestCase):
    def check(self,body,success):
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)/'IndexedCheck.v';path.write_text(HEADER+body)
            p=subprocess.run([str(ROOT/'_opam/bin/coqc'),*framework.FLAGS,str(path)],
                cwd=ROOT,capture_output=True,text=True,timeout=120)
            self.assertEqual(p.returncode==0,success,p.stdout+p.stderr)
            if not success:
                self.assertIn('Error:',p.stderr)
                self.assertNotIn('was not found',p.stderr)
                self.assertNotIn('Syntax error',p.stderr)

    def test_add_first_source_is_its_actual_isa_register(self):
        self.check('''Goal forall s,
 IndexedSourceAddress 5%nat 45%nat s (Decode.Add 1 2 3) 0%nat ->
 norm 5(read_signal s 45%nat)=2.
Proof. intros s H; exact H. Qed.
Goal forall s, IndexedSourceAddress 5%nat 45%nat s (Decode.Add 1 2 3) 0%nat ->
 In (norm 5(read_signal s 45%nat)) [2;3].
Proof. intros s H;exact(indexed_source_address_member 5%nat 45%nat s
 (Decode.Add 1 2 3) 0%nat ltac:(discriminate) H). Qed.
''',True)

    def test_swapped_operand_rejected(self):
        self.check('''Goal forall s,
 IndexedSourceAddress 5%nat 45%nat s (Decode.Add 1 2 3) 0%nat ->
 norm 5(read_signal s 45%nat)=3.
Proof. intros s H;exact H. Qed.
''',False)

    def test_absent_operand_cannot_supply_a_source(self):
        self.check('''Goal forall s,
 IndexedSourceAddress 5%nat 45%nat s (Decode.Lui 1 0) 0%nat.
Proof. intro s;exact I. Qed.
''',True)
        self.check('''Goal forall s,
 IndexedSourceAddress 5%nat 45%nat s (Decode.Lui 1 0) 0%nat ->
 In (norm 5(read_signal s 45%nat)) [].
Proof. intros s H;exact(indexed_source_address_member 5%nat 45%nat s
 (Decode.Lui 1 0) 0%nat ltac:(discriminate) H). Qed.
''',False)

if __name__=='__main__':unittest.main()
