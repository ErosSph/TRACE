"""Native checks of the original-ISA/ready-slot bridge, including rejection."""
import subprocess
import tempfile
import unittest
from pathlib import Path
import cpu_framework as framework

ROOT = Path(__file__).resolve().parents[1]
HEADER = '''From Coq Require Import List ZArith.
Require Import Ex.External.CPUISAReadyBatches.
Import ListNotations CPUISAReadyBatches CPUReadyOperand.CPUReadyOperand
 ExtendedSVRegisterBank.ExtendedSVRegisterBank.
Local Open Scope Z_scope.
Definition batches := [(10%nat,[WriteLane 1 4]);(11%nat,[]);
 (12%nat,[WriteLane 2 8;WriteLane 1 9])].
Definition slots := [Some(1,Some 4);Some(2,Some 8);Some(1,Some 9)].
'''


class ReadyBatchTests(unittest.TestCase):
    def compile(self, body, succeeds):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder)/'ReadyCheck.v'
            path.write_text(HEADER+body)
            result = subprocess.run([str(ROOT/'_opam/bin/coqc'), *framework.FLAGS,
                                     str(path)], cwd=ROOT, capture_output=True,
                                    text=True, timeout=120)
            self.assertEqual(result.returncode == 0, succeeds, result.stdout+result.stderr)
            self.assertEqual(path.with_suffix('.vo').exists(), succeeds)

    def test_empty_and_multiple_operations_preserve_youngest(self):
        self.compile('''Example related:
 Forall2 SlotRelated slots(batch_writes 32 1 batches).
Proof. repeat constructor;reflexivity. Qed.
Example latest:resolve 0(fun _=>77)1 slots=Some 9.
Proof. reflexivity. Qed.
Example zero:resolve 0(fun _=>77)0 slots=Some 0.
Proof. reflexivity. Qed.
Example reset_lane:batch_writes 8 1 [(0%nat,[ResetBank 32 513])]=[Some(1,2)].
Proof. reflexivity. Qed.
''', True)

    def test_unready_youngest_cannot_fall_back_to_old_value(self):
        self.compile('''Example waiting:
 resolve 0(fun _=>77)1 [Some(1,Some 4);Some(1,None)]=None.
Proof. reflexivity. Qed.
''', True)
        self.compile('''Example illegal_fallback:
 resolve 0(fun _=>77)1 [Some(1,Some 4);Some(1,None)]=Some 4.
Proof. reflexivity. Qed.
''', False)

    def test_wrong_ready_value_rejected(self):
        self.compile('''Example invalid_relation:
 Forall2 SlotRelated [Some(1,Some 4);Some(2,Some 8);Some(1,Some 4)]
 (batch_writes 32 1 batches).
Proof. repeat constructor;reflexivity. Qed.
''', False)


if __name__ == '__main__':
    unittest.main()
