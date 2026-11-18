import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import cpu_ready_selection_requirements as ready

class ReadySelectionTests(unittest.TestCase):
    def test_no_old_invariant_lookup(self):
        with patch.object(Path,'read_text',side_effect=AssertionError('old INV lookup')):
            s=ready.render('Raw.program',[dict(width=32,output_root=71)])
        self.assertIn('CombLFP Raw.program seed fixed',s)
        self.assertIn('eval_expr fixed guard<>0',s)
        self.assertIn('lookup address slots=Some None',s)
        self.assertNotIn('Admitted',s)

    def test_native_stall_and_consumption(self):
        root=ready.origin.ROOT
        header='''From Coq Require Import List ZArith.
Require Import Ex.External.CPUReadySelectionRequirements.
Import ListNotations ExtendedSV.ExtendedSV CPUReadySelectionRequirements.
Local Open Scope Z_scope.
'''
        cases=[('Inactive','''Example safe s:
 guarded_requirements (EConst 1 0) 32 (EConst 32 4) s (fun _=>4) 1
 [Some(1,Some 4);Some(1,None)].
Proof. intros H;exfalso;apply H;reflexivity. Qed.
''',True),('ActiveStale','''Example unsafe s:
 guarded_requirements (EConst 1 1) 32 (EConst 32 4) s (fun _=>4) 1
 [Some(1,Some 4);Some(1,None)].
Proof. intros H;vm_compute;reflexivity. Qed.
''',False),('ActiveFresh','''Example fresh s:
 guarded_requirements (EConst 1 1) 32 (EConst 32 9) s (fun _=>4) 1
 [Some(1,Some 4);Some(1,Some 9)].
Proof. intros H;reflexivity. Qed.
''',True)]
        with tempfile.TemporaryDirectory()as folder:
            for name,body,success in cases:
                path=Path(folder)/(name+'.v');path.write_text(header+body)
                p=subprocess.run([str(root/'_opam/bin/coqc'),*ready.origin.pending.rtl.framework.FLAGS,str(path)],cwd=root,capture_output=True,text=True,timeout=120)
                self.assertEqual(p.returncode==0,success,p.stdout+p.stderr)
                self.assertEqual(path.with_suffix('.vo').exists(),success)

if __name__=='__main__':unittest.main()
