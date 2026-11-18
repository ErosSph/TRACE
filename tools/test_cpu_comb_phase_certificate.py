import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import cpu_comb_phase_certificate as phase


class PhaseTests(unittest.TestCase):
    def test_source_keeps_actual_positive_fuel_and_complete_order_check(self):
        profile={'ast':{'program':'New.original'}}
        with patch.object(phase.registry,'proposal',return_value=({'source_sha256':'ast'},'base\n',3))as proposed:
            _,text,count=phase.phase_source(profile)
        proposed.assert_called_once_with(profile,True)
        self.assertEqual(count,5)
        self.assertIn('Nat.ltb 0(lfp_fuel New.original)',text)
        self.assertIn('sequential_writers_disjointb New.original=true',text)
        self.assertIn('original_positive_phase New.original',text)
        self.assertIn('Local Transparent actual_order.',text)
        self.assertNotIn('lfp_fuel New.original=1',text)
        self.assertNotIn('Pico',text)
        self.assertNotIn('Admitted',text)

    def test_nonzero_residuals_cannot_reach_full_phase_compilation(self):
        with tempfile.TemporaryDirectory()as directory, \
             patch.object(phase.registry,'check_profile',return_value={'accepted':True,'counts':{'residual':1}}), \
             patch.object(phase,'run_stage')as run:
            result=phase.check_profile({},Path(directory)/'out')
        run.assert_not_called()
        self.assertFalse(result['accepted'])
        self.assertFalse(result['original_full_phase_proved'])
        self.assertEqual(result['status'],'unproved_original_producers_remain')

    def test_failed_coverage_cannot_be_hidden(self):
        with tempfile.TemporaryDirectory()as directory, \
             patch.object(phase.registry,'check_profile',return_value={'accepted':False}), \
             patch.object(phase,'run_stage')as run:
            result=phase.check_profile({},Path(directory)/'out')
        run.assert_not_called()
        self.assertEqual(result['status'],'coverage_check_failed')

    def run_mock_native(self,log,coqc_exit=0,kernel_exit=0):
        with tempfile.TemporaryDirectory()as directory, \
             patch.object(phase.registry,'check_profile',return_value={'accepted':True,'counts':{'residual':0}}), \
             patch.object(phase,'phase_source',return_value=({'source_sha256':'ast'},'candidate\n',1)), \
             patch.object(phase,'run_stage',side_effect=[
                 (subprocess.CompletedProcess([],coqc_exit,log,''),False),
                 (subprocess.CompletedProcess([],kernel_exit,'',''),False)]):
            return phase.check_profile({},Path(directory)/'out')

    def test_success_is_full_phase_not_global_invariant_or_itree(self):
        result=self.run_mock_native('AUTO_ADAPTER_ASSUMPTIONS_0\nClosed under the global context\n')
        self.assertTrue(result['accepted'])
        self.assertTrue(result['original_full_phase_proved'])
        self.assertFalse(result['global_invariant_synthesized'])
        self.assertFalse(result['itree_refinement_proved'])

    def test_native_failure_audit_failure_or_kernel_failure_reject(self):
        good='AUTO_ADAPTER_ASSUMPTIONS_0\nClosed under the global context\n'
        for args in (('Error',1,0),('AUTO_ADAPTER_ASSUMPTIONS_0\nAxioms: bad : False\n',0,0),(good,0,1)):
            with self.subTest(args=args):self.assertFalse(self.run_mock_native(*args)['accepted'])

    def test_persistent_library_cannot_escape_or_overwrite(self):
        with tempfile.TemporaryDirectory()as directory:
            root=Path(directory).resolve();path=root/'src/Ex/Generated/Phase.v'
            with patch.object(phase.adapter,'ROOT',root), \
                 patch.object(phase,'phase_source',return_value=(None,'candidate\n',5)):
                with self.assertRaises(ValueError):phase.emit_library({},root/'Elsewhere.v')
                phase.emit_library({},path)
                self.assertEqual(path.read_text(),'candidate\n')
                path.write_text('user proof\n')
                with self.assertRaises(ValueError):phase.emit_library({},path)
                self.assertEqual(path.read_text(),'user proof\n')
