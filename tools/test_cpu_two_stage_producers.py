import unittest
from unittest.mock import patch
import cpu_auto_adapter as adapter
import cpu_two_stage_producers as generator


def body(first='EVar 8 7',second='EVar 8 2',key='EVar 1 8',nba='false',target='LVar 8 3'):
    return adapter.Parser('SSeq [SSeq ['
        f'SAssign {nba} ({first}) (LVar 8 2);'
        f'SCase (EConst 1 1) [(Some ({key}),SAssign false (EConst 8 9) (LVar 8 2))];'
        f'SAssign false ({second}) (LVar 8 3);'
        f'SCase (EConst 1 1) [(Some (EVar 1 8),SAssign false (EConst 8 11) ({target}))]'
        ']]').complete()


class TwoStageTests(unittest.TestCase):
    def test_cross_stage_read_is_retained_not_treated_as_old_state(self):
        first,second=generator.extract(body())
        self.assertEqual(first['root'],2)
        self.assertEqual(second['root'],3)
        self.assertIn(2,second['reads'])

    def test_feedback_rejected_in_defaults_and_case_keys(self):
        for kwargs in ({'first':'EVar 8 2'},{'first':'EVar 8 3'},
                       {'second':'EVar 8 3'},{'key':'EVar 1 2'},{'key':'EVar 1 3'}):
            with self.subTest(kwargs=kwargs),self.assertRaises(ValueError):
                generator.extract(body(**kwargs))

    def test_nba_and_incoherent_case_target_are_not_reinterpreted(self):
        for kwargs in ({'nba':'true'},{'target':'LVar 7 3'},{'target':'LVar 8 2'}):
            with self.subTest(kwargs=kwargs),self.assertRaises(ValueError):
                generator.extract(body(**kwargs))

    def test_actual_body_order_is_not_flattened_or_reordered(self):
        original=body()
        flattened=original.args[0].args[0]
        with self.assertRaises(ValueError):generator.extract(flattened)

    def test_unknown_design_generates_actual_shape_registration_and_proof(self):
        profile={'ast':dict(file='unused',module='New.AST',program='New.runtime')}
        ast=dict(module='AST',source_sha256='hash',statement_fuel=64,
            processes=[dict(name='process_0',kind='Combinational',body=body())])
        with patch.object(generator.adapter,'load_ast',return_value=ast):
            _,selected,residual,text,count=generator.proposal(profile)
        self.assertEqual(len(selected),1)
        self.assertEqual(residual,[])
        self.assertEqual(count,4)
        self.assertIn('run_process New.runtime s AST.process_0',text)
        self.assertIn('nth_error(processes New.runtime)0%nat=Some AST.process_0',text)
        self.assertIn('actual_two_stage_producer',text)
        self.assertIn('avoids_rootb',text)
        self.assertNotIn('Pico',text)
        self.assertNotIn('Admitted',text)

    def test_program_and_import_injection_rejected_before_read(self):
        for field in ('module','program'):
            ast=dict(file='unused',module='New.AST',program='New.runtime')
            ast[field]='New. Admitted.'
            with patch.object(generator.adapter,'load_ast')as read:
                with self.assertRaises(ValueError):generator.proposal({'ast':ast})
                read.assert_not_called()

    def test_full_phase_mode_requires_all_original_side_conditions(self):
        profile={'ast':dict(file='unused',module='New.AST',program='New.runtime')}
        ast=dict(module='AST',source_sha256='hash',statement_fuel=64,
            processes=[dict(name='process_0',kind='Combinational',body=body())])
        with patch.object(generator.adapter,'load_ast',return_value=ast):
            _,_,_,text,count=generator.proposal(profile,True)
        self.assertEqual(count,7)
        self.assertIn('residual_order producer_rules original_comb_order=[AST.process_0]',text)
        self.assertIn('ordered_preservationb original_comb_order=true',text)
        self.assertIn('lfp_fuel New.runtime=1%nat',text)
        self.assertIn('sequential_writers_disjointb New.runtime=true',text)
        self.assertIn('PhaseIndependentAt New.runtime ev pre',text)
        self.assertLess(text.index('Local Transparent original_comb_order.'),
            text.index('Theorem original_phase ev pre'))
        self.assertIn('original_phase_from_registry_residual producer_rules New.runtime',text)
        self.assertNotIn('PicoSource',text)
        self.assertNotIn('Admitted',text)

    def test_full_phase_mode_is_strict_boolean(self):
        for value in ('false',1,None):
            with self.assertRaises(ValueError):generator.proposal({},value)

    def test_kernel_cannot_be_skipped_after_compilation_uses_overall_deadline(self):
        import subprocess,tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory()as directory, \
             patch.object(generator,'proposal',return_value=({'source_sha256':'ast'},[],[],'candidate\n',1)), \
             patch.object(generator.time,'monotonic',side_effect=[0,0,1201,1201,1201]), \
             patch.object(generator,'run_stage',return_value=(subprocess.CompletedProcess([],0,
                 'AUTO_ADAPTER_ASSUMPTIONS_0\nClosed under the global context\n',''),False))as run:
            result=generator.check_profile({},Path(directory)/'out',1200,True)
        run.assert_called_once()
        self.assertFalse(result['accepted'])
        self.assertFalse(result['original_full_phase_proved'])
        self.assertTrue(result['kernel_not_run_due_to_overall_deadline'])

    def test_generated_library_stays_in_generated_directory_and_preserves_user_edits(self):
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory()as directory:
            root=Path(directory).resolve();path=root/'src/Ex/Generated/New.v'
            with patch.object(generator.adapter,'ROOT',root), \
                 patch.object(generator,'proposal',return_value=(None,[],[],'candidate\n',0)):
                with self.assertRaises(ValueError):generator.emit_library({},root/'Elsewhere.v')
                generator.emit_library({},path)
                self.assertEqual(path.read_text(),'candidate\n')
                path.write_text('existing user proof\n')
                with self.assertRaises(ValueError):generator.emit_library({},path)
                self.assertEqual(path.read_text(),'existing user proof\n')


if __name__=='__main__':unittest.main()
