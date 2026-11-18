import unittest
import tempfile
from pathlib import Path
from unittest.mock import patch
import cpu_control_capture_frontier as c
import cpu_pending_llm as llm


class CaptureFrontierTests(unittest.TestCase):
    def test_transform_success_keeps_unknown_paths_as_obligations(self):
        direct=c.captures.direct
        with tempfile.TemporaryDirectory() as directory, \
             patch.object(c.sources.selectors.origin,'raw_binding',return_value=({}, {}, [])), \
             patch.object(c,'discover',return_value=dict(transformed_captures=[{}])), \
             patch.object(direct,'discover_control_transforms',return_value=dict(
                 projections=[dict(root=8,unknown_paths=[dict(reason='reset')])],residuals=[])), \
             patch.object(direct,'check',return_value=dict(accepted=True)) as native:
            r=c.check_transforms('raw.v','Raw.AST',Path(directory)/'out')
        self.assertTrue(r['reference_functions_checked'])
        self.assertTrue(r['unknown_paths'])
        self.assertFalse(r['upstream_identity_proved'])
        self.assertFalse(r['complete_R_generated'])
        self.assertEqual(native.call_args.kwargs['source_mode'],'control_transform')

    def test_unsupported_transform_is_not_no_transform(self):
        direct=c.captures.direct
        with tempfile.TemporaryDirectory() as directory, \
             patch.object(c.sources.selectors.origin,'raw_binding',return_value=({}, {}, [])), \
             patch.object(c,'discover',return_value=dict(transformed_captures=[{}])), \
             patch.object(direct,'discover_control_transforms',return_value=dict(projections=[],residuals=[dict(root=8)])):
            r=c.check_transforms('raw.v','Raw.AST',Path(directory)/'out')
        self.assertEqual(r['status'],'unsupported_transformed_capture')
        self.assertFalse(r['accepted'])

    def test_multiple_sampling_boundaries_are_retained(self):
        parse=lambda s:c.rtl.Parser(s).complete()
        ast=dict(processes=[
            dict(name='stage',kind='Sequential',writers=[20],events='edge',body=parse('SAssign true (EVar 1 30) (LVar 1 20)')),
            dict(name='decode',kind='Combinational',writers=[30],events='',body=parse('SAssign false (EConst 1 1) (LVar 1 30)'))])
        rows=[dict(root=10,width=1,process='later',expression=parse('EVar 1 20')),
            dict(root=20,width=1,process='stage',expression=parse('ECond 1 (EVar 1 4) (EVar 1 20) (EVar 1 30)'))]
        with patch.object(c.sources,'discover',return_value=dict(sources=[dict(terminal=10,kind='sequential')])), \
             patch.object(c.captures,'scalar_candidates',return_value=rows):
            r=c.discover(ast)
        self.assertEqual([p['root'] for p in r['producers']],[30])
        self.assertEqual(len(r['captures']),2)
        self.assertEqual(r['captures'][1]['conditions'],(False,))
        self.assertFalse(r['token_history_proved'])

    def test_missing_phase_expression_not_empty_history(self):
        with patch.object(c.sources,'discover',return_value=dict(sources=[dict(terminal=10,kind='sequential')])), \
             patch.object(c.captures,'scalar_candidates',return_value=[]):
            r=c.discover(dict(processes=[]))
        self.assertEqual(len(r['residuals']),1)
        self.assertEqual(r['producers'],[])

    def test_transformed_capture_is_not_identity_and_remains_in_history(self):
        parse=lambda s:c.rtl.Parser(s).complete()
        expression=parse('EExtend 32 false (ESel 31 (EVar 32 85) (EConst 5 0))')
        with patch.object(c.sources,'discover',return_value=dict(sources=[dict(terminal=59,kind='sequential')])), \
             patch.object(c.captures,'scalar_candidates',return_value=[dict(root=59,width=32,process='stage',expression=expression)]), \
             patch.object(c.sources,'trace',return_value=dict(kind='external',terminal=85)):
            r=c.discover(dict(processes=[]))
        self.assertEqual(r['capture_fields'][0]['root'],59)
        self.assertFalse(r['transformed_captures'][0]['identity_copy'])
        self.assertEqual(r['transformed_captures'][0]['dependencies'][0]['root'],85)
        self.assertTrue(r['residuals'])
        self.assertEqual(r['captures'],[])

    def test_llm_strategy_is_closed_and_not_proof(self):
        slots={'producer':[dict(id='state_threaded_dependency_slice')]}
        prompt=llm.prompt(slots,[],'blocking_dependency')
        self.assertIn('NOT a proof',prompt['requirement'])
        with self.assertRaises(ValueError):
            llm.validate({'bindings':{'producer':'assume_correct'}},slots)
        with self.assertRaises(ValueError):
            llm.validate({'bindings':{'producer':'state_threaded_dependency_slice'},'proof':'Admitted'},slots)

    def test_llm_strategy_for_wrong_ast_rejected(self):
        with self.assertRaises(ValueError):
            c.selected_fallbacks(dict(source_sha256='current'),dict(residuals=[]),
                dict(ast_sha256='old',llm=dict(status='accepted_unproved')))

    def test_checked_strategy_reused_without_llm_and_without_scalar_producers(self):
        import cpu_state_threaded_slice as threaded
        plan=dict(producers=[],residuals=[dict(root=20,producer=30)])
        candidate=dict(root=30,process='arbitrary_name')
        with tempfile.TemporaryDirectory() as directory, \
             patch.object(c.sources.selectors.origin,'raw_binding',return_value=({},None,None)), \
             patch.object(c,'discover',return_value=plan), \
             patch.object(threaded,'discover',return_value=dict(candidates=[candidate])), \
             patch.object(threaded,'check',return_value=dict(accepted=True)) as native, \
             patch.object(c,'selected_fallbacks',side_effect=AssertionError('LLM route not needed')):
            result=c.check('raw.v','Raw.AST',Path(directory)/'out')
        native.assert_called_once()
        self.assertTrue(result['all_discovered_producers_checked'])
        self.assertFalse(result['complete_R_generated'])
        self.assertEqual(result['fallbacks'][0]['origin'],'reusable_checked_rule')

    def test_histories_follow_discovered_fields_and_preserve_failure(self):
        with tempfile.TemporaryDirectory() as directory, \
             patch.object(c.sources.selectors.origin,'raw_binding',return_value=({}, {}, [])), \
             patch.object(c,'discover',return_value=dict(captures=[dict(root=12),dict(root=4),dict(root=12)])), \
             patch.object(c.sources.selectors.origin.histories,'check_profile',
                 side_effect=[dict(accepted=True),dict(accepted=False)]) as native:
            result=c.check_histories('raw.v','Raw.AST',Path(directory)/'out')
        self.assertEqual(result['roots'],[4,12])
        self.assertEqual([call.args[2] for call in native.call_args_list],[[4],[12]])
        self.assertFalse(result['accepted'])
        self.assertFalse(result['token_history_proved'])


if __name__=='__main__':unittest.main()
