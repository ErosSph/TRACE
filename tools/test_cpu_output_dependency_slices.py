import unittest
from pathlib import Path
from unittest.mock import patch
import cpu_auto_adapter as adapter
import cpu_output_dependency_slices as slices
import cpu_auto_pipeline as pipeline

def term(text):return adapter.Parser(text).complete()

class DependencySliceProposalTests(unittest.TestCase):
    def test_pipeline_checks_actual_ast_and_propagates_failure(self):
        with patch.object(pipeline.output_dependency_slices,'check') as check:
            self.assertIsNone(pipeline.check_output_dependency_components({},Path('/tmp'),1200))
        check.assert_not_called()
        p={'ast':{}}
        with patch.object(pipeline.output_dependency_slices,'check',return_value={'accepted':False}) as check:
            self.assertFalse(pipeline.check_output_dependency_components(p,Path('/tmp'),1200)['accepted'])
        check.assert_called_once_with(p,Path('/tmp/output-dependency-slices'),1200)

    def test_backward_temporary_closure_not_whole_controller(self):
        body=term('(SSeq [(SAssign false (EVar 8 9) (LVar 8 1)); (SAssign false (EVar 8 1) (LVar 8 2)); (SAssign false (EVar 8 7) (LVar 8 3))])')
        row=slices.backward_closure(body,2)
        self.assertEqual(row['kept'],[1,2])
        self.assertEqual(row['observed'],[1,2,9])
        self.assertNotIn(3,row['kept']);self.assertNotIn(7,row['observed'])

    def test_guard_and_all_case_keys_are_dependencies(self):
        body=term('(SCase (EVar 8 9) [(Some (EVar 8 7), (SAssign false (EConst 8 1) (LVar 8 1))); (Some (EVar 8 8), (SAssign false (EConst 8 2) (LVar 8 2)))])')
        row=slices.backward_closure(body,1)
        self.assertEqual(row['observed'],[1,7,8,9])
        self.assertEqual(row['kept'],[1])

    def test_nested_flags_shape_is_strict(self):
        selected=[{'rows':[{},{}]},{'rows':[]}]
        text='SLICE_DEPENDENCY_FLAGS [[true; false]; []]\nChars 1 - 2 [test] 0. secs\n'
        self.assertEqual(slices.parse_flags(text,selected),[[True,False],[]])
        for bad in (text.replace('false','unknown'),text+text,
                    text.replace('[true; false]','[true]')):
            with self.assertRaises(ValueError):slices.parse_flags(bad,selected)

if __name__=='__main__':unittest.main()
