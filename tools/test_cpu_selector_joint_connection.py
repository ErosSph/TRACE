import unittest
import tempfile
from pathlib import Path
from unittest.mock import patch
import cpu_selector_joint_connection as c


class JointConnectionTests(unittest.TestCase):
    def test_unsupported_schema_does_not_invent_empty_history(self):
        with tempfile.TemporaryDirectory() as directory, \
             patch.object(c.history.origin,'raw_binding',return_value=({},None,None)), \
             patch.object(c.history.birth,'discover',return_value=dict(captures=[])), \
             patch.object(c.history.fields.coverage,'discover',return_value=dict(covered_fields=[])), \
             patch.object(c.history.birth,'check',side_effect=AssertionError('must not run')):
            r=c.check_auto('raw.v','Raw.AST',Path(directory)/'out')
        self.assertFalse(r['accepted'])
        self.assertEqual(r['status'],'unsupported_history_schema')

    def test_dependency_failure_prevents_connection(self):
        with tempfile.TemporaryDirectory() as directory, \
             patch.object(c.history.origin,'raw_binding',return_value=({},None,None)), \
             patch.object(c.history.birth,'discover',return_value=dict(captures=[{}])), \
             patch.object(c.history.fields.coverage,'discover',return_value=dict(covered_fields=[{}])), \
             patch.object(c.history.birth,'check',return_value=dict(accepted=False)), \
             patch.object(c,'check',side_effect=AssertionError('unchecked dependencies')):
            r=c.check_auto('raw.v','Raw.AST',Path(directory)/'out')
        self.assertEqual(r['failed_stage'],'capture-birth')
        self.assertFalse(r['complete_R_generated'])

    def test_exact_width_terminal_and_stable_wire_numbering(self):
        plan=dict(sources=[dict(width=5,input=10,terminal=20,edges=[{}]),
                           dict(width=1,input=11,terminal=21,edges=[{}]),
                           dict(width=5,input=10,terminal=20,edges=[{}])])
        rows,residuals=c.connections(plan,[dict(width=1,root=21,index=0)])
        self.assertEqual(rows[0]['wire_index'],1)
        self.assertEqual(len(residuals),1)

    def test_ambiguous_history_slot_is_not_chosen(self):
        plan=dict(sources=[dict(width=5,input=10,terminal=20,edges=[{}])])
        rows,residuals=c.connections(plan,[dict(width=5,root=20,index=0),dict(width=5,root=20,index=1)])
        self.assertEqual(rows,[])
        self.assertTrue(residuals)


if __name__=='__main__':unittest.main()
