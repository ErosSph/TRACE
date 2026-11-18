import unittest
from pathlib import Path
from unittest.mock import patch
import cpu_captured_history_boot as h


class CapturedHistoryBootTests(unittest.TestCase):
    def fixture(self):
        return (dict(entry=dict(capture=dict(carrier=10,valid_root=11)),
                     rows=[dict(rd=20,write=21,valid=22)]),
                dict(seed=dict(length=40,writes=[]),events=dict(rise=dict(changed_signal=0))))

    def test_nonempty_seed_is_not_silently_replaced(self):
        data,env=self.fixture()
        env['seed']['writes']=[dict(root=22,value=dict(kind='literal',value=1))]
        with self.assertRaisesRegex(ValueError,'not empty'):h.render('Raw.p','Raw.AST',data,env)

    def test_environment_cannot_overwrite_tokens(self):
        data,env=self.fixture();env['events']['rise']['changed_signal']=20
        with self.assertRaisesRegex(ValueError,'history field'):h.render('Raw.p','Raw.AST',data,env)

    def test_history_is_constructed_not_assumed(self):
        data,env=self.fixture();s=h.render('Raw.p','Raw.AST',data,env)
        theorem=s.split('Theorem boot_and_runtime_related',1)[1].split('Proof.',1)[0]
        self.assertEqual(theorem.count('->'),1)
        self.assertIn('Forall W.Environment events',theorem)
        self.assertIn('checked_execution Raw.p',s)
        self.assertIn('boot_history image events',theorem)

    def test_no_old_inv_lookup(self):
        data,env=self.fixture()
        with patch.object(Path,'read_text',side_effect=AssertionError('proof lookup')):
            s=h.render('Raw.p','Raw.AST',data,env)
        self.assertNotIn('Admitted',s)
        self.assertNotIn('Axiom ',s)

    def test_stage_count_not_cpu_name_controls_history_shape(self):
        data,env=self.fixture()
        data['rows'].append(dict(rd=30,write=31,valid=32))
        s=h.render('Other.p','Other.AST',data,env)
        self.assertIn('@C.C.Build_ChainTags Token None None',s)
        self.assertIn('seed_zero_32',s)
        self.assertNotIn('Bzeeno',s)


if __name__=='__main__':unittest.main()
