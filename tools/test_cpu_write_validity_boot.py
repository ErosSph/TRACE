import unittest
from pathlib import Path
from unittest.mock import patch
import cpu_write_validity_boot as b


class WriteValidityBootTests(unittest.TestCase):
    def fixture(self):
        data=dict(entry=dict(capture=dict(carrier=10,valid_root=11)),rows=[dict(rd=20,write=21,valid=22)])
        env=dict(seed=dict(length=40,writes=[dict(root=30,value=dict(kind='image'))]),
            events=dict(rise=dict(changed_signal=0)),boot=dict(events=['rise']),
            actual_boot='Original.boot',encoder='Original.encode')
        return data,env

    def test_initial_rule_requires_actual_zero_not_an_assumed_value(self):
        seed=dict(writes=[dict(root=21,value=dict(kind='literal',value=1))])
        self.assertFalse(b.seed_zero_supported(seed,21))
        seed['writes'].append(dict(root=21,value=dict(kind='literal',value=0)))
        self.assertTrue(b.seed_zero_supported(seed,21))
        seed['writes'].append(dict(root=21,value=dict(kind='image')))
        self.assertFalse(b.seed_zero_supported(seed,21))

    def test_do_not_replace_bad_initial_data_with_zero(self):
        data,env=self.fixture();env['seed']['writes'].append(dict(root=21,value=dict(kind='literal',value=1)))
        with self.assertRaisesRegex(ValueError,'initial values'):b.render('Raw.program','Raw.AST',data,env)

    def test_external_writes_to_internal_fields_are_rejected(self):
        data,env=self.fixture();env['events']['rise']['changed_signal']=20
        with self.assertRaisesRegex(ValueError,'drives an invariant register'):b.render('Raw.program','Raw.AST',data,env)

    def test_lfp_and_initial_relation_not_left_as_boot_assumptions(self):
        data,env=self.fixture();source=b.render('Raw.program','Raw.AST',data,env)
        goal=source.split('Theorem boot_write_validity',1)[1].split('Proof.',1)[0]
        self.assertNotIn('->',goal)
        self.assertIn('checked_history Raw.program Catalog.actual_catalog Phi.actual_certificate',source)
        self.assertIn('Environment environment_protects_fields',source)
        self.assertIn('EnvironmentBinding.actual_boot_data words',source)

    def test_renderer_does_not_consult_old_cpu_proofs(self):
        data,env=self.fixture()
        with patch.object(Path,'read_text',side_effect=AssertionError('old theorem lookup')):
            source=b.render('Raw.program','Raw.AST',data,env)
        self.assertNotIn('Admitted',source)
        self.assertNotIn('Axiom ',source)


if __name__=='__main__':unittest.main()
