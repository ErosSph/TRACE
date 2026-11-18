import tempfile
import unittest
from pathlib import Path
from cpu_joint_obligations import plan, ROLE_OBLIGATIONS


class JointObligationTests(unittest.TestCase):
    def make_plan(self, old=False):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'AST.v').write_text('actual syntax')
            p = {'ast': {'file': 'AST.v', 'module': 'New.AST', 'program': 'AST.cpu'}}
            if old:
                p.update(api='cycle', evidence={'cycle_checked': 'exact old_proof.'})
            return plan(p, root)

    def test_old_evidence_cannot_close_new_joint(self):
        result = self.make_plan(True)
        self.assertFalse(result['goal_complete'])
        self.assertFalse(result['existing_global_evidence_discharges_new_obligations'])
        self.assertTrue(all(x['status'] == 'unproved' for x in result['obligations']))

    def test_every_design_obligation_is_explicit(self):
        result = self.make_plan()
        self.assertEqual(len(result['obligations']), 9)
        self.assertEqual({x['id'] for x in result['obligations']}, {x[0] for x in ROLE_OBLIGATIONS})
        self.assertEqual(len(result['required_checked_arguments']), 6)

    def test_actual_source_and_program_are_bound(self):
        import hashlib
        result = self.make_plan()
        self.assertEqual(result['source_sha256'], hashlib.sha256(b'actual syntax').hexdigest())
        self.assertEqual(result['actual_program'], 'AST.cpu')
        self.assertIn('Physical s retired frontier', result['invariant'])
        self.assertIn('FormalSpec.run1', result['isa_effect'])

    def test_computed_rank_does_not_assume_bounded_progress(self):
        result = self.make_plan()
        alternative = result['automatic_rank_alternative']
        self.assertEqual(alternative['status'], 'design_bound_unproved')
        self.assertFalse(alternative['may_add_environment_assumption'])
        self.assertEqual(alternative['replaces'], 'Hrank')
        self.assertIn('Hbounded', alternative['requires'])

    def test_boundary_entry_does_not_invent_a_uniform_bound(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); (root/'AST.v').write_text('actual syntax')
            result=plan({'ast':{'file':'AST.v','module':'New.AST','program':'AST.cpu'},
                'joint_binding':{'transfer_mode':'boundary_entry'}},root)
        self.assertEqual(len(result['required_checked_arguments']),5)
        self.assertIn('Boundary',result['composition_theorem'])
        self.assertEqual(result['automatic_rank_alternative']['status'],
            'not_required_for_finite_commit_segments')
        self.assertFalse(result['goal_complete'])


if __name__ == '__main__':
    unittest.main()
