import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import cpu_add_write_history as history


class Tests(unittest.TestCase):
    def setUp(self):
        self.raw = dict(source_sha256='configured', processes=[])
        self.fields = []
        self.scalars = []
        for index, root in enumerate([100, 200, 300]):
            name = 'p' + str(index)
            parent = [50, 100, 200][index]
            recipe = '(Select (EVar 1 2) Capture Unknown)'
            self.raw['processes'].append(dict(name=name, kind='Sequential', writers=[root],
                events='[]', body=history.rtl.Term('SSkip')))
            self.fields.append(dict(process=name, valid_root=index+10, source_valid=index+9, recipe=recipe))
            self.scalars.append(dict(root=root, width=1, process=name,
                next_expression=f'(ECond 1 (EVar 1 2) (EVar 1 {parent}) (EConst 1 0))'))
        self.covered = dict(coverage=dict(covered_fields=self.fields))

    def discover(self):
        with patch.object(history.admission.observation.origin.pending, 'analyze',
                          return_value=dict(scalar_transitions=self.scalars)):
            return history.discover(self.raw, dict(write=100), self.covered)

    def test_real_predecessor_order_not_sorted_names(self):
        plan = self.discover()
        self.assertEqual([r['root'] for r in plan['rows']], [100, 200, 300])
        self.assertEqual([r['route']['terminal'] for r in plan['rows'][1:]], [100, 200])

    def test_broken_identity_predecessor_rejected(self):
        self.scalars[2]['next_expression'] = '(ECond 1 (EVar 1 2) (EVar 1 100) (EConst 1 0))'
        with self.assertRaisesRegex(ValueError, 'predecessor'):
            self.discover()

    def test_duplicate_candidate_rejected(self):
        self.scalars.append(copy.deepcopy(self.scalars[1]))
        with self.assertRaisesRegex(ValueError, 'unique'):
            self.discover()

    def test_wrong_recipe_guard_rejected(self):
        self.fields[1]['recipe'] = '(Select (EVar 1 3) Capture Unknown)'
        with self.assertRaisesRegex(ValueError, 'unique'):
            self.discover()

    def test_wrong_field_width_not_fitted(self):
        self.scalars[1]['width'] = 2
        with self.assertRaisesRegex(ValueError, 'unique'):
            self.discover()

    def source(self):
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory) / 'plan.json').write_text(json.dumps(dict(paths=[])))
            with patch.object(history.admission.observation.origin.expressions, 'proposal',
                              return_value=(None, [], [], '', 0)), \
                 patch.object(history.admission.comb, 'proposal',
                              return_value=(None, dict(residuals=[], ports=[]), '')):
                return history.render(dict(history=directory, ast_module='Input.AST'),
                    dict(self.raw, module='DUT'), dict(ast=dict(program='DUT.program')),
                    self.discover(), dict(fields=[dict(source=50)], reset=2))

    def test_final_runtime_target_does_not_take_per_prefix_correctness(self):
        target = self.source().split('Theorem reset_reachable_add_write_controls', 1)[1].split('Proof.', 1)[0]
        self.assertIn('Forall Runtime.W.Environment events', target)
        self.assertIn('Runtime.boot_history image events', target)
        self.assertNotIn('InputsAlong', target)
        self.assertNotIn('HeadsAlong', target)
        self.assertNotIn('Joint pre', target)

    def test_selection_does_not_replace_physical_coverage_or_queue(self):
        source = self.source()
        relation = source.split('Definition Joint', 1)[1].split('Theorem actual_phase', 1)[0]
        self.assertIn('Covered.CoveredCapturedFields pre packed', relation)
        self.assertEqual(relation.count('SelectedValidField'), 3)
        self.assertNotIn('selected_tag', relation)
        self.assertNotIn('pending', relation)

    def test_phase_consumer_uses_actual_capture_and_original_tag_advance(self):
        source = self.source()
        self.assertIn('GeneratedAdmissionWrite.AdmissionWrite.actual_add_capture_write', source)
        self.assertIn('Covered.advance_capture_fields ev pre packed tt', source)
        self.assertIn('Covered.covered_capture_step', source)
        self.assertIn('actual_selected_valid_expression_phase', source)


if __name__ == '__main__':
    unittest.main()
