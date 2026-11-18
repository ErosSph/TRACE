import unittest
import tempfile
from pathlib import Path
from unittest.mock import patch

import cpu_auto_adapter as adapter
import cpu_plan_slices as slices


def ast_for(text):
    body=adapter.Parser(text).complete()
    proc=dict(name='process_19',body=body,kind='Sequential',writers=sorted({
        adapter.root_of(n.args[2]) for n in adapter.walk(body) if n.name=='SAssign'}))
    return dict(module='Novel',processes=[proc])


def plan_for(text):
    return adapter.analyze(ast_for(text))['plans'][0][1]


class SliceTests(unittest.TestCase):
    def test_persistent_emission_does_not_overwrite_or_claim_checked_proof(self):
        result=({},dict(residuals=[]),'generated source',1,[dict(root=9)])
        with tempfile.TemporaryDirectory() as tmp,patch.object(slices,'proposal',return_value=result):
            path=Path(tmp)/'Slices.v'
            emitted=slices.emit_library({},path,[9])
            self.assertFalse(emitted['coq_checked'])
            slices.emit_library({},path,[9],True)
            with self.assertRaises(ValueError):slices.emit_library({},path,[9])
            with patch.object(slices,'proposal',return_value=(*result[:2],'changed',*result[3:])):
                with self.assertRaises(ValueError):slices.emit_library({},path,[9],True)

    def test_zero_fuel_is_identity_not_truncation(self):
        plan=plan_for('SAssign true (EVar 17 2) (LVar 17 9)')
        self.assertIs(slices.slice_plan(plan,9,0),plan)

    def test_drops_other_writes_not_rhs_dependencies(self):
        plan=plan_for('SSeq [SAssign true (EConst 17 8) (LVar 17 2); SAssign true (EVar 17 2) (LVar 17 9)]')
        children=slices.slice_plan(plan,9).args[0].args
        self.assertEqual(children[0].name,'NEmpty')
        self.assertEqual(children[1],plan.args[0].args[1])
        self.assertIn('(EVar 17 2)',adapter.render(children[1]))

    def test_guard_and_reset_paths_preserved(self):
        plan=plan_for('SIf (EVar 1 1) (SAssign true (EVar 17 2) (LVar 17 9)) (SAssign true (EConst 17 0) (LVar 17 9))')
        projected=slices.slice_plan(plan,9)
        self.assertEqual(projected,plan)
        self.assertEqual(projected.args[0],plan.args[0])

    def test_case_keys_defaults_and_priority_not_reordered(self):
        plan=plan_for('SCase (EVar 2 1) [(None, SAssign true (EConst 17 2) (LVar 17 8)); (Some (EConst 2 1), SAssign true (EConst 17 3) (LVar 17 9)); (None, SAssign true (EConst 17 4) (LVar 17 9))]')
        projected=slices.slice_plan(plan,9)
        self.assertEqual([a.args[0] for a in projected.args[1].args],
            [a.args[0] for a in plan.args[1].args])
        self.assertEqual(projected.args[1].args[0].args[1].name,'NEmpty')
        self.assertEqual(projected.args[1].args[1:],plan.args[1].args[1:])

    def test_multiple_target_writes_and_partial_target_not_collapsed(self):
        plan=plan_for('SSeq [SAssign true (EConst 8 7) (LSel 8 (LVar 32 9) (EConst 5 8)); SAssign true (EVar 32 2) (LVar 32 9)]')
        self.assertEqual(slices.slice_plan(plan,9),plan)

    def test_unknown_plan_is_not_silently_accepted(self):
        with self.assertRaises(ValueError):
            slices.slice_plan(adapter.Term('Unknown'),9)

    def test_generated_certificate_checks_proposal_against_actual_full_plan(self):
        ast=ast_for('SSeq [SAssign true (EVar 17 2) (LVar 17 9); SAssign true (EConst 17 7) (LVar 17 8)]')
        profile={'ast':dict(file='unused',module='Novel.AST',program='Actual.program')}
        with patch.object(adapter,'load_ast',return_value=ast):
            _,_,source,count,metrics=slices.proposal(profile,[9])
        self.assertIn('slice_plan 512 9%nat process_19_plan',source)
        self.assertIn('checked_sliced_phase Actual.program 9%nat',source)
        self.assertIn('(LVar 17 8)',source)  # complete original writer is checked
        self.assertEqual(metrics[0]['original_assignments'],2)
        self.assertEqual(metrics[0]['sliced_assignments'],1)
        self.assertEqual(count,6)
        self.assertNotIn('Admitted',source)


if __name__=='__main__':
    unittest.main()
