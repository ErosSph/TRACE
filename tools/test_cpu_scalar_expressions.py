import unittest
import tempfile
from pathlib import Path
from unittest.mock import patch
import cpu_auto_adapter as a
import cpu_scalar_expressions as e


def ast_for(text):
    body=a.Parser(text).complete()
    return dict(module='Unregistered',processes=[dict(name='process_19',kind='Sequential',
        body=body,writers=sorted({a.root_of(n.args[2]) for n in a.walk(body) if n.name=='SAssign'}))])


def plan_for(text):return a.analyze(ast_for(text))['plans'][0][1]
def seed():return a.Term('EVar',(a.Term('17'),a.Term('9')))


class ScalarExpressionTests(unittest.TestCase):
    def test_emit_source_is_not_a_checked_proof_and_preserves_old_file(self):
        proposal=({},[],[dict(root=9)],'generated source',1)
        with tempfile.TemporaryDirectory() as tmp,patch.object(e,'proposal',return_value=proposal):
            path=Path(tmp)/'Expr.v'
            self.assertFalse(e.emit_library({},path,[9])['coq_checked'])
            e.emit_library({},path,[9],True)
            with self.assertRaises(ValueError):e.emit_library({},path,[9])
            with patch.object(e,'proposal',return_value=(*proposal[:3],'changed',1)):
                with self.assertRaises(ValueError):e.emit_library({},path,[9],True)

    def test_guarded_hold_is_not_assumed_to_capture(self):
        plan=plan_for('SIf (EVar 1 1) (SAssign true (EVar 17 2) (LVar 17 9)) SSkip')
        expr=e.compile_expression(plan,9,17,seed())
        self.assertEqual(expr.name,'ECond')
        self.assertEqual(expr.args[-1],seed())

    def test_nba_rhs_is_not_rewritten_by_prior_write(self):
        plan=plan_for('SSeq [SAssign true (EConst 17 7) (LVar 17 2); SAssign true (EVar 17 2) (LVar 17 9)]')
        result=e.compile_expression(plan,9,17,seed())
        self.assertEqual(a.render(result),'(EVar 17 2)')

    def test_later_guarded_write_uses_previous_expression_only_as_hold(self):
        plan=plan_for('SSeq [SAssign true (EConst 17 7) (LVar 17 9); SIf (EVar 1 1) (SAssign true (EVar 17 2) (LVar 17 9)) SSkip]')
        expr=e.compile_expression(plan,9,17,seed())
        self.assertEqual(a.render(expr.args[-1]),'(EConst 17 7)')
        self.assertEqual(a.render(expr.args[-2]),'(EVar 17 2)')

    def test_case_preserves_keys_and_last_default(self):
        plan=plan_for('SCase (EVar 2 1) [(None,SAssign true (EConst 17 3) (LVar 17 9)); (Some (EConst 2 1),SAssign true (EConst 17 5) (LVar 17 9)); (None,SAssign true (EConst 17 7) (LVar 17 9))]')
        expr=e.compile_expression(plan,9,17,seed())
        self.assertEqual(expr.name,'ECond')
        self.assertEqual(a.render(expr.args[-2]),'(EConst 17 5)')
        self.assertEqual(a.render(expr.args[-1]),'(EConst 17 7)')

    def test_partial_target_and_wrong_width_are_rejected(self):
        for text in ['SAssign true (EConst 8 1) (LSel 8 (LVar 17 9) (EConst 5 0))',
                     'SAssign true (EConst 8 1) (LVar 8 9)']:
            self.assertIsNone(e.compile_expression(plan_for(text),9,17,seed()))

    def test_empty_guards_are_eliminated_structurally(self):
        plan=plan_for('SIf (EVar 1 199) SSkip (SCase (EVar 32 299) [(None,SSkip)])')
        self.assertEqual(e.compile_expression(plan,9,17,seed()),seed())

    def test_depth_exhaustion_is_failure(self):
        self.assertIsNone(e.compile_expression(a.Term('NEmpty'),9,17,seed(),0))

    def test_generated_expressions_are_checked_against_actual_plan(self):
        ast=ast_for('SIf (EVar 1 1) (SAssign true (EVar 17 2) (LVar 17 9)) SSkip')
        profile={'ast':dict(file='unused',module='Unregistered.AST',program='Actual.program')}
        with patch.object(a,'load_ast',return_value=ast):
            _,residuals,outputs,source,count=e.proposal(profile,[9])
        self.assertFalse(residuals)
        self.assertEqual(len(outputs),1)
        self.assertEqual(count,7)
        self.assertIn('checked_sliced_scalar_phase',source)
        self.assertIn('compile_scalar 512 9%nat 17',source)
        self.assertIn('Actual.program',source)
        self.assertNotIn('Admitted',source)


if __name__=='__main__':unittest.main()
