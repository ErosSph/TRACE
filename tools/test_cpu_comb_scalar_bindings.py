import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import cpu_auto_adapter as a
import cpu_comb_scalar_bindings as c


def ast(body,kind='Combinational'):
    term=a.Parser(body).complete()
    return dict(module='Unnamed',processes=[dict(name='process_91',kind=kind,body=term,
        writers=sorted({a.root_of(n.args[2]) for n in a.walk(term) if n.name=='SAssign'}))])


class CombScalarBindingTests(unittest.TestCase):
    def test_not_restricted_to_rf_or_cpu_names(self):
        data=c.analyze(ast('SAssign false (EVar 17 2) (LVar 17 9)'),[9])
        self.assertFalse(data['residuals']);self.assertEqual(len(data['ports']),1)
        self.assertEqual(data['ports'][0]['output_root'],9)

    def test_preserves_complete_guarded_rhs(self):
        data=c.analyze(ast('SAssign false (ECond 17 (EVar 1 1) (EConst 17 0) (EVar 17 2)) (LVar 17 9)'),[9])
        self.assertEqual(a.render(data['ports'][0]['rhs']),
            '(ECond 17 (EVar 1 1) (EConst 17 0) (EVar 17 2))')

    def test_last_scalar_write_selected_without_dropping_prior_block(self):
        data=c.analyze(ast('SSeq [SAssign false (EConst 17 7) (LVar 17 9); SAssign false (EVar 17 2) (LVar 17 9)]'),[9])
        self.assertEqual(data['ports'][0]['assignment_index'],1)
        self.assertEqual(len(data['blocks'][0]['assignments']),2)

    def test_unknown_or_sequential_target_remains_residual(self):
        for data in [c.analyze(ast('SSkip'),[9]),
                     c.analyze(ast('SAssign true (EVar 17 2) (LVar 17 9)','Sequential'),[9])]:
            self.assertTrue(data['residuals']);self.assertEqual(data['ports'],[])

    def test_nested_statement_guard_not_flattened_away(self):
        data=c.analyze(ast('SIf (EVar 1 1) (SAssign false (EVar 17 2) (LVar 17 9)) SSkip'),[9])
        self.assertTrue(data['residuals']);self.assertEqual(data['ports'],[])

    def test_competing_writers_not_silently_selected(self):
        model=ast('SAssign false (EVar 17 2) (LVar 17 9)')
        model['processes'].append(dict(model['processes'][0],name='process_92'))
        self.assertTrue(c.analyze(model,[9])['residuals'])

    def test_generated_equality_bound_to_actual_block(self):
        model=ast('SAssign false (EVar 17 2) (LVar 17 9)')
        profile={'ast':dict(file='unused',module='New.AST',program='New.program')}
        with patch.object(a,'load_ast',return_value=model):
            _,_,source=c.proposal(profile,[9])
        self.assertIn('checked_scalar_block_binding New.program',source)
        self.assertIn('Lemma port_0_checked : scalar_block_bindingb actual_combs',source)
        self.assertIn('block_0_decomposes',source)
        self.assertNotIn('Admitted',source)

    def test_source_emission_is_not_kernel_success(self):
        model=ast('SAssign false (EVar 17 2) (LVar 17 9)')
        profile={'ast':dict(file='unused',module='New.AST',program='New.program')}
        with tempfile.TemporaryDirectory() as directory,patch.object(a,'load_ast',return_value=model):
            path=Path(directory)/'Comb.v';r=c.emit_library(profile,path,[9])
            self.assertFalse(r['coq_checked'])
            self.assertTrue(c.emit_library(profile,path,[9],check=True)['source_matches_generator'])
            with self.assertRaisesRegex(ValueError,'exists'):c.emit_library(profile,path,[9])
            path.write_text('changed')
            with self.assertRaisesRegex(ValueError,'differs'):c.emit_library(profile,path,[9],check=True)


if __name__=='__main__':unittest.main()
