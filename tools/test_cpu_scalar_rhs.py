import tempfile
from pathlib import Path
import unittest
from unittest.mock import patch

import cpu_auto_adapter as adapter
import cpu_scalar_rhs as rhs


def proc(name, text, kind='Sequential'):
    body = adapter.Parser(text).complete()
    return dict(name=name, body=body, kind=kind, writers=sorted({
        adapter.root_of(n.args[2]) for n in adapter.walk(body) if n.name == 'SAssign'}))


class RHSTests(unittest.TestCase):
    def ast(self, body):
        return dict(module='Unregistered', processes=[proc('process_19', body)])

    def test_novel_width_and_conditional_expression(self):
        ast = self.ast('SSeq [SAssign true (ECond 17 (EVar 1 2) (EVar 17 3) (EConst 17 4)) (LVar 17 12)]')
        result = rhs.analyze(ast, [12])
        self.assertFalse(result['residuals'])
        self.assertEqual(result['supported'][0]['width'], 17)
        self.assertEqual(result['supported'][0]['rhs'].name, 'ECond')

    def test_outer_control_is_explicit_residual(self):
        for text in ('SIf (EVar 1 2) (SAssign true (EVar 32 1) (LVar 32 12)) SSkip',
            'SCase (EVar 1 2) [(None, SAssign true (EVar 32 1) (LVar 32 12))]'):
            result = rhs.analyze(self.ast(text), [12])
            self.assertFalse(result['supported'])
            self.assertIn('control flow', result['residuals'][0]['reason'])

    def test_multiple_assignments_not_last_assignment_guess(self):
        result = rhs.analyze(self.ast('SSeq [SAssign true (EConst 32 0) (LVar 32 12); SAssign true (EConst 32 1) (LVar 32 12)]'), [12])
        self.assertIn('exactly one whole-root', result['residuals'][0]['reason'])

    def test_multiple_actual_writers_not_singleton_guess(self):
        ast = self.ast('SAssign true (EVar 32 1) (LVar 32 12)')
        ast['processes'].append(proc('process_23', 'SAssign true (EVar 32 2) (LVar 32 12)'))
        result = rhs.analyze(ast, [12])
        self.assertIn('exactly one complete actual', result['residuals'][0]['reason'])

    def test_indexed_and_blocking_rejected(self):
        for text in ('SAssign true (EVar 32 1) (LSel 32 (LVar 1024 12) (EConst 10 0))',
            'SAssign false (EVar 32 1) (LVar 32 12)'):
            self.assertTrue(rhs.analyze(self.ast(text), [12])['residuals'])

    def test_generated_phase_binds_real_program_and_preserves_full_plan(self):
        ast = self.ast('SSeq [SAssign true (EVar 32 1) (LVar 32 12); SAssign true (EConst 1 1) (LVar 1 14)]')
        result = rhs.analyze(ast, [12])
        source = rhs.render_rhs(dict(module='Unregistered.AST', program='Actual.program'), ast, result)
        self.assertIn('PlanRootCertificate Actual.program 12%nat', source)
        self.assertIn('(LVar 1 14)', source)
        self.assertIn('root_12_compiled_phase ev pre HE', source)
        self.assertIn('Print Assumptions root_12_rhs_phase.', source)
        self.assertNotIn('Admitted', source)

    def test_emit_and_check_refuse_overwrite_mismatch_and_residual(self):
        ast = self.ast('SAssign true (EVar 32 1) (LVar 32 12)')
        proposal = (ast, rhs.analyze(ast, [12]), 'checked source\n')
        with tempfile.TemporaryDirectory() as tmp, patch.object(rhs, 'proposal', return_value=proposal):
            dest = Path(tmp)/'RHS.v'
            rhs.emit_library({}, dest, [12])
            rhs.emit_library({}, dest, [12], True)
            with self.assertRaises(ValueError):
                rhs.emit_library({}, dest, [12])
            with patch.object(rhs, 'proposal', return_value=(*proposal[:2], 'mismatch')):
                with self.assertRaises(ValueError):
                    rhs.emit_library({}, dest, [12], True)
            bad = dict(proposal[1], residuals=[dict(root=12, reason='unsupported')])
            with patch.object(rhs, 'proposal', return_value=(ast, bad, '')):
                with self.assertRaises(ValueError):
                    rhs.emit_library({}, Path(tmp)/'Unsupported.v', [12])

    def test_base_render_uses_imported_actual_certificates_and_only_rhs_audits(self):
        ast = self.ast('SAssign true (EVar 32 1) (LVar 32 12)')
        found = rhs.analyze(ast, [12])
        source = rhs.render_rhs(dict(module='Unregistered.AST', program='Actual.program'),
            ast, found, 'Ex.Generated.Base')
        self.assertIn('Base.root_12_compiled_phase', source)
        self.assertIn('Base.process_19_plan', source)
        self.assertNotIn('Definition process_19_plan', source)
        self.assertIn('AUTO_ADAPTER_ASSUMPTIONS_0', source)
        self.assertNotIn('AUTO_ADAPTER_ASSUMPTIONS_1', source)
        with self.assertRaises(ValueError):
            rhs.render_rhs({}, ast, found, 'Bad;admit')

    def test_base_source_must_exactly_match_current_scalar_generation(self):
        found = dict(residuals=[], analysis=dict(roots=[12]))
        with tempfile.TemporaryDirectory() as tmp, patch.object(rhs.scalar, 'proposal',
                return_value=({}, found, 'base source')):
            path = Path(tmp)/'Base.v'
            with self.assertRaises(ValueError):
                rhs.base_provenance({}, [12], 'X.Base', path)
            path.write_text('different source')
            with self.assertRaises(ValueError):
                rhs.base_provenance({}, [12], 'X.Base', path)
            path.write_text('base source')
            self.assertTrue(rhs.base_provenance({}, [12], 'X.Base', path)['source_matches_scalar_generator'])
            with self.assertRaises(ValueError):
                rhs.base_provenance({}, [12], None, path)


if __name__ == '__main__':
    unittest.main()
