import tempfile
from pathlib import Path
import unittest
from unittest.mock import patch

import cpu_auto_adapter as adapter
import cpu_scalar_captures as scalar


def proc(name, text, kind='Sequential'):
    body = adapter.Parser(text).complete()
    writers = sorted({adapter.root_of(n.args[2]) for n in adapter.walk(body)
        if n.name == 'SAssign'})
    return dict(name=name, body=body, kind=kind, writers=writers)


class ScalarTests(unittest.TestCase):
    def setUp(self):
        self.ast = dict(module='TestAST', processes=[
            proc('process_4', 'SAssign true (EVar 32 1) (LVar 32 8)'),
            proc('process_2', 'SAssign true (EVar 32 2) (LVar 32 8)'),
            proc('process_3', 'SAssign true (EVar 32 1) (LSel 32 (LVar 1024 9) (EConst 10 0))'),
            proc('process_7', 'SAssign false (EConst 1 0) (LVar 1 10)'),
            proc('process_8', 'SAssign true (EConst 1 0) (LVar 1 11)'),
            proc('process_9', 'SAssign false (EConst 1 0) (LVar 1 11)', 'Combinational')])

    def test_selection_preserves_all_writer_order(self):
        result = scalar.analyze(self.ast, [8])
        self.assertEqual([p['name'] for p, _ in result['analysis']['plans']],
            ['process_4', 'process_2'])
        self.assertEqual(result['analysis']['plan_roots'], [8])

    def test_default_identifies_scalar_but_reports_unsupported(self):
        result = scalar.analyze(self.ast)
        self.assertEqual(result['scalar_candidates'], [8, 10])
        self.assertEqual(result['analysis']['roots'], [8])
        self.assertEqual(result['residuals'][0]['root'], 10)

    def test_indexed_and_comb_roots_unsupported(self):
        result = scalar.analyze(self.ast, [9, 11, 999])
        self.assertEqual(len(result['residuals']), 3)
        self.assertFalse(result['analysis']['plans'])

    def test_invalid_selections(self):
        for roots in ([], [8, 8], [-1], [True]):
            with self.assertRaises(ValueError):
                scalar.analyze(self.ast, roots)

    def test_audit_must_be_exact_and_closed(self):
        log = 'AUTO_ADAPTER_ASSUMPTIONS_0\nClosed under the global context\n'
        self.assertTrue(scalar.audit_output(log, 1))
        for bad in (log.replace('_0', '_1'), log+'Axioms:\nX : True', ''):
            self.assertFalse(scalar.audit_output(bad, 1))
        self.assertFalse(scalar.audit_output(log, 2))

    def test_persistent_source_is_reproducible_and_never_overwritten(self):
        proposal = (self.ast, scalar.analyze(self.ast, [8]), 'checked source\n')
        with tempfile.TemporaryDirectory() as tmp, patch.object(scalar, 'proposal', return_value=proposal):
            dest = Path(tmp)/'Capture.v'
            scalar.emit_library({}, dest, [8])
            scalar.emit_library({}, dest, [8], True)
            with self.assertRaises(ValueError):
                scalar.emit_library({}, dest, [8])
            with patch.object(scalar, 'proposal', return_value=(*proposal[:2], 'different')):
                with self.assertRaises(ValueError):
                    scalar.emit_library({}, dest, [8], True)

    def test_full_process_not_root_pruned(self):
        self.ast['processes'][0] = proc('process_4',
            'SSeq [SAssign true (EVar 32 1) (LVar 32 8); SAssign true (EConst 1 1) (LVar 1 12)]')
        result = scalar.analyze(self.ast, [8])
        self.assertIn('(LVar 1 12)', adapter.render(result['analysis']['plans'][0][1]))


if __name__ == '__main__':
    unittest.main()
