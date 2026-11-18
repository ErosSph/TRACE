import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import cpu_add_admission_write as admission


class ResetCaptureTests(unittest.TestCase):
    def test_original_one_bit_reset_copy(self):
        self.assertEqual(admission.reset_copy(admission.rtl.Parser(
            '(ECond 1 (EVar 1 7) (EVar 1 8) (EConst 1 0))').complete()), (7, 8))

    def test_wrong_width_is_not_truncated_to_fit(self):
        with self.assertRaises(ValueError):
            admission.reset_copy(admission.rtl.Parser(
                '(ECond 1 (EVar 1 7) (EVar 2 8) (EConst 1 0))').complete())

    def test_wrong_reset_value_is_not_ignored(self):
        with self.assertRaises(ValueError):
            admission.reset_copy(admission.rtl.Parser(
                '(ECond 1 (EVar 1 7) (EVar 1 8) (EConst 1 1))').complete())


class EnvironmentTests(unittest.TestCase):
    def test_missing_original_receipt_rejected(self):
        with self.assertRaisesRegex(ValueError, 'receipt'):
            admission.verify_environment_paths([])

    def test_original_environment_data_must_still_match(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder)
            data = path / 'data.v'
            data.write_text('original environment')
            receipt = {str(data): hashlib.sha256(data.read_bytes()).hexdigest()}
            (path / 'plan.json').write_text(json.dumps(dict(environment=dict(input_hashes=receipt))))
            paths = [dict(directory=folder, namespace='GeneratedSeedBoot')]
            self.assertEqual(admission.verify_environment_paths(paths), receipt)
            data.write_text('changed environment')
            with self.assertRaisesRegex(ValueError, 'changed'):
                admission.verify_environment_paths(paths)


class GraphTests(unittest.TestCase):
    def setUp(self):
        body = admission.rtl.Parser('''(SSeq [
            (SAssign false (EConst 1 1) (LVar 1 7));
            (SAssign false (EConst 1 1) (LVar 1 8));
            (SIf (EVar 1 2)
              (SSeq [(SAssign false (EConst 1 0) (LVar 1 7));
                     (SAssign false (EConst 1 0) (LVar 1 8))]) SSkip)])''').complete()
        self.raw = dict(processes=[dict(name='controller', writers=[7, 8], body=body),
            dict(name='capture', events='[{| event_edge := Posedge; event_signal := 21 |}]')])
        symbols = [dict(path=str(x), width=1, coq_root=x) for x in [2, 7, 8, 20, 21, 22]]
        edges = [dict(id=0, process=0, target='7', data=['2'], address=[], guards=[], assignment='blocking'),
                 dict(id=1, process=0, target='8', data=[], address=[], guards=[dict(reads=['2'])], assignment='blocking'),
                 dict(id=2, process=1, target='20', data=['8'], address=[], guards=[dict(reads=['22'])], assignment='nonblocking')]
        self.graph = dict(symbols=symbols, edges=edges, obligations=[], processes=[dict(id=0),
            dict(id=1, timing=dict(kind='SignalEventControl', edge='EdgeKind.PosEdge',
                                  expr=dict(kind='NamedValueExpression', symbol='21'), iff=None))])
        self.plan = dict(gate=7, write=20, route=dict(terminal=8), process='controller',
            scalar=dict(root=20, width=1, process='capture',
                        next_expression='(ECond 1 (EVar 1 22) (EVar 1 8) (EConst 1 0))'))

    def check(self):
        return admission.graph_evidence(self.graph, self.raw, self.plan)

    def test_consumer_queries_both_real_outputs_and_real_capture(self):
        evidence = self.check()
        self.assertEqual([q['target'] for q in evidence['queries']], ['7', '8'])
        self.assertEqual(evidence['capture'][0]['root'], 20)
        self.assertFalse(evidence['translation_equivalence_proved'])

    def test_missing_guard_rejected(self):
        self.graph['edges'][0]['data'] = []
        self.graph['edges'][1]['guards'] = []
        with self.assertRaisesRegex(ValueError, 'dependency'):
            self.check()

    def test_wrong_width_rejected(self):
        self.graph['symbols'][0]['width'] = 2
        with self.assertRaisesRegex(ValueError, 'width'):
            self.check()

    def test_mixed_controller_process_rejected(self):
        self.graph['edges'][1]['process'] = 4
        with self.assertRaisesRegex(ValueError, 'one ordered process'):
            self.check()

    def test_nonblocking_not_reinterpreted_as_blocking(self):
        self.graph['edges'][1]['assignment'] = 'nonblocking'
        with self.assertRaisesRegex(ValueError, 'not blocking'):
            self.check()

    def test_missing_write_identity_rejected(self):
        self.raw['processes'][0]['writers'].append(9)
        with self.assertRaisesRegex(ValueError, 'identity'):
            self.check()

    def test_wrong_capture_phase_rejected(self):
        self.graph['processes'][1]['timing']['edge'] = 'EdgeKind.NegEdge'
        with self.assertRaisesRegex(ValueError, 'phase'):
            self.check()

    def test_no_read_after_write_dependency_cut(self):
        compiler = admission.observation.Compiler(1)
        body = admission.rtl.Parser('''(SSeq [
            (SAssign false (EVar 1 2) (LVar 1 3));
            (SIf (EVar 1 3) (SAssign false (EConst 1 0) (LVar 1 7)) SSkip)])''').complete()
        post = admission.rtl.Parser('(ECond 1 (EVar 1 7) (EVar 1 8) (EConst 1 1))').complete()
        result = compiler.compile(body, admission.rtl.render(post), admission.observation.inputs(post))
        self.assertIn((1, 2), result[3])
        self.assertNotIn((1, 3), result[3])
        self.assertIn((1, 8), result[3])


if __name__ == '__main__':
    unittest.main()
