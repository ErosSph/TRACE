"""Generator guards; native Coq evidence is recorded separately."""
import json
from pathlib import Path
import tempfile
import unittest

import cpu_addi_fetch_reference as fetch


class AddiFetchTests(unittest.TestCase):
    def setUp(self):
        self.source, _, _ = fetch.render(dict(capacity=101, offset_width=12))

    def test_immediate_is_not_a_register_or_a_success_premise(self):
        self.assertNotIn('Himm', self.source)
        self.assertNotIn('second_register_field', self.source)
        signature = fetch.declaration(self.source, 'recorded_addi_step')
        premises = signature.split('exists after,')[0]
        self.assertNotIn('FormalSpec.run1', premises)
        self.assertNotIn('0<=imm', premises)
        self.assertIn('(i<101)%nat', premises)
        self.assertIn('2^Z.of_nat 12', premises)

    def test_reuses_original_physical_fetch(self):
        self.assertIn('GeneratedFetchReference.FetchReference', self.source)
        self.assertIn('recorded_word_matches_original_memory', self.source)
        self.assertNotIn('Theorem recorded_word_matches_original_memory', self.source)

    def test_explicit_type_extraction_keeps_typed_binders(self):
        signature = fetch.declaration(self.source, 'recorded_addi_frontier')
        self.assertTrue(signature.startswith('forall token(before after:FormalSpec.State)rd rs imm,'))
        self.assertIn('Decode.Addi rd rs imm', signature)
        self.assertIn('AddiPost before after rd rs imm', signature)

    def test_rejects_another_original_configuration(self):
        config = json.loads(Path('framework/bzeeno-cdfg-addi-inputs.json').read_text())
        config['history'] = 'different-original-history'
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, 'different original'):
                fetch.check(config, str(Path(directory)/'out'))


if __name__ == '__main__':
    unittest.main()
