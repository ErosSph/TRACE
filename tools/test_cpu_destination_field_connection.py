import unittest
from unittest.mock import patch
import cpu_destination_field_connection as f


class DestinationFieldTests(unittest.TestCase):
    def fixture(self, kind='Combinational', field='Rd'):
        return dict(name='field7', root=44, source=29, width=5,
                    field=field, kind=kind, original='actual_expression', base='captured_phase')

    def render(self, row):
        selected = dict(Sequential=[44] if row['kind']=='Sequential' else [])
        with patch.object(f.inputs.fields, 'discover', return_value=selected), \
             patch.object(f.inputs.fields.paths.expressions, 'proposal',
                          return_value=(None,None,[dict(root=44,process='capture')],None,None)):
            return f.render(dict(module='Raw'),dict(ast=dict(program='Raw.p')),[row])

    def test_real_fixed_point_and_normalized_token_premises_remain(self):
        source, rows = self.render(self.fixture())
        self.assertEqual(len(rows),1)
        self.assertIn('CombLFP Raw.p seed fixed',source)
        self.assertIn('PathHolds fixed actual_expression field7_choices',source)
        self.assertIn('norm 32(read_signal fixed 29)=norm 32 code',source)
        self.assertIn('destination_registers instruction=address::rest',source)
        self.assertIn('original_destination_address',source)

    def test_sequential_sampling_and_trigger_not_removed(self):
        source, _ = self.render(self.fixture('Sequential'))
        self.assertIn('changed_signal ev<>44%nat',source)
        self.assertIn('process_matches_states pre (phase_driven_state Raw.p ev pre) Raw.capture=true',source)
        self.assertIn('norm 5(read_signal (PhaseSemantics Raw.p ev pre) 44)=address',source)

    def test_source_field_cannot_be_mislabeled_as_destination(self):
        _, rows = self.render(self.fixture(field='Rs1'))
        self.assertEqual(rows,[])

    def test_tagged_field_keeps_six_bits_and_uses_checked_carrier(self):
        row=self.fixture('TaggedCombinational')
        row['width']=6
        source, rows=self.render(row)
        self.assertEqual(len(rows),1)
        self.assertIn('root_44_actual_carrier seed fixed HL',source)
        self.assertIn('norm 6(read_signal fixed 44)=address',source)
        self.assertNotIn('norm 5(read_signal fixed 44)',source)


if __name__ == '__main__': unittest.main()
