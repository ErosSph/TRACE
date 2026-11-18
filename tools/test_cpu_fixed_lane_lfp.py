"""Check generated connections retain the real fixed point and full address."""
import unittest
import cpu_fixed_lane_lfp as f


class FixedLaneLFPTests(unittest.TestCase):
    def fixture(self):
        ast = dict(module='Raw', processes=[
            dict(name='clocked', kind='Sequential'),
            dict(name='before', kind='Combinational'),
            dict(name='decoder', kind='Combinational'),
            dict(name='after', kind='Combinational')])
        profile = dict(ast=dict(module='Ex.Raw', program='Raw.p'))
        row = dict(address='(EVar 6 904)', process='decoder', root=906, lane=1)
        return ast, profile, row

    def test_real_order_and_slice_frame(self):
        ast, profile, row = self.fixture()
        text = f.render(ast, profile, [row])
        self.assertIn('nth_error combs 1=Some Raw.decoder', text)
        self.assertIn('slice_frameb 906%nat 1%Z 1%Z)(skipn 2 combs)', text)
        self.assertIn('CombLFP Raw.p seed fixed', text)
        self.assertIn('actual_lfp_slice_output', text)
        self.assertIn('actual_lfp_pivot_input', text)
        self.assertIn('ltac:(clear;lia) ltac:(clear;lia)', text)
        self.assertIn('Print Assumptions lane_0_actual_lfp.', text)

    def test_full_address_not_truncated_to_five_bits(self):
        ast, profile, row = self.fixture()
        text = f.render(ast, profile, [row])
        self.assertIn('norm 6(read_signal fixed 904)=norm 6 1', text)
        self.assertIn('roots_unwrittenb 904%nat', text)
        self.assertNotIn('norm 5(read_signal fixed 904)', text)

    def test_computed_address_requires_new_stability_rule(self):
        ast, profile, row = self.fixture()
        row['address'] = '(EBinary 6 BAdd (EVar 6 904) (EConst 6 1))'
        with self.assertRaisesRegex(ValueError, 'full scalar address'):
            f.render(ast, profile, [row])


if __name__ == '__main__':
    unittest.main()
