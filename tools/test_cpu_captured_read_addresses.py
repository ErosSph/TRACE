import unittest
import cpu_captured_read_addresses as c
class Tests(unittest.TestCase):
    def row(self,e,source=7,width=5):return dict(root=9,width=width,source=source,expanded=e)
    def test_identity_extensions_preserve_rs1(self):
        rows=c.classify([self.row('(EExtend 5 false (ESel 5 (EExtend 32 false (EVar 32 7)) (EConst 5 15)))')],7)
        self.assertEqual(rows[0]['field'],'Rs1')
    def test_rs2(self):
        self.assertEqual(c.classify([self.row('(ESel 5 (EVar 32 7) (EConst 5 20))')],7)[0]['field'],'Rs2')
    def test_other_instruction_source_rejected(self):
        with self.assertRaises(ValueError):c.classify([self.row('(ESel 5 (EVar 32 8) (EConst 5 15))',8)],7)
    def test_signed_extension_not_erased(self):
        with self.assertRaises(ValueError):c.classify([self.row('(EExtend 5 true (ESel 5 (EVar 32 7) (EConst 5 15)))')],7)
    def test_narrowing_not_erased(self):
        with self.assertRaises(ValueError):c.classify([self.row('(EExtend 5 false (ESel 6 (EVar 32 7) (EConst 5 15)))')],7)
    def test_rd_is_not_source_address(self):
        with self.assertRaises(ValueError):c.classify([self.row('(ESel 5 (EVar 32 7) (EConst 5 7))')],7)
    def port(self,shift=5,zero=0):
        rhs=c.rtl.Parser(f'(ECond 32 (EBinary 1 BEq (EConst 5 0) (EVar 5 9)) (EConst 32 {zero}) (ESel 32 (EVar 1024 15) (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (EVar 5 9)) (EConst 32 {shift})) (EConst 32 0))))').complete()
        return dict(residuals=[],ports=[dict(rhs=rhs,width=32,output_root=16)])
    def test_value_port_matches_exact_guard_and_bank(self):
        rows=c.match_read_ports(self.port(),[dict(root=9,field='Rs1')])
        self.assertEqual(rows,[dict(port=0,output=16,address=9,bank=15,total=1024,field='Rs1')])
    def test_nonzero_x0_output_rejected(self):
        with self.assertRaises(ValueError):c.match_read_ports(self.port(zero=1),[dict(root=9,field='Rs1')])
    def test_wrong_lane_scale_rejected(self):
        with self.assertRaises(ValueError):c.match_read_ports(self.port(shift=4),[dict(root=9,field='Rs1')])
    def test_unresolved_port_is_not_silently_dropped(self):
        analysis=self.port();analysis['residuals']=['unsupported']
        with self.assertRaises(ValueError):c.match_read_ports(analysis,[dict(root=9,field='Rs1')])
    def test_value_export_uses_actual_validity_and_one_token(self):
        ports=c.match_read_ports(self.port(),[dict(root=9,field='Rs1')])
        text=c.render_values('Actual.program',ports,42)
        self.assertIn('norm 1(read_signal pre 42)<>0%Z ->exists token,',text)
        self.assertIn('destruct(valid_sampled_read_addresses image events ev HE HEv HV)',text)
        self.assertIn('read_signal pre 15',text)
        self.assertIn('Print Assumptions valid_sampled_read_values.',text)
if __name__=='__main__':unittest.main()
