import unittest
import cpu_selected_candidate_tokens as c

class Tests(unittest.TestCase):
    def e(self,s):return c.rtl.Parser(s).complete()
    def test_positive_guard_certified(self):
        e=self.e('(ECond 2 (EVar 1 9) (EConst 2 1) (EConst 2 0))')
        self.assertIsNotNone(c.certificate(e,2,1,self.e('(EVar 1 9)')))
    def test_default_does_not_imply_guard(self):
        e=self.e('(ECond 2 (EVar 1 9) (EConst 2 1) (EConst 2 1))')
        self.assertIsNone(c.certificate(e,2,1,self.e('(EVar 1 9)')))
    def test_or_does_not_require_left(self):
        self.assertIsNone(c.requirement(self.e('(EVar 1 9)'),self.e('(EBinary 1 BOr (EVar 1 9) (EVar 1 10))')))
    def test_and_requires_either_operand(self):
        self.assertIsNotNone(c.requirement(self.e('(EVar 1 9)'),self.e('(EBinary 1 BAnd (EVar 1 10) (EVar 1 9))')))
    def test_nonzero_destination_guard(self):
        self.assertIsNotNone(c.requirement(self.e('(EVar 5 9)'),self.e('(EBinary 1 BNeq (EConst 5 0) (EVar 5 9))')))
    def test_nonzero_constant_not_zero_test(self):
        self.assertIsNone(c.requirement(self.e('(EVar 5 9)'),self.e('(EBinary 1 BNeq (EConst 5 1) (EVar 5 9))')))
    def test_width_truncation_not_impossible(self):
        self.assertIsNone(c.certificate(self.e('(EConst 2 5)'),2,1,self.e('(EVar 1 9)')))
    def test_guard_constants_not_reported_as_output_codes(self):
        e=self.e('(ECond 2 (EBinary 1 BEq (EVar 2 9) (EConst 2 3)) (EConst 2 1) (EConst 2 0))')
        self.assertEqual(c.output_codes(e,2),{0,1})
    def test_selected_code_requires_matching_address_equality(self):
        eq=self.e('(EBinary 1 BEq (EVar 5 10) (EVar 5 11))')
        e=self.e('(ECond 2 (EBinary 1 BAnd (EVar 1 9) (EBinary 1 BEq (EVar 5 10) (EVar 5 11))) (EConst 2 1) (EConst 2 0))')
        self.assertIsNotNone(c.certificate(e,2,1,eq))
    def test_other_source_equality_not_invented(self):
        e=self.e('(ECond 2 (EBinary 1 BEq (EVar 5 10) (EVar 5 11)) (EConst 2 1) (EConst 2 0))')
        self.assertIsNone(c.certificate(e,2,1,self.e('(EBinary 1 BEq (EVar 5 10) (EVar 5 12))')))

if __name__=='__main__':unittest.main()
