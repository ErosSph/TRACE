import unittest
import cpu_invalid_capture_projection as r


class InvalidProjectionTests(unittest.TestCase):
    def check(self,word,valid,field='Rd'):
        return r.proof(r.rtl.Parser(word).complete(),r.rtl.Parser(valid).complete(),10,11,field)

    def test_nonzero_nop_has_zero_rd(self):
        self.assertIsNotNone(self.check('(EConst 32 28691)','(EConst 1 0)'))

    def test_nonzero_rd_in_invalid_slot_rejected(self):
        self.assertIsNone(self.check('(EConst 32 128)','(EConst 1 0)'))

    def test_live_slot_does_not_constrain_payload(self):
        self.assertIsNotNone(self.check('(EVar 32 99)','(EConst 1 1)'))

    def test_hold_requires_matching_valid_root(self):
        self.assertIsNotNone(self.check('(EVar 32 10)','(EVar 1 11)'))
        self.assertIsNone(self.check('(EVar 32 10)','(EVar 1 12)'))

    def test_unknown_invalid_capture_rejected(self):
        self.assertIsNone(self.check('(EVar 32 99)','(EConst 1 0)'))

    def test_matching_branches_only(self):
        word='(ECond 32 (EVar 1 2) (EVar 32 10) (EConst 32 28691))'
        self.assertIsNotNone(self.check(word,'(ECond 1 (EVar 1 2) (EVar 1 11) (EConst 1 0))'))
        self.assertIsNone(self.check(word,'(ECond 1 (EVar 1 3) (EVar 1 11) (EConst 1 0))'))

    def test_constant_is_width_normalized(self):
        self.assertIsNotNone(self.check('(EConst 32 4294967315)','(EConst 1 0)'))


if __name__=='__main__':unittest.main()
