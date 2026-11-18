import unittest
import cpu_nonzero_capture as n


class NonzeroCaptureTests(unittest.TestCase):
    def parse(self,text):return n.rtl.Parser(text).complete()
    def test_hold_capture_and_zero_preserve_guard_structure(self):
        proof=n.shape(self.parse('ECond 32 (EVar 1 4) (EVar 32 8) (EConst 32 0)'))
        self.assertIn('CopyChoice',proof)
        self.assertIn('CopyLeaf',proof)
        self.assertIn('ZeroLeaf',proof)
    def test_nonzero_constant_is_not_classified_as_zero_bubble(self):
        with self.assertRaises(ValueError):n.shape(self.parse('EConst 32 19'))
    def test_wrong_width_and_arithmetic_are_not_identity_copies(self):
        for expression in ['EVar 16 8','EBinary 32 BAdd (EVar 32 8) (EConst 32 4)']:
            with self.assertRaises(ValueError):n.shape(self.parse(expression))


if __name__=='__main__':unittest.main()
