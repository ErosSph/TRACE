import unittest
import cpu_bank_index_certificate as b


class BankIndexTests(unittest.TestCase):
    def test_dynamic_index_preserves_signal(self):
        row=b.recognize('(EBinary 12 BMul (EVar 5 255) (EConst 12 32))')
        self.assertEqual(row,dict(index='(EVar 5 255)',rule='multiply_index'))

    def test_aligned_but_truncated_offset_is_rejected(self):
        self.assertIsNone(b.recognize('(EBinary 9 BMul (EVar 5 255) (EConst 12 32))'))

    def test_normalized_scale_not_source_spelling(self):
        self.assertIsNone(b.recognize('(EBinary 12 BMul (EVar 5 255) (EConst 5 32))'))

    def test_shift_index_and_wrong_shift(self):
        expr='(ESel 10 (EBinary 32 BShiftL (EExtend 32 false (EVar 5 314)) (EConst 32 5)) (EConst 32 0))'
        self.assertEqual(b.recognize(expr)['index'],'(EVar 5 314)')
        self.assertIsNone(b.recognize(expr.replace('(EConst 32 5)','(EConst 32 4)')))

    def test_constant_index_normalized(self):
        self.assertEqual(b.recognize('(EConst 10 1056)')['index'],'(EConst 5 1)')
        self.assertIsNone(b.recognize('(EConst 10 33)'))


if __name__=='__main__':unittest.main()
