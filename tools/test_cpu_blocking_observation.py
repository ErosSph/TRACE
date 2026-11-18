import unittest
import cpu_blocking_observation as c

class BlockingObservationTests(unittest.TestCase):
    def compile(self,text,width=5,root=9):
        compiler=c.Compiler(width)
        result=compiler.compile(c.rtl.Parser(text).complete(),f'(EVar {width} {root})',{(width,root)})
        return compiler,result
    def test_earlier_write_replaces_later_read(self):
        compiler,result=self.compile('(SSeq [(SAssign false (EVar 5 3) (LVar 5 7)); (SAssign false (EVar 5 7) (LVar 5 9))])')
        self.assertEqual(result[3],{(5,3)})
        self.assertIn('seq_cons','\n'.join(compiler.lines))
        self.assertIn('assignment_checked','\n'.join(compiler.lines))
        self.assertNotIn('inversion HI','\n'.join(compiler.lines))
    def test_reverse_order_retains_old_value(self):
        _,result=self.compile('(SSeq [(SAssign false (EVar 5 7) (LVar 5 9)); (SAssign false (EVar 5 3) (LVar 5 7))])')
        self.assertEqual(result[3],{(5,7)})
    def test_guard_uses_prior_write(self):
        _,result=self.compile('(SSeq [(SAssign false (EVar 1 3) (LVar 1 7)); (SIf (EVar 1 7) (SAssign false (EConst 5 1) (LVar 5 9)) (SAssign false (EConst 5 2) (LVar 5 9)))])')
        self.assertEqual(result[3],{(1,3)})
    def test_nba_not_reinterpreted(self):
        with self.assertRaises(ValueError):self.compile('(SAssign true (EVar 5 7) (LVar 5 9))')
    def test_partial_read_rejected(self):
        with self.assertRaises(ValueError):self.compile('(SAssign false (EConst 1 1) (LVar 1 9))')
    def test_case_default_order_retained(self):
        compiler,result=self.compile('(SCase (EVar 2 7) [(Some (EConst 2 0),(SAssign false (EConst 5 1) (LVar 5 9))); (None,(SAssign false (EConst 5 2) (LVar 5 9)))])')
        self.assertEqual(result[3],{(2,7)})
        self.assertIn('case_default','\n'.join(compiler.lines))
        self.assertIn('case_some','\n'.join(compiler.lines))

    def test_unread_part_select_preserves_original_assignment(self):
        compiler,result=self.compile('(SAssign false (EConst 1 0) (LSel 1 (LVar 32 8) (EConst 5 0)))')
        self.assertEqual(result[3],{(5,9)})
        self.assertIn('LSel 1 (LVar 32 8)', '\n'.join(compiler.lines))
        self.assertIn('assignment_unread_lvalue_checked', '\n'.join(compiler.lines))
    def test_observed_part_select_still_requires_certificate(self):
        with self.assertRaisesRegex(ValueError,'substitution certificate'):
            self.compile('(SAssign false (EConst 1 0) (LSel 1 (LVar 5 9) (EConst 5 0)))')
    def test_prior_partial_write_cannot_be_hidden_by_later_copy(self):
        with self.assertRaisesRegex(ValueError,'substitution certificate'):
            self.compile('(SSeq [(SAssign false (EConst 1 0) (LSel 1 (LVar 5 7) (EConst 5 0))); (SAssign false (EVar 5 7) (LVar 5 9))])')

    def test_observed_low_bit_clear_uses_exact_certificate(self):
        compiler,result=self.compile('(SAssign false (EConst 1 0) (LSel 1 (LVar 32 9) (EConst 5 0)))',width=32)
        self.assertEqual(result[3],{(32,9)})
        self.assertIn('clear_low_observation','\n'.join(compiler.lines))
        self.assertIn('LSel 1 (LVar 32 9)','\n'.join(compiler.lines))
    def test_low_bit_set_does_not_use_clear_certificate(self):
        with self.assertRaisesRegex(ValueError,'substitution certificate'):
            self.compile('(SAssign false (EConst 1 1) (LSel 1 (LVar 32 9) (EConst 5 0)))',width=32)
    def test_other_bit_clear_does_not_use_low_bit_certificate(self):
        with self.assertRaisesRegex(ValueError,'substitution certificate'):
            self.compile('(SAssign false (EConst 1 0) (LSel 1 (LVar 32 9) (EConst 5 1)))',width=32)

    def test_unrelated_if_omits_guard_but_preserves_effect(self):
        compiler,result=self.compile('(SIf (EVar 1 2) (SAssign false (EConst 5 1) (LVar 5 7)) (SSkip))')
        self.assertEqual(result[3],{(5,9)})
        self.assertIn('FIf (EVar 1 2)','\n'.join(compiler.lines))
        self.assertIn('apply branch_same','\n'.join(compiler.lines))
    def test_unrelated_case_omits_guard_but_preserves_effect(self):
        compiler,result=self.compile('(SCase (EVar 2 2) [(Some (EConst 2 1),(SAssign false (EConst 5 1) (LVar 5 7))); (None,(SSkip))])')
        self.assertEqual(result[3],{(5,9)})
        self.assertIn('apply case_some_same','\n'.join(compiler.lines))
        self.assertIn('FCase (EVar 2 2)','\n'.join(compiler.lines))
    def test_guard_kept_when_observed_branches_differ(self):
        compiler,result=self.compile('(SIf (EVar 1 2) (SAssign false (EConst 5 1) (LVar 5 9)) (SAssign false (EConst 5 2) (LVar 5 9)))')
        self.assertIn((1,2),result[3])
        self.assertNotIn('apply branch_same','\n'.join(compiler.lines))

if __name__=='__main__':unittest.main()
