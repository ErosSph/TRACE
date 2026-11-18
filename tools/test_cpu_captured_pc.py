import unittest
import cpu_captured_pc as c

class CapturedPCTests(unittest.TestCase):
    def parse(self,x):return c.rtl.Parser(x).complete()
    def rule(self,w,v,p):
        return c.match(self.parse(w),self.parse(v),self.parse(p),10,11,
                       dict(word_input=20,pc_input=21,address_root=22))
    def test_hold_requires_pc_hold(self):
        self.assertEqual(self.rule('(EVar 32 10)','(EVar 1 12)','(EVar 32 11)'),'apply Hold.')
        self.assertIsNone(self.rule('(EVar 32 10)','(EVar 1 12)','(EVar 32 21)'))
    def test_fresh_requires_checked_companion(self):
        self.assertIn('fetch_pair_0_sampled_pc',self.rule('(EVar 32 20)','(EConst 1 1)','(EVar 32 21)'))
        self.assertIsNone(self.rule('(EVar 32 20)','(EConst 1 1)','(EVar 32 23)'))
    def test_invalid_slot_has_no_pc_obligation(self):
        self.assertEqual(self.rule('(EConst 32 0)','(EConst 1 0)','(EConst 32 7)'),'apply Invalid.')
    def test_guards_must_match(self):
        self.assertIsNone(self.rule('(ECond 32 (EVar 1 1) (EVar 32 20) (EVar 32 10))',
            '(ECond 1 (EVar 1 2) (EConst 1 1) (EVar 1 12))',
            '(ECond 32 (EVar 1 1) (EVar 32 21) (EVar 32 11))'))

if __name__=='__main__':unittest.main()
