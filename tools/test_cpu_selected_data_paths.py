import unittest
import cpu_selected_data_paths as c

class Tests(unittest.TestCase):
    def e(self,s):return c.rtl.Parser(s).complete()
    def mux(self,key=1):return self.e(f'(ECond 32 (EBinary 1 BEq (EVar 2 9) (EConst 2 {key})) (EVar 32 10) (EVar 32 11))')
    def test_selected_leaf(self):
        leaf,proof=c.select(self.mux(),32,2,9,1)
        self.assertEqual(leaf,self.e('(EVar 32 10)'));self.assertIn('Yes',proof)
    def test_default_leaf(self):
        leaf,proof=c.select(self.mux(),32,2,9,2)
        self.assertEqual(leaf,self.e('(EVar 32 11)'));self.assertIn('No',proof)
    def test_truncated_case_key(self):
        self.assertEqual(c.select(self.mux(5),32,2,9,1)[0],self.e('(EVar 32 10)'))
    def test_priority_preserved(self):
        e=self.e('(ECond 32 (EBinary 1 BEq (EVar 2 9) (EConst 2 1)) (EVar 32 10) (ECond 32 (EBinary 1 BEq (EVar 2 9) (EConst 2 1)) (EVar 32 12) (EVar 32 11)))')
        self.assertEqual(c.select(e,32,2,9,1)[0],self.e('(EVar 32 10)'))
    def test_other_selector_rejected(self):
        with self.assertRaises(ValueError):c.select(self.mux(),32,2,8,1)
    def test_width_change_rejected(self):
        with self.assertRaises(ValueError):c.select(self.mux(),32,3,9,1)
    def test_retained_output_not_reported_as_forward_source(self):
        body=self.e('(SCase (EVar 2 9) [(Some (EConst 2 1), SAssign false (EVar 32 11) (LVar 32 10))])')
        ast=dict(processes=[dict(name='mux',kind='Combinational',body=body,writers=[10],events=[])])
        with self.assertRaises(ValueError):c.discover(ast,[dict(selector=dict(root=9,width=2),code=0)])

if __name__=='__main__':unittest.main()
