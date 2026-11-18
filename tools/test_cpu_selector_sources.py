import unittest
import cpu_selector_sources as s


class SelectorSourceTests(unittest.TestCase):
    def proc(self,name,root,body,kind='Combinational'):
        return dict(name=name,writers=[root],kind=kind,events='[]',body=s.rtl.Parser(body).complete())

    def test_stops_at_true_register(self):
        ast=dict(processes=[self.proc('copy',1,'SAssign false (EVar 5 2) (LVar 5 1)'),
            self.proc('register',2,'SAssign true (EVar 5 3) (LVar 5 2)','Sequential')])
        r=s.trace(ast,5,1)
        self.assertEqual((r['terminal'],r['kind']),(2,'sequential'))
        self.assertEqual(len(r['edges']),1)

    def test_arithmetic_is_not_a_copy(self):
        ast=dict(processes=[self.proc('add',1,'SAssign false (EBinary 5 BAdd (EVar 5 2) (EConst 5 1)) (LVar 5 1)')])
        self.assertEqual(s.trace(ast,5,1)['kind'],'computed')

    def test_cycle_not_external(self):
        ast=dict(processes=[self.proc('a',1,'SAssign false (EVar 5 2) (LVar 5 1)'),
            self.proc('b',2,'SAssign false (EVar 5 1) (LVar 5 2)')])
        self.assertEqual(s.trace(ast,5,1)['kind'],'cycle')

    def test_width_change_not_identity(self):
        ast=dict(processes=[self.proc('a',1,'SAssign false (EVar 6 2) (LVar 5 1)')])
        self.assertEqual(s.trace(ast,5,1)['kind'],'computed')


if __name__=='__main__':unittest.main()
