import unittest
import cpu_result_cone as c

class Tests(unittest.TestCase):
    def proc(self,name,root,expr,kind='Combinational'):
        return dict(name=name,writers=[root],kind=kind,body=c.rtl.Parser(f'(SAssign false {expr} (LVar 32 {root}))').complete())
    def test_stops_at_registers(self):
        p=[self.proc('add',2,'(EBinary 32 BAdd (EVar 32 1) (EConst 32 4))'),self.proc('reg',1,'(EVar 32 0)','Sequential')]
        r=c.cone(dict(processes=p),32,2)
        self.assertEqual([x['root']for x in r['nodes']],[2]);self.assertEqual(r['boundaries'][0]['root'],1)
    def test_dependency_order(self):
        p=[self.proc('out',3,'(EVar 32 2)'),self.proc('add',2,'(EBinary 32 BAdd (EVar 32 1) (EConst 32 4))')]
        self.assertEqual([x['root']for x in c.cone(dict(processes=p),32,3)['nodes']],[2,3])
    def test_control_and_both_branches_preserved(self):
        p=[self.proc('mux',4,'(ECond 32 (EVar 1 0) (EVar 32 1) (EVar 32 2))')]
        r=c.cone(dict(processes=p),32,4)
        self.assertEqual({x['root']for x in r['boundaries']},{0,1,2})
    def test_cycle_rejected(self):
        p=[self.proc('a',1,'(EVar 32 2)'),self.proc('b',2,'(EVar 32 1)')]
        with self.assertRaises(ValueError):c.cone(dict(processes=p),32,1)
    def test_width_mismatch_rejected(self):
        with self.assertRaises(ValueError):c.cone(dict(processes=[self.proc('a',1,'(EConst 32 0)')]),5,1)
    def test_ambiguous_writers_not_selected(self):
        p=[self.proc('a',1,'(EConst 32 0)'),self.proc('b',1,'(EConst 32 1)')]
        r=c.cone(dict(processes=p),32,1)
        self.assertFalse(r['nodes']);self.assertEqual(r['boundaries'][0]['reason'],'external_or_ambiguous')
    def test_unwritten_is_distinct_from_ambiguous(self):
        r=c.cone(dict(processes=[]),1,0)
        self.assertEqual(r['boundaries'],[dict(width=1,root=0,reason='external_or_unresolved')])
    def test_multioutput_control_slice(self):
        p=dict(name='decode',kind='Combinational',writers=[4,5],body=c.rtl.Parser('(SSeq [(SAssign false (EConst 32 9) (LVar 32 5)); (SIf (EVar 1 0) (SAssign false (EConst 32 1) (LVar 32 4)) (SAssign false (EConst 32 2) (LVar 32 4)))])').complete())
        r=c.cone(dict(processes=[p]),32,4)
        self.assertEqual(r['nodes'][0]['kind'],'blocking_slice')
        self.assertEqual({b['root']for b in r['boundaries']},{0})
    def test_blocking_local_dependency_not_ignored(self):
        p=dict(name='decode',kind='Combinational',writers=[4,5],body=c.rtl.Parser('(SSeq [(SAssign false (EConst 32 9) (LVar 32 5)); (SAssign false (EVar 32 5) (LVar 32 4))])').complete())
        r=c.cone(dict(processes=[p]),32,4)
        self.assertFalse(r['nodes']);self.assertEqual(r['boundaries'][0]['reason'],'unsupported_process')

if __name__=='__main__':unittest.main()
