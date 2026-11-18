import unittest
import copy
import cpu_result_companions as c

class Tests(unittest.TestCase):
    def e(self,s):return c.rtl.Parser(s).complete()
    def r(self,s):return c.companion.RecipeParser(s).complete()
    def test_computed_capture(self):
        e=self.e('(EBinary 8 BAdd (EVar 8 1) (EConst 8 2))')
        self.assertEqual(c.match(e,self.r('Capture'),8,4)[0],[e])
    def test_same_guard(self):
        e=self.e('(ECond 8 (EVar 1 3) (EVar 8 1) (EVar 8 4))')
        self.assertIsNotNone(c.match(e,self.r('(Select (EVar 1 3) Capture Hold)'),8,4))
    def test_changed_guard_rejected(self):
        e=self.e('(ECond 8 (EVar 1 3) (EVar 8 1) (EVar 8 4))')
        self.assertIsNone(c.match(e,self.r('(Select (EVar 1 5) Capture Hold)'),8,4))
    def test_hold_width_rejected(self):
        self.assertIsNone(c.match(self.e('(EVar 32 4)'),self.r('Hold'),8,4))
    def test_hold_other_register_rejected(self):
        self.assertIsNone(c.match(self.e('(EVar 8 5)'),self.r('Hold'),8,4))
    def test_reset_unknown_not_capture(self):
        m=c.match(self.e('(ECond 8 (EVar 1 3) (EVar 8 1) (EConst 8 0))'),self.r('(Select (EVar 1 3) Capture Unknown)'),8,4)
        self.assertEqual(m[0],[self.e('(EVar 8 1)')])
    def test_distinct_capture_leaves_remain_distinct(self):
        m=c.match(self.e('(ECond 8 (EVar 1 3) (EVar 8 1) (EVar 8 2))'),self.r('(Select (EVar 1 3) Capture Capture)'),8,4)
        self.assertEqual(len(set(m[0])),2)

class CaptureGraphTests(unittest.TestCase):
    def setUp(self):
        self.graph=dict(symbols=[dict(path='q',width=32,coq_root=4),dict(path='d',width=32,coq_root=1),
            dict(path='clk',width=1,coq_root=2),dict(path='reset',width=1,coq_root=3)],
            edges=[dict(id=0,process=0,target='q',data=['d'],address=[],guards=[dict(reads=['reset'])],assignment='nonblocking')],
            processes=[dict(id=0,timing=dict(kind='SignalEventControl',edge='EdgeKind.PosEdge',
                expr=dict(kind='NamedValueExpression',symbol='clk'),iff=None))])
        self.raw=dict(processes=[dict(name='process_0',events='[{| event_edge := Posedge; event_signal := 2 |}]')])
        self.rows=[dict(root=4,width=32,process='process_0',recipe='Capture',
            next_expression='(ECond 32 (EVar 1 3) (EVar 32 1) (EConst 32 0))')]
    def test_accept(self):self.assertEqual(c.capture_graph_evidence(self.graph,self.raw,self.rows)[0]['root'],4)
    def test_missing_guard(self):
        self.graph['edges'][0]['guards']=[]
        with self.assertRaises(ValueError):c.capture_graph_evidence(self.graph,self.raw,self.rows)
    def test_wrong_edge(self):
        self.graph['processes'][0]['timing']['edge']='EdgeKind.NegEdge'
        with self.assertRaises(ValueError):c.capture_graph_evidence(self.graph,self.raw,self.rows)
    def test_blocking_not_nba(self):
        self.graph['edges'][0]['assignment']='blocking'
        with self.assertRaises(ValueError):c.capture_graph_evidence(self.graph,self.raw,self.rows)
    def test_duplicate_writer(self):
        other=copy.deepcopy(self.graph['edges'][0]);other['process']=1;self.graph['edges'].append(other)
        with self.assertRaises(ValueError):c.capture_graph_evidence(self.graph,self.raw,self.rows)

if __name__=='__main__':unittest.main()
