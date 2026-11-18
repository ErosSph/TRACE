import unittest
from unittest.mock import patch
import cpu_write_destination_history as h


class WriteHistoryTests(unittest.TestCase):
    def fixture(self, offset=7):
        graph=dict(rows=[dict(root=10),dict(root=20)],
                   edges=[dict(target=1,source=0)],
                   head=dict(source=3,expression=f'(ESel 5 (EVar 32 3) (EConst 5 {offset}))'))
        writes=[dict(process='write',offset='(EBinary 12 BMul (EVar 5 20) (EConst 12 32))')]
        return graph,writes

    def discover(self, graph,writes):
        with patch.object(h.chain,'discover',return_value=graph), \
             patch.object(h.index.ownership,'analyze',return_value=dict(writes=writes)):
            return h.discover(dict(processes=[]))

    def test_transitive_predecessors_are_selected(self):
        rows,res=self.discover(*self.fixture())
        self.assertEqual(rows[0]['roots'],[10,20]);self.assertEqual(res,[])

    def test_rs1_chain_is_not_rd(self):
        rows,res=self.discover(*self.fixture(offset=15))
        self.assertEqual(rows,[]);self.assertTrue(res)

    def test_missing_history_not_invented(self):
        graph,writes=self.fixture();graph['rows']=[];graph['edges']=[]
        rows,res=self.discover(graph,writes)
        self.assertEqual(rows,[]);self.assertTrue(res)

    def test_no_head_is_residual(self):
        graph,writes=self.fixture();graph['head']=None
        rows,res=self.discover(graph,writes)
        self.assertEqual(rows,[]);self.assertTrue(res)

    def test_fixed_lane_requires_enable_proof(self):
        graph,writes=self.fixture();writes[0]['offset']='(EConst 10 32)'
        rows,res=self.discover(graph,writes)
        self.assertEqual(rows,[])
        self.assertIn('enable decoding',res[0]['reason'])

    def test_reset_not_silently_accepted(self):
        graph,writes=self.fixture();writes[0]['offset']=None
        rows,res=self.discover(graph,writes)
        self.assertEqual(rows,[])
        self.assertIn('reset proof',res[0]['reason'])

    def test_distinct_alias_routes_are_not_merged(self):
        graph,writes=self.fixture()
        writes.append(dict(process='other_write',offset='(EBinary 12 BMul (EVar 5 30) (EConst 12 32))'))
        proc=dict(writers=[30],kind='Combinational',
                  body=h.index.rtl.Parser('(SAssign false (EVar 5 20) (LVar 5 30))').complete())
        with patch.object(h.chain,'discover',return_value=graph), \
             patch.object(h.index.ownership,'analyze',return_value=dict(writes=writes)):
            rows,_=h.discover(dict(processes=[proc]))
        self.assertEqual(len(rows),2)
        self.assertEqual({tuple(r['aliases']) for r in rows},{(),(30,)})


if __name__=='__main__':unittest.main()
