import unittest
from unittest.mock import patch
import cpu_write_ownership_frontier as w

class OwnershipTests(unittest.TestCase):
    def test_preserves_branch_polarity_and_order(self):
        T=w.rtl.Term
        def expr(s):return w.rtl.Parser(s).complete()
        yes=T('BPWord',(expr('EConst 10 32'),expr('EVar 32 3')))
        no=T('BPWord',(expr('EConst 10 64'),expr('EVar 32 4')))
        plan=T('BPSeq',(T('list',(T('BPIf',(expr('EVar 1 2'),yes,no)),
                                  T('BPReset',(expr('EConst 1024 0'),)))),))
        leaves=list(w.leaves(plan))
        self.assertEqual([x[0]for x in leaves],[(0,0),(0,1),(1,)])
        self.assertEqual([x[1][0][1]for x in leaves[:2]],[True,False])
        self.assertEqual(leaves[-1][2].name,'BPReset')

    def test_unknown_plan_cannot_disappear(self):
        with self.assertRaises(ValueError):list(w.leaves(w.rtl.Term('BPUnknown')))

    def test_stop_at_sampled_state_and_terminate_comb_cycle(self):
        def proc(name,kind,root,source):
            return dict(name=name,kind=kind,writers=[root],events=[],
                body=w.rtl.Parser(f'SAssign false (EVar 32 {source}) (LVar 32 {root})').complete())
        ast=dict(processes=[proc('a','Combinational',1,2),proc('b','Sequential',2,3),
                            proc('c','Combinational',4,5),proc('d','Combinational',5,4)])
        result=w.frontier(ast,[1,4,9])
        self.assertEqual(list(result['boundaries']),['2'])
        self.assertEqual(result['external_inputs'],[9])
        self.assertNotIn(3,result['external_inputs'])

    def test_address_and_data_are_not_collapsed(self):
        plan=w.rtl.Term('BPWord',(w.rtl.Parser('EVar 10 1').complete(),
                                  w.rtl.Parser('EVar 32 2').complete()))
        proc=dict(name='writer',events=[])
        with patch.object(w.bank,'analyze',return_value=dict(banks=[dict(root=8,plans=[(proc,None,plan)])],residuals=[])):
            r=w.analyze(dict(source_sha256='test',processes=[]))
        site=r['writes'][0]
        self.assertEqual(site['frontiers']['address']['external_inputs'],[1])
        self.assertEqual(site['frontiers']['data']['external_inputs'],[2])
        self.assertFalse(site['token_ownership_proved'])
        self.assertFalse(site['shared_boundary_proves_identity'])
        self.assertEqual(site['destination']['kind'],'dynamic_offset')

    def test_constant_destination_is_guard_obligation_not_missing_address(self):
        T=w.rtl.Term
        plan=T('BPWord',(w.rtl.Parser('EConst 10 96').complete(),w.rtl.Parser('EVar 32 2').complete()))
        proc=dict(name='writer',events=[])
        with patch.object(w.bank,'analyze',return_value=dict(banks=[dict(root=8,plans=[(proc,None,plan)])],residuals=[])):
            r=w.analyze(dict(source_sha256='test',processes=[]))
        self.assertEqual(r['writes'][0]['destination']['lane'],3)
        self.assertEqual(r['writes'][0]['destination']['kind'],'fixed_lane')

if __name__=='__main__':unittest.main()
