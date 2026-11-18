import unittest
from unittest.mock import patch
import cpu_field_selector_origin as c

class FieldSelectorTests(unittest.TestCase):
    def test_discovery_keeps_constant_source_and_does_not_parse_route_as_rtl(self):
        expr=c.chain.p.rtl.Parser('(ECond 5 (EVar 1 7) (EVar 5 12) (EConst 5 0))').complete()
        ast={'processes':[{'name':'mux','kind':'Combinational','writers':[9]}]}
        with patch.object(c.chain.p,'discover_narrow_fields',return_value={'projections':[{'source':9}]}),patch.object(c.selector,'proposal',return_value=(None,None,5,[7,12],expr)):
            plan=c.discover(ast,projected=True)
        self.assertEqual(len(plan['selectors']),1);self.assertEqual(plan['residuals'],[])
        self.assertEqual(plan['selectors'][0]['literal_sources'],['(Literal 5 0)'])
        self.assertEqual(plan['selectors'][0]['sources'],[12])
    def test_exhaustive_bit_case_removes_only_default(self):
        e=c.chain.p.rtl.Parser('(ECond 5 (EBinary 1 BEq (EVar 1 9) (EConst 1 1)) (EVar 5 12) (ECond 5 (EBinary 1 BEq (EVar 1 9) (EConst 1 0)) (EVar 5 13) (EVar 5 99)))').complete()
        reduced,changed=c.reduce_bit_case(e)
        self.assertTrue(changed)
        self.assertEqual(c.chain.p.rtl.render(reduced),'(ECond 5 (EVar 1 9) (EVar 5 12) (EVar 5 13))')
        for wrong in [c.chain.p.rtl.render(e).replace('EVar 1 9','EVar 2 9'),c.chain.p.rtl.render(e).replace('(EConst 1 0)','(EConst 1 1)')]:
            self.assertFalse(c.reduce_bit_case(c.chain.p.rtl.Parser(wrong).complete())[1])
    def test_projected_source_keeps_width_and_expression(self):
        e=c.chain.p.rtl.Parser('(ESel 5 (EVar 32 838) (EConst 5 5))').complete()
        tree,proof,sources=c.route(e,5,projected=True)
        self.assertIn('Project 32 838',tree);self.assertIn('(EConst 5 5)',tree)
        self.assertIn('MatchProject',proof);self.assertEqual(sources,[838])
    def test_projected_constant_is_not_a_token(self):
        tree,proof,sources=c.route(c.chain.p.rtl.Parser('(EConst 5 0)').complete(),5,projected=True)
        self.assertEqual(tree,'(Literal 5 0)');self.assertEqual(sources,[])
        self.assertNotIn('Project',tree);self.assertNotIn('None',tree)
    def test_multiple_source_computation_is_not_one_source(self):
        e=c.chain.p.rtl.Parser('(EBinary 5 BAdd (EVar 5 1) (EVar 5 2))').complete()
        with self.assertRaises(ValueError):c.route(e,5,projected=True)
    def test_guard_and_all_sources_preserved(self):
        e=c.chain.p.rtl.Parser('(ECond 5 (EVar 1 7) (EVar 5 12) (EVar 5 13))').complete()
        route,proof,sources=c.route(e,5)
        self.assertEqual(sources,[12,13]);self.assertIn('(EVar 1 7)',route)
        self.assertEqual(proof.count('MatchSource'),2)
    def test_constant_branch_is_not_missing_token(self):
        e=c.chain.p.rtl.Parser('(ECond 5 (EVar 1 7) (EVar 5 12) (EConst 5 0))').complete()
        with self.assertRaises(ValueError):c.route(e,5)
    def test_wrong_width_rejected(self):
        with self.assertRaises(ValueError):c.route(c.chain.p.rtl.Parser('(EVar 32 12)').complete(),5)

if __name__=='__main__':unittest.main()
