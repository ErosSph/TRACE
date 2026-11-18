import unittest
import cpu_comb_residual_diagnostics as diagnostic
import cpu_auto_adapter as adapter


class ResidualDiagnosticsTests(unittest.TestCase):
    def test_optional_checked_catalog_is_explicit_and_cpu_independent(self):
        from unittest.mock import patch
        text=('Require Import Ex.External.CPUCombRuleCatalog.\n'
            'Import ExtendedSVCombRuleRegistry CPUCombRuleCatalog.\n'
            'Definition checked := certified_order producer_rules order.\n'
            'Local Opaque actual_order certified_order residual_order.\n')
        profile={'ast':{'program':'Renamed.actual'}}
        with patch.object(diagnostic.registry,'proposal',return_value=({},text,2)):
            _,base,_=diagnostic.proposal(profile)
            _,extended,_=diagnostic.proposal(profile,True)
            self.assertNotIn('CPUCombNBAExtendedCatalog',base)
            self.assertIn('CPUCombNBAExtendedCatalog',extended)
            self.assertIn('producer_rules_with_nba order',extended)
            self.assertIn('processes Renamed.actual',extended)
            with self.assertRaises(ValueError):
                diagnostic.proposal(profile,'yes')

    def test_empty_and_multiline_indices(self):
        self.assertEqual(diagnostic.parse_indices('REGISTRY_RESIDUAL_INDICES []\n'),[])
        self.assertEqual(diagnostic.parse_indices('REGISTRY_RESIDUAL_INDICES [2;\n 9]\n'),[2,9])

    def test_reject_ambiguous_unsorted_and_nonliteral(self):
        for value in ('[2;2]','[9;2]','[f 3]'):
            with self.assertRaises(ValueError):
                diagnostic.parse_indices('REGISTRY_RESIDUAL_INDICES '+value+'\n')
        with self.assertRaises(ValueError):
            diagnostic.parse_indices('REGISTRY_RESIDUAL_INDICES []\nREGISTRY_RESIDUAL_INDICES []\n')

    def test_actual_nba_candidate_is_not_claimed_proved(self):
        T=adapter.Term
        body=T('SAssign',(T('true'),T('EVar',(T('32'),T('7'))),T('LVar',(T('32'),T('8')))))
        ast={'processes':[{'name':'renamed','kind':'Combinational','body':body}]}
        row=diagnostic.describe(ast,[0])[0]
        self.assertEqual(row['candidate_family'],'output-independent-nonblocking')
        self.assertFalse(row['producer_idempotence_proved'])
        self.assertEqual(row['syntactic_expression_reads'],[7])

    def test_no_architecture_inference_from_self_read(self):
        T=adapter.Term
        body=T('SAssign',(T('false'),T('EVar',(T('1'),T('8'))),T('LVar',(T('1'),T('8')))))
        ast={'processes':[{'name':'other','kind':'Combinational','body':body}]}
        self.assertEqual(diagnostic.describe(ast,[0])[0]['syntactic_read_write_overlap'],[8])
        with self.assertRaises(ValueError):
            diagnostic.describe(ast,[1])


if __name__=='__main__':
    unittest.main()
