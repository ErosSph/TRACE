import unittest,json
from unittest.mock import patch
import cpu_r_validity_strategy as s


class ValidityStrategyTests(unittest.TestCase):
    def test_saved_choice_requires_identical_current_request(self):
        slots={'carrier_29':[dict(id='derive_inactive_encoding_predicate')]};facts=[]
        answer={'carrier_29':'derive_inactive_encoding_predicate'}
        report=dict(llm=dict(status='accepted_unproved',bindings=answer),proposals=answer)
        raw=json.dumps(s.llm.prompt(slots,facts,'capture_validity')).encode()
        with patch.object(s.Path,'read_text',return_value=json.dumps(report)),patch.object(s.Path,'read_bytes',return_value=raw):
            audit,result=s.reuse_proposal('report.json',slots,facts)
            self.assertEqual(result,answer);self.assertEqual(audit['new_attempts'],0)
            with self.assertRaises(ValueError):s.reuse_proposal('report.json',slots,[dict(changed=True)])

    def test_checked_prerequisite_does_not_become_architectural_proof(self):
        import cpu_synchronized_values as synchronized
        import cpu_zero_instruction_rf as zero_rf
        with patch.object(synchronized,'check',return_value=dict(accepted=True,coupled_pairs=[dict(carrier=29,target=30)]))as check, \
             patch.object(zero_rf,'check',return_value=dict(accepted=True,rows=[dict(word=29)])):
            result=s.apply_proposals('raw.v','Raw','unused',{'carrier_27':'derive_inactive_encoding_predicate','carrier_29':'derive_inactive_encoding_predicate'})
        check.assert_called_once()
        self.assertTrue(result[0]['local_certificate_accepted'])
        self.assertFalse(result[0]['architectural_obligation_closed'])
        self.assertEqual(result[0]['covered_roles'],['carrier_29'])
        self.assertEqual(result[0]['uncovered_roles'],['carrier_27'])
        self.assertEqual(result[0]['rf_effect_covered_roles'],['carrier_29'])
        self.assertFalse(result[0]['architectural_obligation_closed'])

    def test_metadata_uses_raw_failure_obligations_not_old_inv(self):
        gap=dict(root=8,gap=dict(reason='different_guard_structure',path=[]))
        with patch.object(s.coverage,'discover',return_value=dict(unresolved_fields=[8],coverage_gaps=[gap,gap])):
            slots,facts=s.metadata_proposal({})
        self.assertEqual(set(slots),{'metadata_8'})
        self.assertEqual(facts[0]['candidate_failure_count'],2)
        self.assertEqual(len(facts[0]['representative_failures']),1)
        self.assertIn('neither reachability',facts[0]['scope'])

    def test_no_residual_no_proposal(self):
        with patch.object(s.validity,'discover',return_value=dict(residuals=[])), \
             patch.object(s.validity.origins.pending,'analyze',return_value=dict(slots=[])):
            self.assertEqual(s.proposal(dict(processes=[])),({},[]))

    def test_unknown_strategy_or_added_assumption_rejected(self):
        slots={'carrier':[dict(id='derive_control_history_validity')]}
        with self.assertRaises(ValueError):
            s.llm.validate(dict(bindings=dict(carrier='assume_valid')),slots)
        with self.assertRaises(ValueError):
            s.llm.validate(dict(bindings=dict(carrier='derive_control_history_validity'),axiom='valid'),slots)
        prompt=s.llm.prompt(slots,[],'capture_validity')
        self.assertIn('NOT a proof',prompt['requirement'])


if __name__=='__main__':unittest.main()
