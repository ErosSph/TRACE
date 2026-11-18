import json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import cpu_phase_from_known as phase

def profile():
    return {'ast':{'module':'Renamed.AST','program':'OriginalRuntime.p',
        'program_imports':['Original.Runtime']}}

class PhaseFromKnownTests(unittest.TestCase):
    def test_symbolic_original_phase_preserves_program_and_budget(self):
        text=phase.phase_source(profile())
        self.assertIn('Original.Runtime.',text)
        self.assertIn('original_positive_phase OriginalRuntime.p',text)
        self.assertIn('Complete.all_original_producers',text)
        self.assertIn('ordered_from_checked_transports OriginalRuntime.p transport_rules',text)
        self.assertIn('transport_orderb transport_rules',phase.eligibility_source(profile()))
        self.assertIn('PhaseIndependentAt OriginalRuntime.p ev pre',text)
        self.assertNotIn('lfp_fuel:=1',text)
        self.assertNotIn('Admitted',text)

    def test_boolean_conditions_are_separately_checked(self):
        log='KNOWN_PHASE_PRESERVATION false\nKNOWN_PHASE_DISJOINT true\nKNOWN_PHASE_POSITIVE true\n'
        self.assertEqual(phase.parse_checks(log),{'preservation':False,'disjoint':True,'positive':True})
        for text in (log.replace('false','unknown'),log+'KNOWN_PHASE_PRESERVATION true\n',
                     log.replace('KNOWN_PHASE_POSITIVE true\n','')):
            with self.assertRaises(ValueError):phase.parse_checks(text)

    def test_incomplete_producer_evidence_cannot_start_phase(self):
        with tempfile.TemporaryDirectory() as tmp:
            provider=Path(tmp)/'provider';provider.mkdir()
            (provider/'report.json').write_text(json.dumps({'accepted':True,
                'complete_original_producer_list_proved':False}))
            with patch.object(phase,'run_stage') as native:
                result=phase.check(profile(),provider,Path(tmp)/'out')
            native.assert_not_called()
            self.assertFalse(result['accepted'])
            self.assertFalse(result['original_full_phase_proved'])

    def test_untrusted_runtime_symbol_is_not_coq_source(self):
        p=profile();p['ast']['program']='Bad.p. Admitted.'
        with self.assertRaises(ValueError):phase.phase_source(p)

if __name__=='__main__':unittest.main()
