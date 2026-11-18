import unittest
from unittest.mock import patch
import cpu_known_producers as known

def profile():
    return {'ast':{'module':'Renamed.AST','program':'ActualRuntime.p',
        'program_imports':['Another.Runtime']}}

def log():
    return '\n'.join('KNOWN_'+k+' '+str(v) for k,v in (
        ('TOTAL',4),('BASE_RESIDUAL',2),('NEW_ACCEPTED',1),('REMAINING',1),
        ('LFP_FUEL',9),('STATEMENT_FUEL',512)))+'\n'

class KnownProducerTests(unittest.TestCase):
    def test_short_circuit_changes_only_diagnostic_expression(self):
        with patch.object(known.registry,'proposal',return_value=({'source_sha256':'test'},'',2)):
            _,old=known.proposal(profile(),False)
            _,new=known.proposal(profile(),True)
            with self.assertRaises(ValueError):known.proposal(profile(),'false')
        self.assertIn('if is_comb(snd ip) then',new)
        self.assertIn(' if producer_accepted',new)
        self.assertIn('is_comb(snd ip) &&\n negb(producer_accepted',old)
        import re
        strip=lambda s:re.sub(r'(?s)Definition accepted_indices :=.*?\nGoal True\.',
            'Definition DIAGNOSTIC_ONLY.\nGoal True.',s)
        self.assertEqual(strip(old),strip(new))

    def test_counts_preserve_actual_program_configuration(self):
        counts=known.counts(log())
        self.assertEqual(counts['remaining'],1)
        self.assertEqual(counts['lfp_fuel'],9)
        self.assertEqual(counts['statement_fuel'],512)

    def test_missing_duplicate_and_inconsistent_counts_rejected(self):
        for text in (log().replace('KNOWN_TOTAL 4\n',''),log()+'KNOWN_TOTAL 4\n',
            log().replace('KNOWN_NEW_ACCEPTED 1','KNOWN_NEW_ACCEPTED 2'),
            log().replace('KNOWN_BASE_RESIDUAL 2','KNOWN_BASE_RESIDUAL 5')):
            with self.assertRaises(ValueError):known.counts(text)

    def test_completion_explicitly_imports_original_runtime_namespace(self):
        text=known.completion_source(profile())
        self.assertIn('Renamed.AST Another.Runtime.',text)
        self.assertIn('ProducerIdempotent ActualRuntime.p',text)
        self.assertIn('Known.original_producers_if_remaining_empty original_remaining_empty',text)
        self.assertNotIn('PhaseSemantics',text)

    def test_completion_rejects_source_injection(self):
        for field,value in (('program','Actual.p. Admitted.'),
            ('program_imports','Another.Runtime'),('module','Bad;Assume')):
            p=profile();p['ast'][field]=value
            with self.assertRaises(ValueError):known.completion_source(p)

    def test_proposal_uses_actual_context_and_conditional_completeness(self):
        with patch.object(known.registry,'proposal',return_value=({'source_sha256':'test'},'',2)):
            _,text=known.proposal(profile())
        self.assertIn('known_producerb ActualRuntime.p',text)
        self.assertIn('remaining_order=[] -> Forall',text)
        self.assertIn('KNOWN_ACCEPTED_INDICES',text)
        self.assertNotIn('Bzeeno',text)
        self.assertNotIn('Admitted',text)

if __name__=='__main__':unittest.main()
