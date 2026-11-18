import json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import cpu_pending_constrained_history as h


class ConstrainedHistoryTests(unittest.TestCase):
    def test_native_budget_checked_before_reading_providers(self):
        for timeout in[0,-1,1201]:
            with self.assertRaises(ValueError):h.check(None,None,None,None,None,None,timeout)

    def test_partial_or_open_assumption_provider_cannot_be_used(self):
        good=dict(accepted=True,coqc_exit=0,coqchk_exit=0,assumptions_closed=True)
        h.native_accepted(good)
        for key,value in[('accepted',False),('coqc_exit',124),('coqchk_exit',124),('assumptions_closed',False)]:
            with self.assertRaises(ValueError):h.native_accepted(dict(good,**{key:value}))

    def test_wrong_cpu_rejected_before_reading_any_old_source(self):
        report=dict(accepted=True,coqc_exit=0,coqchk_exit=0,assumptions_closed=True,actual_program='Wrong.p',ast_sha256='hash')
        def guarded(path,*args,**kwargs):
            if path.name!='report.json':raise AssertionError('proof read before input identity check')
            return json.dumps(report)
        with patch.object(Path,'read_text',guarded):
            with self.assertRaises(ValueError):h.verify_phase({},dict(actual_program='Raw.p',ast_sha256='hash'),Path('/catalog'),Path('/phase'))

    def test_generated_interface_retains_real_event_reset_and_entry_conditions(self):
        source=h.emit('Fresh.program','Raw.AST',23)
        self.assertEqual(source.count('Print Assumptions'),4)
        self.assertIn('CatalogEvent Fresh.program',source)
        self.assertIn('Age.J.EventAllowed ev',source);self.assertIn('Age.Q.ClockAllowed ev',source)
        self.assertIn('pre)23',source);self.assertIn('events<>[]',source)
        self.assertIn('Shape pre->',source);self.assertIn('(exists seed,CombLFP Fresh.program seed pre)',source)
        self.assertIn('Age.replay_erases',source)
        self.assertNotIn('Admitted',source);self.assertNotIn('Axiom',source)
        self.assertNotIn('Ex.External',source)
        statement=source.split('Theorem pending_history_from_environment',1)[1].split('Proof.',1)[0]
        self.assertIn('EnvironmentReady events pre',statement)
        self.assertNotIn('Age.Ready',statement)

    def test_symbol_and_reset_are_closed_data(self):
        for program,module,reset in[('Raw.p. Admitted.','Raw.AST',0),('Raw.p','bad;Import',0),('Raw.p','Raw.AST',-1),('Raw.p','Raw.AST',True)]:
            with self.assertRaises(ValueError):h.emit(program,module,reset)

    def test_native_partial_catalog_cannot_discharge_full_phase(self):
        report=dict(accepted=True,coqc_exit=0,coqchk_exit=0,assumptions_closed=True,
            actual_program='Raw.p',ast_sha256='hash',original_full_phase_under_catalog_shape_proved=False,
            itree_refinement_proved=False,metadata=dict(converges=True,covers_writers=True))
        with patch.object(Path,'read_text',return_value=json.dumps(report)),\
                patch.object(h.runtime,'proposal',side_effect=AssertionError('no old proof fallback')):
            with self.assertRaises(ValueError):h.verify_phase({},dict(actual_program='Raw.p',ast_sha256='hash'),Path('/catalog'),Path('/phase'))

    def test_unsupported_pending_stops_before_reading_a_phase_provider(self):
        with tempfile.TemporaryDirectory()as tmp,\
                patch.object(h.origin,'raw_binding',return_value=({},dict(ast={}),[])),\
                patch.object(h.age,'render',side_effect=ValueError('unsupported FIFO transport')),\
                patch.object(h,'verify_phase',side_effect=AssertionError('old certificate fallback')),\
                patch.object(h,'run_stage',side_effect=AssertionError('unchecked native stage')):
            report=h.check(Path('raw.v'),'Raw.AST',Path('/pending'),Path('/catalog'),Path('/phase'),Path(tmp)/'out')
        self.assertFalse(report['accepted']);self.assertFalse(report['native_started'])
        self.assertFalse(report['old_inv_read']);self.assertFalse(report['global_inv_proved'])
        self.assertEqual(report['residual'],'unsupported FIFO transport')


if __name__=='__main__':unittest.main()
