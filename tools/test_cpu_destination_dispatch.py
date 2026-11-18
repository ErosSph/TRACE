import unittest
import tempfile
from pathlib import Path
from contextlib import ExitStack
from unittest.mock import patch
import cpu_destination_dispatch as d


class DispatchTests(unittest.TestCase):
    def test_history_boot_requires_successful_initialization(self):
        for boot_ok in [False,True]:
            with tempfile.TemporaryDirectory()as tmp,ExitStack()as s:
                s.enter_context(patch.object(d.history.chain.p.origins,'raw_binding',return_value=({'source_sha256':'test'},{},[])))
                s.enter_context(patch.object(d.direct.destinations.inputs.fields,'proposal',return_value=(None,None,[],None,None,None)))
                s.enter_context(patch.object(d,'select',return_value=dict(routes=[dict(template='registered_rd_history'),dict(template='guarded_controller_write')],remaining=['ISA ownership'])))
                s.enter_context(patch.object(d.history,'check',return_value=dict(accepted=True,targets=[dict(roots=[3])])) )
                for name in ['cpu_capture_chain_coverage.check','cpu_invalid_capture_projection.check','cpu_covered_write_destination.check']:
                    s.enter_context(patch(name,return_value=dict(accepted=True)))
                s.enter_context(patch.object(d.guarded,'check',return_value=dict(accepted=True)))
                s.enter_context(patch('cpu_write_validity_chain.check',return_value=dict(accepted=True,entry_relation_proved=True)))
                s.enter_context(patch('cpu_write_validity_boot.check',return_value=dict(accepted=boot_ok)))
                history=s.enter_context(patch('cpu_captured_history_boot.check',return_value=dict(accepted=True)))
                provenance=s.enter_context(patch('cpu_capture_provenance.check',return_value=dict(accepted=True)))
                out=Path(tmp)/'run'
                result=d.run('raw.v','Raw.AST','isa',out,native=True,boot_provider='boot',catalog_provider='catalog',phase_provider='phase')
                self.assertEqual(history.call_count,int(boot_ok))
                self.assertEqual(provenance.call_count,int(boot_ok))
                self.assertFalse(result['complete_R_generated'])

    def test_partial_boot_provider_set_is_rejected(self):
        with self.assertRaisesRegex(ValueError,'requires boot, catalog and phase'):
            d.run('raw.v','Raw.AST','isa','unused',boot_provider='boot')

    def test_covered_write_uses_checked_endogenous_coverage(self):
        with tempfile.TemporaryDirectory()as tmp,ExitStack()as s:
            s.enter_context(patch.object(d.history.chain.p.origins,'raw_binding',return_value=({'source_sha256':'test'},{},[])))
            s.enter_context(patch.object(d.direct.destinations.inputs.fields,'proposal',return_value=(None,None,[],None,None,None)))
            s.enter_context(patch.object(d,'select',return_value=dict(routes=[dict(template='registered_rd_history')],remaining=['ISA ownership'])))
            s.enter_context(patch.object(d.history,'check',return_value=dict(accepted=True,targets=[dict(roots=[3,4])])) )
            cov=s.enter_context(patch('cpu_capture_chain_coverage.check',return_value=dict(accepted=True)))
            invalid=s.enter_context(patch('cpu_invalid_capture_projection.check',return_value=dict(accepted=True)))
            connect=s.enter_context(patch('cpu_covered_write_destination.check',return_value=dict(accepted=True)))
            out=Path(tmp)/'run';result=d.run('raw.v','Raw.AST','isa',out,native=True)
            cov.assert_called_once_with('raw.v','Raw.AST',out/'registered-rd-coverage',{3,4})
            invalid.assert_called_once_with('raw.v','Raw.AST',out/'registered-rd-coverage',out/'invalid-capture-projection')
            connect.assert_called_once_with('raw.v','Raw.AST','isa',out/'registered-rd-coverage',out/'covered-actual-destination')
            self.assertFalse(result['common_goal_proved'])
            self.assertFalse(result['complete_R_generated'])
    def select(self,direct=False,history=False,fixed=False):
        with patch.object(d.direct,'discover',return_value=([{'root':7}] if direct else [],[])), \
             patch.object(d.history,'discover',return_value=([{'endpoint':8}] if history else [],[])), \
             patch.object(d.fixed,'discover',return_value={'rows':[{'lane':1}] if fixed else [],'residuals':[]}):
            return d.select({'module':'never_used_cpu_name'},[])

    def test_direct_structure(self):
        self.assertEqual(self.select(direct=True)['routes'][0]['template'],'direct_sampled_rd')

    def test_history_structure(self):
        self.assertEqual(self.select(history=True)['routes'][0]['template'],'registered_rd_history')

    def test_fixed_structure(self):
        self.assertEqual(self.select(fixed=True)['routes'][0]['template'],'fixed_lane_decoder')

    def test_mixed_structures_do_not_drop_routes(self):
        self.assertEqual(len(self.select(True,True,True)['routes']),3)

    def test_no_template_is_not_success(self):
        p=self.select();self.assertEqual(p['routes'],[])
        self.assertFalse(p['common_goal_proved']);self.assertTrue(p['remaining'])

    def test_selection_is_not_proof(self):
        p=self.select(True,True,True)
        self.assertFalse(p['selection_is_proof']);self.assertFalse(p['common_goal_proved'])

    def test_native_runs_only_selected_checker_and_preserves_failure(self):
        with tempfile.TemporaryDirectory() as tmp,ExitStack() as s:
            s.enter_context(patch.object(d.history.chain.p.origins,'raw_binding',
                return_value=({'source_sha256':'test'},{},[])))
            s.enter_context(patch.object(d.direct.destinations.inputs.fields,'proposal',
                return_value=(None,None,[],None,None,None)))
            s.enter_context(patch.object(d,'select',return_value=dict(
                routes=[dict(template='registered_rd_history')],remaining=['token identity'])))
            h=s.enter_context(patch.object(d.history,'check',return_value=dict(accepted=False)))
            direct=s.enter_context(patch.object(d.direct,'check'))
            fixed=s.enter_context(patch.object(d.fixed,'check'))
            r=d.run('raw.v','Raw.AST','isa',Path(tmp)/'run',native=True)
            h.assert_called_once();direct.assert_not_called();fixed.assert_not_called()
            self.assertEqual(r['checked_components'],0)
            self.assertFalse(r['complete_R_generated'])


if __name__=='__main__':unittest.main()
