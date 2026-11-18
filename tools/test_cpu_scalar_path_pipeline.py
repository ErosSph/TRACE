import subprocess
import tempfile
import unittest
from contextlib import ExitStack
from pathlib import Path
from unittest.mock import patch
import cpu_auto_pipeline as p


class PathPipelineTests(unittest.TestCase):
    def test_absent_stage_does_not_claim_proof(self):
        with patch.object(p.scalar_paths,'check_profile') as check:
            self.assertIsNone(p.check_scalar_path_components({},Path('.'),1))
        check.assert_not_called()

    def test_roots_are_required(self):
        with self.assertRaisesRegex(ValueError,'observation roots'):
            p.check_scalar_path_components({'scalar_path_library':'x.v'},Path('.'),1)

    def exercise(self,component=True,compile_rc=0,kernel_rc=0,closed=True):
        profile=dict(plan_slice_roots=[9],scalar_path_library='src/Ex/Generated/TestPaths.v')
        log='AUTO_ADAPTER_ASSUMPTIONS_0\n'+('Closed under the global context\n'
            if closed else 'Axioms:\nBad : False\n')
        with tempfile.TemporaryDirectory() as tmp,ExitStack() as stack:
            check=stack.enter_context(patch.object(p.scalar_paths,'check_profile',
                return_value=dict(accepted=component,audited_exports=1)))
            emit=stack.enter_context(patch.object(p.scalar_paths,'emit_library',return_value={}))
            stack.enter_context(patch.object(p,'flags_for',return_value=[]))
            run=stack.enter_context(patch.object(p,'run_stage',side_effect=[
                (subprocess.CompletedProcess([],compile_rc,log,''),False),
                (subprocess.CompletedProcess([],kernel_rc,'',''),False)]))
            result=p.check_scalar_path_components(profile,Path(tmp),1200)
            self.assertEqual(check.call_args.args[2],[9])
            if component:self.assertTrue(emit.call_args.kwargs['check'])
            else:emit.assert_not_called();run.assert_not_called()
        return result

    def test_new_component_failure_cannot_use_old_library(self):
        self.assertFalse(self.exercise(component=False)['accepted'])

    def test_compile_kernel_and_axiom_failures_rejected(self):
        for rc,kr,closed in [(1,0,True),(0,1,True),(0,0,False)]:
            with self.subTest(rc=rc,kr=kr,closed=closed):
                self.assertFalse(self.exercise(compile_rc=rc,kernel_rc=kr,closed=closed)['accepted'])

    def test_paths_do_not_prove_reachability_or_identity(self):
        result=self.exercise()
        self.assertTrue(result['accepted'])
        self.assertFalse(result['discharges_reachable_guards'])
        self.assertFalse(result['discharges_token_identity'])

    def test_path_escape_rejected(self):
        for path in ['../outside.v','src/not-coq.txt']:
            with patch.object(p.scalar_paths,'check_profile',return_value=dict(accepted=True)), \
                 self.assertRaisesRegex(ValueError,'project Coq source'):
                p.check_scalar_path_components(dict(scalar_path_roots=[9],
                    scalar_path_library=path),Path('.'),1)

    def test_old_itree_success_cannot_hide_path_failure(self):
        local=dict(local_semantics_accepted=True,generated_sequential_plans=1,
            generated_state_threaded_effect_plans=0,sequential_processes=1,
            generated_compiled_phase_projections=1,generated_semantic_consequences=5,residual_processes=[])
        replacements=[(p.adapter,'check_profile',local),
            (p,'check_scalar_path_components',dict(accepted=False)),
            (p.bank_adapter,'check_profile',dict(accepted=True,generated_banks=[],residuals=[])),
            (p.bank_reads,'check_profile',dict(accepted=True,sites=[])),
            (p.rf_ports,'check_profile',dict(accepted=True,ports=[])),
            (p.roles,'suggest_roles',dict(llm={})),(p.joint_obligations,'plan',{}),
            (p,'assemble_contract',dict(accepted=True))]
        with tempfile.TemporaryDirectory() as tmp,ExitStack() as stack:
            stack.enter_context(patch('builtins.print'))
            for obj,name,value in replacements:
                stack.enter_context(patch.object(obj,name,return_value=value))
            result=p.run_one('new',dict(joint_binding={'test':True}),Path(tmp)/'out',1,False,None)
        self.assertTrue(result['new_joint_local_evidence_itree_assembly_accepted'])
        self.assertFalse(result['registered_design_pipeline_accepted'])


if __name__=='__main__':unittest.main()
