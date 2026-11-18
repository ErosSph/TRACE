import subprocess
import tempfile
import unittest
from contextlib import ExitStack
from pathlib import Path
from unittest.mock import patch
import cpu_auto_pipeline as p


class GuardPipelineTests(unittest.TestCase):
    def test_absent_stage_is_not_a_proof(self):
        with patch.object(p.guard_bindings,'check_profile') as check:
            self.assertIsNone(p.check_guard_binding_components({},Path('.'),1))
        check.assert_not_called()

    def test_observation_roots_required(self):
        with self.assertRaisesRegex(ValueError,'observation roots'):
            p.check_guard_binding_components({'scalar_guard_library':'x.v'},Path('.'),1)

    def exercise(self,component=True,compile_rc=0,kernel_rc=0,closed=True,partition=True):
        profile=dict(plan_slice_roots=[9],scalar_guard_library='src/Ex/Generated/TestGuards.v')
        log='AUTO_ADAPTER_ASSUMPTIONS_0\n'+('Closed under the global context\n'
            if closed else 'Axioms:\nBad : False\n')
        with tempfile.TemporaryDirectory() as tmp,ExitStack() as stack:
            check=stack.enter_context(patch.object(p.guard_bindings,'check_profile',
                return_value=dict(accepted=component,audited_exports=1)))
            emit=stack.enter_context(patch.object(p.guard_bindings,'emit_library',return_value={}))
            partition_check=stack.enter_context(patch.object(p.guard_partitions,'check_profile',
                return_value=dict(accepted=partition)))
            stack.enter_context(patch.object(p,'flags_for',return_value=[]))
            run=stack.enter_context(patch.object(p,'run_stage',side_effect=[
                (subprocess.CompletedProcess([],compile_rc,log,''),False),
                (subprocess.CompletedProcess([],kernel_rc,'',''),False)]))
            result=p.check_guard_binding_components(profile,Path(tmp),1200)
            self.assertEqual(check.call_args.args[2],[9])
            if component and partition:self.assertTrue(emit.call_args.kwargs['check'])
            else:emit.assert_not_called();run.assert_not_called()
            if not component:partition_check.assert_not_called()
        return result

    def test_failed_component_cannot_reuse_old_library(self):
        self.assertFalse(self.exercise(component=False)['accepted'])

    def test_failed_partition_cannot_reuse_sufficient_conditions(self):
        self.assertFalse(self.exercise(partition=False)['accepted'])

    def test_compile_kernel_and_axiom_failures_rejected(self):
        for rc,kr,closed in [(1,0,True),(0,1,True),(0,0,False)]:
            with self.subTest(rc=rc,kr=kr,closed=closed):
                self.assertFalse(self.exercise(compile_rc=rc,kernel_rc=kr,closed=closed)['accepted'])

    def test_local_bindings_not_global_preservation(self):
        result=self.exercise()
        self.assertTrue(result['accepted'])
        for key in ['discharges_reachable_guards','discharges_token_identity',
                    'discharges_joint_preservation']:
            self.assertFalse(result[key])

    def test_path_escape_rejected(self):
        for path in ['../outside.v','src/not-coq.txt']:
            with patch.object(p.guard_bindings,'check_profile',return_value=dict(accepted=True)), \
                 patch.object(p.guard_partitions,'check_profile',return_value=dict(accepted=True)), \
                 self.assertRaisesRegex(ValueError,'project Coq source'):
                p.check_guard_binding_components(dict(scalar_guard_roots=[9],
                    scalar_guard_library=path),Path('.'),1)

    def test_old_itree_success_cannot_hide_failed_guards(self):
        local=dict(local_semantics_accepted=True,generated_sequential_plans=1,
            generated_state_threaded_effect_plans=0,sequential_processes=1,
            generated_compiled_phase_projections=1,generated_semantic_consequences=5,residual_processes=[])
        replacements=[(p.adapter,'check_profile',local),
            (p,'check_guard_binding_components',dict(accepted=False)),
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
