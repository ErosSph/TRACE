import subprocess
import tempfile
import unittest
from contextlib import ExitStack
from pathlib import Path
from unittest.mock import patch

import cpu_auto_pipeline as p


class PlanSlicePipelineTests(unittest.TestCase):
    def test_absent_stage_is_not_claimed_checked(self):
        with patch.object(p.plan_slices,'check_profile') as check:
            self.assertIsNone(p.check_plan_slice_components({},Path('.'),1))
        check.assert_not_called()

    def test_library_requires_declared_roots(self):
        with self.assertRaisesRegex(ValueError,'declared roots'):
            p.check_plan_slice_components({'plan_slice_library':'x.v'},Path('.'),1)

    def exercise(self,component_ok=True,compile_rc=0,kernel_rc=0,closed=True):
        profile=dict(plan_slice_roots=[337],
            plan_slice_library='src/Ex/Generated/CVTokenSlices.v')
        log='AUTO_ADAPTER_ASSUMPTIONS_0\n'+(
            'Closed under the global context\n' if closed else 'Axioms:\nBad : False\n')
        with tempfile.TemporaryDirectory() as tmp,ExitStack() as stack:
            stack.enter_context(patch.object(p.plan_slices,'check_profile',
                return_value=dict(accepted=component_ok,audited_exports=1)))
            emit=stack.enter_context(patch.object(p.plan_slices,'emit_library',
                return_value=dict(source_matches_generator=True,coq_checked=False)))
            stack.enter_context(patch.object(p,'flags_for',return_value=[]))
            run=stack.enter_context(patch.object(p,'run_stage',side_effect=[
                (subprocess.CompletedProcess([],compile_rc,log,''),False),
                (subprocess.CompletedProcess([],kernel_rc,'',''),False)]))
            result=p.check_plan_slice_components(profile,Path(tmp),1200)
            if component_ok:self.assertTrue(emit.call_args.kwargs['check'])
            else:
                emit.assert_not_called();run.assert_not_called()
        return result

    def test_component_failure_cannot_reuse_old_library(self):
        self.assertFalse(self.exercise(component_ok=False)['accepted'])

    def test_compile_kernel_or_audit_failure_rejected(self):
        for rc,kr,closed in [(1,0,True),(0,1,True),(0,0,False)]:
            with self.subTest(rc=rc,kr=kr,closed=closed):
                self.assertFalse(self.exercise(compile_rc=rc,kernel_rc=kr,closed=closed)['accepted'])

    def test_local_success_does_not_claim_architectural_identity(self):
        result=self.exercise()
        self.assertTrue(result['accepted'])
        self.assertFalse(result['discharges_token_identity'])

    def test_source_path_validation(self):
        for library in ['../outside.v','src/not-coq.txt']:
            with patch.object(p.plan_slices,'check_profile',
                    return_value=dict(accepted=True,audited_exports=1)), \
                 self.assertRaisesRegex(ValueError,'project Coq source'):
                p.check_plan_slice_components(dict(plan_slice_roots=[9],
                    plan_slice_library=library),Path('.'),1)

    def test_old_itree_success_cannot_mask_slice_failure(self):
        local=dict(local_semantics_accepted=True,generated_sequential_plans=1,
            generated_state_threaded_effect_plans=0,sequential_processes=1,
            generated_compiled_phase_projections=1,generated_semantic_consequences=5,
            residual_processes=[])
        replacements=[(p.adapter,'check_profile',local),
            (p,'check_plan_slice_components',dict(accepted=False)),
            (p.bank_adapter,'check_profile',dict(accepted=True,generated_banks=[],residuals=[])),
            (p.bank_reads,'check_profile',dict(accepted=True,sites=[])),
            (p.rf_ports,'check_profile',dict(accepted=True,ports=[])),
            (p.roles,'suggest_roles',dict(llm=dict(attempts=0))),
            (p.joint_obligations,'plan',{}),(p,'assemble_contract',dict(accepted=True))]
        with tempfile.TemporaryDirectory() as tmp,ExitStack() as stack:
            stack.enter_context(patch('builtins.print'))
            for obj,name,value in replacements:
                stack.enter_context(patch.object(obj,name,return_value=value))
            result=p.run_one('new',dict(joint_binding={'test':True}),Path(tmp)/'out',1200,False,None)
        self.assertTrue(result['new_joint_local_evidence_itree_assembly_accepted'])
        self.assertFalse(result['registered_design_pipeline_accepted'])


if __name__=='__main__':unittest.main()
