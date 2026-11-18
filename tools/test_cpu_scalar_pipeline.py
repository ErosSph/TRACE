import subprocess
import tempfile
import unittest
from contextlib import ExitStack
from pathlib import Path
from unittest.mock import patch

import cpu_auto_pipeline as pipeline


class ScalarPipelineTests(unittest.TestCase):
    def test_undeclared_stage_does_not_claim_success(self):
        with patch.object(pipeline.scalar_captures, 'check_profile') as check:
            self.assertIsNone(pipeline.check_scalar_components({}, Path('.'), 1))
        check.assert_not_called()

    def test_persistent_library_needs_declared_roots(self):
        with self.assertRaisesRegex(ValueError, 'explicit capture roots'):
            pipeline.check_scalar_components({'scalar_capture_library':'x.v'}, Path('.'), 1)

    def test_persistent_library_cannot_escape_src_or_change_suffix(self):
        for library in ('../outside.v','src/not-a-coq-file.txt'):
            with self.subTest(library=library), \
                 patch.object(pipeline.scalar_captures,'check_profile',
                    return_value={'accepted':True,'audited_exports':1}), \
                 patch.object(pipeline.scalar_captures,'emit_library') as emit:
                with self.assertRaisesRegex(ValueError,'project Coq source'):
                    pipeline.check_scalar_components(dict(scalar_capture_roots=[29],
                        scalar_capture_library=library),Path('.'),1)
                emit.assert_not_called()

    def exercise(self, component_ok=True, compile_rc=0, kernel_rc=0, closed=True, rhs_ok=None):
        profile = dict(scalar_capture_roots=[29,64,65],
            scalar_capture_library='src/Ex/Generated/DarkRISCVGeneratedScalarCaptures.v')
        if rhs_ok is not None:
            profile['scalar_rhs_library']='src/Ex/Generated/DarkRISCVGeneratedScalarRHS.v'
        log = ('AUTO_ADAPTER_ASSUMPTIONS_0\nClosed under the global context\n'
            if closed else 'AUTO_ADAPTER_ASSUMPTIONS_0\nAxioms:\nBad : False\n')
        compile_result = (subprocess.CompletedProcess([],compile_rc,log,''),False)
        kernel_result = (subprocess.CompletedProcess([],kernel_rc,'',''),False)
        with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
            check = stack.enter_context(patch.object(pipeline.scalar_captures,'check_profile',
                return_value={'accepted':component_ok,'audited_exports':1}))
            emit = stack.enter_context(patch.object(pipeline.scalar_captures,'emit_library',
                return_value={'source_matches_generator':True,'coq_checked':False}))
            stack.enter_context(patch.object(pipeline,'flags_for',return_value=[]))
            stack.enter_context(patch.object(pipeline,'check_scalar_rhs_library',
                return_value={'accepted':rhs_ok}))
            run = stack.enter_context(patch.object(pipeline,'run_stage',
                side_effect=[compile_result,kernel_result]))
            result = pipeline.check_scalar_components(profile,Path(tmp),1200)
            self.assertEqual(check.call_args.args[2],[29,64,65])
            if component_ok:
                self.assertTrue(emit.call_args.kwargs['check'])
            else:
                emit.assert_not_called()
                run.assert_not_called()
        return result

    def test_component_failure_stops_persistent_check(self):
        self.assertFalse(self.exercise(component_ok=False)['accepted'])

    def test_persistent_compile_failure_cannot_be_hidden(self):
        self.assertFalse(self.exercise(compile_rc=1)['accepted'])

    def test_persistent_kernel_failure_cannot_be_hidden(self):
        self.assertFalse(self.exercise(kernel_rc=1)['accepted'])

    def test_unexpected_axiom_rejected(self):
        self.assertFalse(self.exercise(closed=False)['accepted'])

    def test_checked_local_stage_does_not_claim_identity(self):
        result = self.exercise()
        self.assertTrue(result['accepted'])
        self.assertFalse(result['discharges_token_identity'])

    def test_rhs_library_requires_checked_persistent_capture_base(self):
        with self.assertRaisesRegex(ValueError,'persistent capture library'):
            pipeline.check_scalar_components({'scalar_rhs_library':'x.v'},Path('.'),1)

    def test_rhs_failure_cannot_hide_behind_capture_success(self):
        result=self.exercise(rhs_ok=False)
        self.assertTrue(result['component']['accepted'])
        self.assertTrue(result['persistent_library']['accepted'])
        self.assertFalse(result['accepted'])

    def test_rhs_success_is_required_when_registered(self):
        result=self.exercise(rhs_ok=True)
        self.assertTrue(result['accepted'])
        self.assertTrue(result['rhs_library']['accepted'])

    def test_rhs_persistent_compile_or_kernel_failure_rejected(self):
        profile=dict(scalar_capture_roots=[29],
            scalar_capture_library='src/Ex/Generated/DarkRISCVGeneratedScalarCaptures.v',
            scalar_rhs_library='src/Ex/Generated/DarkRISCVGeneratedScalarRHS.v')
        closed='AUTO_ADAPTER_ASSUMPTIONS_0\nClosed under the global context\n'
        for compile_rc,kernel_rc in [(1,0),(0,1),(0,0)]:
            with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
                emit=stack.enter_context(patch.object(pipeline.scalar_rhs,'emit_library',
                    return_value={'source_matches_generator':True}))
                stack.enter_context(patch.object(pipeline,'flags_for',return_value=[]))
                stack.enter_context(patch.object(pipeline,'run_stage',side_effect=[
                    (subprocess.CompletedProcess([],compile_rc,closed,''),False),
                    (subprocess.CompletedProcess([],kernel_rc,'',''),False)]))
                result=pipeline.check_scalar_rhs_library(profile,Path(tmp),1200)
                self.assertEqual(result['accepted'],compile_rc==kernel_rc==0)
                self.assertTrue(emit.call_args.kwargs['check'])
                self.assertEqual(emit.call_args.kwargs['base_module'],
                    'Ex.Generated.DarkRISCVGeneratedScalarCaptures')

    def test_old_itree_success_cannot_mask_scalar_failure(self):
        local = dict(local_semantics_accepted=True,generated_sequential_plans=1,
            generated_state_threaded_effect_plans=0,sequential_processes=1,
            generated_compiled_phase_projections=1,generated_semantic_consequences=5,
            residual_processes=[])
        replacements = [
            (pipeline.adapter,'check_profile',local),
            (pipeline,'check_scalar_components',{'accepted':False}),
            (pipeline.bank_adapter,'check_profile',{'accepted':True,'generated_banks':[],'residuals':[]}),
            (pipeline.bank_reads,'check_profile',{'accepted':True,'sites':[]}),
            (pipeline.rf_ports,'check_profile',{'accepted':True,'ports':[]}),
            (pipeline.roles,'suggest_roles',{'llm':{'attempts':0}}),
            (pipeline.joint_obligations,'plan',{}),
            (pipeline,'assemble_contract',{'accepted':True})]
        with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
            stack.enter_context(patch('builtins.print'))
            for obj,name,value in replacements:
                stack.enter_context(patch.object(obj,name,return_value=value))
            result = pipeline.run_one('unknown',{'joint_binding':{'test':True}},
                Path(tmp)/'out',1200,False,None)
        self.assertTrue(result['new_joint_local_evidence_itree_assembly_accepted'])
        self.assertFalse(result['registered_design_pipeline_accepted'])


if __name__ == '__main__':
    unittest.main()
