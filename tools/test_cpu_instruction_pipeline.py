import tempfile
import unittest
from types import SimpleNamespace
from contextlib import ExitStack
from pathlib import Path
from unittest.mock import patch
import cpu_auto_pipeline as p
import cpu_field_snapshots as snapshots
import cpu_sampled_field_snapshots as sampled


class InstructionPipelineTests(unittest.TestCase):
    def setUp(self):
        replacement=patch.object(snapshots,'check',return_value=dict(accepted=True))
        self.snapshot_check=replacement.start();self.addCleanup(replacement.stop)
        replacement=patch.object(sampled,'check',return_value=dict(accepted=True))
        self.sampled_check=replacement.start();self.addCleanup(replacement.stop)
    def test_missing_ast_not_claimed_as_a_stage_proof(self):
        with patch.object(p.instruction_fields,'check_profile') as check:
            self.assertIsNone(p.check_instruction_components({},Path('.'),1))
        check.assert_not_called()

    def exercise(self,fields=True,aliases=True,tagged=True):
        with tempfile.TemporaryDirectory() as tmp,ExitStack() as stack:
            stack.enter_context(patch.object(p.instruction_fields,'check_profile',
                return_value=dict(accepted=fields)))
            alias=stack.enter_context(patch.object(p.instruction_aliases,'check_profile',
                return_value=dict(accepted=aliases)))
            tag=stack.enter_context(patch.object(p.instruction_tags,'check_profile',
                return_value=dict(accepted=tagged)))
            result=p.check_instruction_components({'ast':{}},Path(tmp),1200)
            if not fields:alias.assert_not_called()
            if not fields or not aliases:tag.assert_not_called()
        return result

    def test_layout_failure_does_not_use_aliases(self):
        self.assertFalse(self.exercise(fields=False)['accepted'])

    def test_alias_failure_not_masked_by_field_layouts(self):
        self.assertFalse(self.exercise(aliases=False)['accepted'])

    def test_tag_failure_not_masked_by_field_and_alias_proofs(self):
        self.assertFalse(self.exercise(tagged=False)['accepted'])

    def test_success_not_a_current_instruction_or_global_proof(self):
        result=self.exercise()
        self.assertTrue(result['accepted'])
        for key in ['discharges_current_isa_identity','discharges_operand_freshness',
                    'discharges_joint_preservation']:
            self.assertFalse(result[key])

    def test_supported_snapshot_failure_is_not_hidden(self):
        self.snapshot_check.return_value=dict(accepted=False)
        self.assertFalse(self.exercise()['accepted'])

    def test_supported_sampled_snapshot_failure_is_not_hidden(self):
        self.sampled_check.return_value=dict(accepted=False)
        self.assertFalse(self.exercise()['accepted'])

    def test_unsupported_snapshot_is_explicit_not_claimed_proven(self):
        self.snapshot_check.return_value=dict(accepted=False,status='no_supported_comb_snapshot')
        result=self.exercise()
        self.assertTrue(result['accepted'])
        self.assertFalse(result['field_snapshots']['accepted'])

    def test_explicit_field_only_scope_does_not_start_unrelated_tag_proofs(self):
        with tempfile.TemporaryDirectory()as directory,ExitStack()as stack:
            for module in (p.instruction_fields,p.instruction_aliases):
                stack.enter_context(patch.object(module,'check_profile',return_value=dict(accepted=True)))
            tag=stack.enter_context(patch.object(p.instruction_tags,'check_profile'))
            result=p.check_instruction_components({'ast':{}},Path(directory),1200,check_tagged=False)
        tag.assert_not_called()
        self.assertTrue(result['accepted'])
        self.assertFalse(result['complete_instruction_component_scope_requested'])
        self.assertFalse(result['tagged_fields']['accepted'])
        self.assertEqual(result['tagged_fields']['status'],'not_requested')

    def test_persistent_library_path_escape_rejected(self):
        for path in ['../outside.v','src/not-coq.txt']:
            with tempfile.TemporaryDirectory() as tmp, \
                 patch.object(p.instruction_fields,'check_profile',return_value=dict(accepted=True)), \
                 patch.object(p.instruction_aliases,'check_profile',return_value=dict(accepted=True)), \
                 patch.object(p.instruction_tags,'check_profile',return_value=dict(accepted=True)), \
                 self.assertRaisesRegex(ValueError,'project Coq source'):
                p.check_instruction_components({'ast':{},'instruction_field_library':path},Path(tmp),1)

    def test_old_itree_success_does_not_hide_new_component_failure(self):
        local=dict(local_semantics_accepted=True,generated_sequential_plans=1,
            generated_state_threaded_effect_plans=0,sequential_processes=1,
            generated_compiled_phase_projections=1,generated_semantic_consequences=5,residual_processes=[])
        replacements=[(p.adapter,'check_profile',local),
            (p,'check_instruction_components',dict(accepted=False,fields=dict(accepted=False))),
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

    def test_failed_persistent_alias_not_hidden_by_checked_temporary_alias(self):
        with tempfile.TemporaryDirectory() as tmp,ExitStack() as stack:
            for module in [p.instruction_fields,p.instruction_aliases,p.instruction_tags]:
                stack.enter_context(patch.object(module,'check_profile',return_value=dict(accepted=True)))
            stack.enter_context(patch.object(p.instruction_aliases,'emit_library',return_value={}))
            stack.enter_context(patch.object(p,'run_stage',return_value=(SimpleNamespace(returncode=1),False)))
            result=p.check_instruction_components({'ast':{},
                'instruction_word_alias_library':'src/Ex/Generated/TestAliases.v'},Path(tmp),1)
        self.assertFalse(result['accepted'])
        self.assertFalse(result['persistent_alias_library']['accepted'])


if __name__=='__main__':unittest.main()
