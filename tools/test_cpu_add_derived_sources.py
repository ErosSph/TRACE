import unittest
import cpu_add_derived_sources as sources


class Tests(unittest.TestCase):
    def proof(self,text,root=3):
        return sources.required_bit_proof(sources.rtl.Parser(text).complete(),root)

    def test_bit_source(self):
        self.assertEqual(self.proof('(EVar 1 3)'),'apply RequiresSource.')

    def test_wrong_width_is_not_a_source_bit(self):
        self.assertIsNone(self.proof('(EVar 2 3)'))

    def test_guard_preserved_and_proof_branches_focused(self):
        p=self.proof('(ECond 1 (EVar 1 7) (EVar 1 3) (EConst 1 0))')
        self.assertIn('RequiresChoice. {',p)
        self.assertIn('} {',p)

    def test_nonzero_branch_cannot_be_ignored(self):
        self.assertIsNone(self.proof('(ECond 1 (EVar 1 7) (EVar 1 3) (EConst 1 1))'))

    def test_and_preserves_source_requirement(self):
        self.assertIn('RequiresAndLeft',self.proof('(EBinary 1 BAnd (EVar 1 3) (EVar 1 7))'))

    def test_or_does_not_imply_either_input(self):
        self.assertIsNone(self.proof('(EBinary 1 BOr (EVar 1 3) (EVar 1 7))'))

    def source(self):
        plan=dict(rows=[dict(stage=0,valid=10,routes={k:dict(input=v)for k,v in [('write',1),('load',2),('rd',3)]}),
                        dict(stage=1,valid=20,routes={k:dict(input=v)for k,v in [('write',4),('load',5),('rd',6)]})],
            young_value=30,old_value=40,memory_value=50,bank=60,birth=dict(valid=70),
            head=dict(valid=10,process='capture',event=dict(clock=76,reset=77)),
            ports=[dict(selector=80,source=81,field='Rs1',operand=82),dict(selector=90,source=91,field='Rs2',operand=92)])
        cov=dict(coverage=dict(covered_fields=[dict(expanded='(ECond 1 (EVar 1 77) (EBinary 1 BAnd (EVar 1 70) (EVar 1 73)) (EConst 1 0))')]))
        return sources.render(dict(ast_module='Input.AST'),dict(module='DUT'),dict(ast=dict(program='DUT.program')),plan,cov)[0]

    def test_actual_operand_target_has_no_caller_batches_or_slot_correctness(self):
        target=self.source().split('Theorem actual_admitted_add_operand_relation',1)[1].split('Proof.',1)[0]
        self.assertNotIn('CertifiedBatches',target)
        self.assertNotIn('SlotRelated',target)
        self.assertNotIn('HeadsAlong',target)
        self.assertIn('computed_result_R',target)
        self.assertIn('OperandProjection token (PhaseSemantics DUT.program ev pre)',target)

    def test_clock_and_source_valid_are_derived_not_caller_obligations(self):
        source=self.source();target=source.split('Theorem actual_admitted_add_operand_relation',1)[1].split('Proof.',1)[0]
        self.assertNotIn('read_signal pre 76',target)
        self.assertNotIn('read_signal pre 70',target)
        self.assertIn('admitted_source_valid seed ev pre',source)
        self.assertIn('admission_old_clock_zero ev pre',source)

    def test_original_chain_and_same_hardware_stage_order_are_consumed(self):
        source=self.source()
        self.assertIn('Ref.certify_reference_producers',source)
        self.assertIn('collect_1 pre sampled packed',source)
        self.assertIn('Some(older++younger)',source)
        self.assertIn('lookup_before_complete',source)
        self.assertIn('Captured.C.chain_tag1',source)

    def test_both_actual_capture_consumers_are_present(self):
        source=self.source()
        self.assertIn('captured_source_add_80',source)
        self.assertIn('captured_source_add_90',source)
        self.assertIn('Ref.before_prefix',source)

    def test_real_post_tag_is_used_to_restore_same_operand_clause(self):
        source=self.source()
        self.assertIn('actual_admitted_tag',source)
        self.assertIn('actual_add_operand_clause_phase',source)
        self.assertIn('Captured.advance_capture_fields ev pre',source)
        self.assertIn('operand_clause_idle',source)

    def test_new_tail_requires_no_execution_assumption(self):
        source=self.source();target=source.split('Theorem actual_add_operand_clause_with_new_tokens',1)[1].split('Proof.',1)[0]
        self.assertIn('++added',target)
        self.assertNotIn('EffectChain',target)
        self.assertNotIn('CertifiedBatches',target)
        self.assertIn('apply Ref.computed_result_append',source)


if __name__=='__main__':unittest.main()
