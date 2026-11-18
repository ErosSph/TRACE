import unittest
import cpu_add_admission_ledger as ledger


class Tests(unittest.TestCase):
    def source(self):
        plan=dict(birth=dict(root=140,valid=141,process='fetch'), head=dict(process='ex',valid=250))
        return ledger.render(dict(ast_module='Input.AST'),dict(module='DUT'),dict(ast=dict(program='DUT.program')),plan)

    def test_real_queue_and_physical_data_are_both_consumed(self):
        source=self.source()
        self.assertIn('AQ.actual_admission_pending_transfer',source)
        self.assertIn('AD.actual_admission_preserves_physical_RFJoint',source)
        self.assertIn('AQ.actual_admission_restores_operand_clause',source)

    def test_target_uses_actual_post_queue_not_a_caller_equality(self):
        header=self.source().split('Theorem actual_admission_restores_extended_register_data')[1].split('Proof.')[0]
        self.assertIn('Q.actual_pending (PhaseSemantics DUT.program ev pre)',header)
        self.assertNotIn('HQ',header)
        self.assertNotIn('CertifiedBatches',header)

    def test_range_is_explicit_current_inv_component_not_environment_correctness(self):
        source=self.source()
        self.assertIn('Definition LedgerRange',source)
        self.assertIn('HistoryRange(serial(fst packed))',source)
        self.assertIn('D.Current token_pc initial retired current pre packed /\\LedgerRange',source)
        self.assertIn('actual_births_preserve_ledger_range',source)
        self.assertIn('actual_births_preserve_unique_ledger',source)

    def test_actual_phase_counter_and_births_are_proved_equal(self):
        source=self.source()
        self.assertIn('Lemma admitted_form',source)
        self.assertIn('Lemma actual_post_serial',source)
        self.assertIn('phase_decision DUT.program DUT.fetch 140',source)

    def test_does_not_claim_the_new_ISA_chain(self):
        source=self.source()
        header=source.split('Theorem actual_admission_restores_extended_register_data')[1].split('Proof.')[0]
        self.assertIn('O.RFJoint',header)
        self.assertNotIn('FormalSpec.run1',header)
        self.assertNotIn('Admitted.',source)
        self.assertNotIn('Axiom ',source)

    def test_qualification_removes_only_exact_aliases(self):
        original=self.source();qualified=ledger.qualify_module_aliases(original)
        self.assertNotIn('Module AQ:=',qualified)
        self.assertNotIn('Module AD:=',qualified)
        self.assertIn('GeneratedAdmissionQueue.AdmissionQueue.D.Current',qualified)
        self.assertIn('GeneratedAdmissionData.AdmissionData.actual_admission_preserves_physical_RFJoint',qualified)
        self.assertEqual(original.count('Theorem '),qualified.count('Theorem '))
        self.assertEqual(original.count('->'),qualified.count('->'))

    def test_qualification_does_not_requalify_dotted_module_components(self):
        source=self.source()+'\nCheck GeneratedAdmissionQueue.AdmissionQueue.D.Current.\n'
        qualified=ledger.qualify_module_aliases(source)
        self.assertTrue(qualified.endswith('Check GeneratedAdmissionQueue.AdmissionQueue.D.Current.\n'))

    def test_changed_module_binding_is_rejected(self):
        source=self.source().replace('Module D:=AQ.D.','Module D:=WrongCPU.Inv.')
        with self.assertRaises(ValueError):
            ledger.qualify_module_aliases(source)


if __name__=='__main__':
    unittest.main()
