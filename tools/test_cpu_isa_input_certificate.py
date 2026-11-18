import subprocess
import tempfile
import unittest
from pathlib import Path
import cpu_isa_input_certificate as certificate


class InputCertificate(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root=certificate.synthesis.ROOT
        cls.plan,cls.source=certificate.render((cls.root/'dep/riscv-coq/src/riscv/Spec/ExecuteI.v').read_text())

    def test_all_requested_instructions(self):
        self.assertEqual(len(self.plan['instructions']),38)
        self.assertIn('| Decode.Add rd rs1 rs2 => [rs1;rs2]',self.source)
        self.assertIn('| Decode.Addi rd rs1 imm12 => [rs1]',self.source)
        self.assertIn('| Decode.Auipc rd oimm20 => []',self.source)
        self.assertNotIn('Admitted',self.source)
        self.assertNotIn('Axiom ',self.source)

    def test_non_data_reads_are_checked_not_only_classified(self):
        self.assertIn('Theorem requested_reads',self.source)
        header=self.source.split('Theorem requested_reads',1)[1].split('Proof.',1)[0]
        self.assertNotIn('data_operation',header)
        self.assertIn('| Decode.Sb rs1 rs2 simm12 => [rs1;rs2]',self.source)
        self.assertIn('| Decode.Beq rs1 rs2 sbimm12 => [rs1;rs2]',self.source)
        self.assertIn('Lemma requested_translation_frame',self.source)
        self.assertIn('pose proof(requested_translation_frame',self.source)

    def test_wrong_add_source_rejected_by_coq(self):
        original='| Decode.Add rd rs1 rs2 => [rs1;rs2]'
        self.assertEqual(self.source.count(original),1)
        mutated=self.source.replace(original,'| Decode.Add rd rs1 rs2 => [rs2;rs2]')
        with tempfile.TemporaryDirectory()as folder:
            path=Path(folder)/'WrongISAInputs.v';path.write_text(mutated)
            result=subprocess.run([str(self.root/'_opam/bin/coqc'),
                *certificate.synthesis.origin.pending.rtl.framework.FLAGS,str(path)],
                cwd=self.root,capture_output=True,text=True,timeout=120)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('Unable to unify',result.stderr)

    def test_extra_axiom_rejected(self):
        log='Closed under the global context\n'+('Axioms:\nFunctionalExtensionality.functional_extensionality_dep : T\n'*9)
        self.assertTrue(certificate.assumptions_expected(log))
        self.assertFalse(certificate.assumptions_expected(log+'cpu_is_correct : Prop\n'))

    def test_effect_batches_are_constructed_not_required(self):
        header=self.source.split('Theorem requested_values_from_history',1)[1].split('Proof.',1)[0]
        premises,conclusion=header.split('exists batches',1)
        self.assertNotIn('CertifiedBatches',premises)
        self.assertIn('CertifiedBatches',conclusion)
        self.assertIn('firstn index pending',premises)
        self.assertIn('requested_instruction j=true',premises)
        self.assertIn('map fst batches=firstn index pending',conclusion)
        self.assertIn('| Decode.Fence_i  => true',self.source)
        self.assertNotIn('| Decode.Fence pred succ => true',self.source)

    def test_pre_execution_read_does_not_assume_current_success(self):
        header=self.source.split('Theorem requested_values_before_execution',1)[1].split('Proof.',1)[0]
        self.assertNotIn('reference=Some after',header)
        self.assertNotIn('ExecuteI.execute',header)
        self.assertNotIn('Forall(fun address=>0<=address<32)',header)
        self.assertIn('exact(decoded_source_bounds (token_word token) i HD)',self.source)
        self.assertIn('Decode.RV32I(token_word token)',header)
        self.assertNotIn('CertifiedBatches',header.split('exists batches',1)[0])

    def test_register_32_cannot_be_admitted_by_totality(self):
        marker='Lemma legal_register_read'
        prefix,body=self.source.split(marker,1)
        mutated=prefix+marker+body.replace('0<=address<32','0<=address<33',1)
        with tempfile.TemporaryDirectory()as folder:
            path=Path(folder)/'InvalidRegisterBound.v';path.write_text(mutated)
            result=subprocess.run([str(self.root/'_opam/bin/coqc'),
                *certificate.synthesis.origin.pending.rtl.framework.FLAGS,str(path)],
                cwd=self.root,capture_output=True,text=True,timeout=120)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('Cannot find witness',result.stderr)
            self.assertFalse(path.with_suffix('.vo').exists())

    def test_values_use_exact_older_prefix_not_all_pending(self):
        header=self.source.split('Theorem requested_values_at_pending_cut',1)[1].split('Proof.',1)[0]
        self.assertIn('map fst batches=firstn index pending',header)
        self.assertIn('BeforeToken(instruction_effect',header)
        self.assertIn('CertifiedBatches',header)
        self.assertIn('ExecuteI.execute i reference',header)
        self.assertIn('owner_value 32(ISAView initial)batches address',header)

    def test_token_values_bound_to_original_fetch_not_arbitrary_execute(self):
        header=self.source.split('Theorem requested_token_values',1)[1].split('Proof.',1)[0]
        self.assertIn('Decode.decode Decode.RV32I(token_word token)',header)
        self.assertIn('instruction_effect token_pc token_word token reference=Some after',header)
        self.assertNotIn('ExecuteI.execute',header)
        self.assertNotIn('Forall(fun address=>0<=address<32)',header)
        self.assertIn('map fst batches=firstn index pending',header)

    def test_other_token_decode_rejected_by_coq(self):
        marker='Theorem requested_token_values'
        prefix,body=self.source.split(marker,1)
        body=body.replace('index token batches','index token (other:Token) batches',1)
        body=body.replace('Decode.RV32I(token_word token)','Decode.RV32I(token_word other)',1)
        with tempfile.TemporaryDirectory()as folder:
            path=Path(folder)/'WrongTokenValues.v';path.write_text(prefix+marker+body)
            result=subprocess.run([str(self.root/'_opam/bin/coqc'),
                *certificate.synthesis.origin.pending.rtl.framework.FLAGS,str(path)],
                cwd=self.root,capture_output=True,text=True,timeout=120)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('while it is expected to have type',result.stderr)
            self.assertIn('token_word other',result.stderr)
            self.assertFalse(path.with_suffix('.vo').exists())

    def test_younger_suffix_cannot_replace_older_prefix(self):
        marker='Theorem requested_values_from_history'
        prefix,body=self.source.split(marker,1)
        body=body.replace('(firstn index pending) ->','(skipn index pending) ->',1)
        with tempfile.TemporaryDirectory()as folder:
            path=Path(folder)/'WrongEffectPrefix.v';path.write_text(prefix+marker+body)
            result=subprocess.run([str(self.root/'_opam/bin/coqc'),
                *certificate.synthesis.origin.pending.rtl.framework.FLAGS,str(path)],
                cwd=self.root,capture_output=True,text=True,timeout=120)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('while it is expected to have type',result.stderr)
            self.assertIn('skipn index pending',result.stderr)
            self.assertFalse(path.with_suffix('.vo').exists())


if __name__=='__main__':unittest.main()
