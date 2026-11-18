import unittest
from pathlib import Path
from unittest.mock import patch
import cpu_covered_write_destination as r


class CoveredDestinationTests(unittest.TestCase):
    def source(self,with_validity=False,boot=False):
        target=dict(endpoint=7,roots=[7],aliases=[],head=dict(source=1))
        data=dict(coverage=dict(covered_fields=[dict(root=7,valid_root=9)]))
        branch=dict(bank=100,total=1024,index_root=7,process='writer',guards=[],
                    data='(EVar 32 8)',offset='(EBinary 12 BMul (EVar 5 7) (EConst 12 32))',
                    index=dict(rule='multiply_index',index='(EVar 5 7)'))
        validity=None
        if with_validity:
            guard='(EBinary 1 BAnd (EVar 1 8) (EBinary 1 BNeq (EConst 5 0) (EVar 5 7)))'
            branch['guards']=[(guard,True)]
            validity=dict(entry=dict(capture=dict(carrier=1,valid_root=2)),
                          rows=[dict(rd=7,write=8,valid=9)],write_guard=guard)
        with patch.object(r.history.chain,'discover',return_value=dict(rows=[dict(root=7)])):
            return r.render(dict(module='Raw'),dict(ast=dict(module='Raw.AST',program='Raw.program')),
                            target,data,branch,{},validity,boot)

    def test_boot_corollary_constructs_relations_and_lfp(self):
        source=self.source(True,True)
        goal=source.split('Theorem actual_write_destination_from_boot',1)[1].split('Proof.',1)[0]
        before=goal.split('exists token',1)[0]
        for forbidden in ['CoveredCapturedFields','WriteValidityInvariant','CombLFP','CoveredExecution']:
            self.assertNotIn(forbidden,before)
        self.assertIn('Forall HB.W.Environment events',before)
        self.assertIn('catalog_phase_evidence',source)
        self.assertIn('HB.boot_and_runtime_related image events HE',source)

    def test_boot_requires_validity_provider(self):
        with self.assertRaisesRegex(ValueError,'requires checked write validity'):
            self.source(False,True)

    def test_terminal_validity_is_derived_from_preserved_relation(self):
        source=self.source(True)
        goal=source.split('Theorem actual_write_destination_from_relation',1)[1].split('Proof.',1)[0]
        before,after=goal.split('exists token',1)
        self.assertNotIn('norm 1(read_signal pre 9)<>0%Z',before)
        self.assertIn('WV.WriteValidityInvariant pre',before)
        self.assertIn('WV.actual_write_branch_valid seed ev pre HB HL HI HG0',source)
        self.assertIn('C.chain_tag0(snd packed)=Some token',after)

    def test_witness_is_conclusion_not_assumption(self):
        source=self.source()
        goal=source.split('Theorem valid_actual_write_destination',1)[1].split('Proof.',1)[0]
        before,after=goal.split('exists token',1)
        self.assertNotIn('chain_tag',before)
        self.assertNotIn('Some token',before)
        self.assertIn('C.chain_tag0(snd packed)=Some token',after)
        self.assertIn('norm 1(read_signal pre 9)<>0%Z',before)

    def test_isa_decode_belongs_to_extracted_token(self):
        source=self.source()
        self.assertIn('Lang.ExtendedSVCaptureBirth.',source)
        self.assertIn('Decode.decode Decode.RV32I(token_word token)',source)
        self.assertIn('original_destination_address(token_word token)',source)
        self.assertIn('valid_field_0_has_value pre packed HR HV',source)

    def test_history_preservation_is_used_not_asserted(self):
        source=self.source()
        self.assertIn('covered_capture_history initial initial_tags events pre packed HX HI',source)
        self.assertIn('sampled_root_preserved Raw.program',source)
        self.assertIn('C.root_7_projection_certificate',source)
        self.assertIn('f_equal (norm 5)(sampled_root_preserved',source)

    def test_emission_does_not_read_old_cpu_proofs(self):
        with patch.object(Path,'read_text',side_effect=AssertionError('old proof lookup')):
            source=self.source()
        self.assertNotIn('Admitted',source)
        self.assertNotIn('Axiom ',source)


if __name__=='__main__':unittest.main()
