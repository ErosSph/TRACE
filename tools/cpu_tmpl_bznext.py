#!/usr/bin/env python3
"""ISA next pc of the ID token per branch class (module BzTmplNext): per class `np_<C>` generated from the class table, composed with the hand core in
framework/template-sources/bz/BzTmplNext.v.in.  Untrusted generator; Coq checks everything.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import sys
from pathlib import Path
import cpu_isa_classes as isa

BR = [c['name'] for c in isa.classes() if c['group'] == 'BRANCH']


def lemma(cl):
    return f'''Lemma np_{cl} seed d t c post rs1 rs2 imm w :
 CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 32 (read_signal d 139%nat) = t ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.{cl} rs1 rs2 imm) ->
 Id.IC d (Decode.{cl} rs1 rs2 imm) -> OpsOK d c (Decode.{cl} rs1 rs2 imm) ->
 t = uw (getPc c) -> t mod 4 = 0 -> getNextPc c = JE.link c -> post = BE.branch_post c (Decode.{cl} rs1 rs2 imm) ->
 (norm 1 (read_signal d 157%nat) = 0 -> uw (getPc post) = norm 32 (t + 4)) /\\ (norm 1 (read_signal d 157%nat) <> 0 -> uw (getPc post) = norm 32 (read_signal d 130%nat)).
Proof. intros HL Hw Ht Hdec HI [Hx Hy] Htc Ht4 HN Hp.
 pose proof (Id.br_{cl} seed d (formal_register_word c rs1) (formal_register_word c rs2) rs1 rs2 imm HL HI Hx Hy) as [A [B C]].
 destruct HI as [_ [_ [H168 _]]]. cbn in H168.
 destruct (Inv.inv_{cl} w rs1 rs2 imm Hdec) as [[_ [_ Himm]] [Hop _]].
 assert (Hlink : uw (getNextPc c) = norm 32 (t + 4)) by (rewrite HN, JE.link_unsigned, ExtendedSVBankAlignment.norm_mod; rewrite Htc; reflexivity).
 assert (Hg : BE.reference_branch_taken c (Decode.{cl} rs1 rs2 imm) = isa_branch_guard (Decode.{cl} rs1 rs2 imm) (formal_register_word c rs1) (formal_register_word c rs2)) by reflexivity.
 destruct (isa_branch_guard (Decode.{cl} rs1 rs2 imm) (formal_register_word c rs1) (formal_register_word c rs2)) eqn:Eg; cbn in A, B.
 - split.
   + intro H157. rewrite A in H157. discriminate H157.
   + intros _. rewrite Hp. unfold BE.branch_post. cbn [getPc]. unfold BE.branch_next_pc. rewrite Hg.
     unfold BE.reference_branch_target. cbn [BE.branch_immediate immediate_field]. rewrite uw_add_of_Z.
     assert (Hpc4 : Z.testbit (norm 32 (read_signal d 139%nat)) 0 = false) by (rewrite Ht; apply testbit0_aligned; exact Ht4).
     rewrite (Ex.{cl}_e3 seed d w HL B C Hw Hop H168 Hpc4). rewrite Ht, <- Htc. rewrite Himm. reflexivity.
 - split.
   + intros _. rewrite Hp. unfold BE.branch_post. cbn [getPc]. unfold BE.branch_next_pc. rewrite Hg. exact Hlink.
   + intro H157. rewrite A in H157. contradiction.
Qed.
'''


def build(template):
    t = Path(template).read_text()
    return t.replace('@BR_LEMMAS@', '\n'.join(lemma(c) for c in BR))


if __name__ == '__main__':
    Path(sys.argv[2]).write_text(build(sys.argv[1]))
