(** Fetch-address alignment (design independent, template route, 2026-11-03).
    [align2_expr r] is the Verilog [{r[31:1], 1'b0}]; [eval_align2]: it clears bit 0 of the word (JALR target [& ~1]).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBankAlignment Lang.ExtendedSVPackedROM Lang.ExtendedSVWordInvariant Lang.ExtendedSVSliceBits.
Import ListNotations ExtendedSV ExtendedSVBankAlignment ExtendedSVPackedROM ExtendedSVWordInvariant ExtendedSVSliceBits.
Local Open Scope Z_scope.
Module CPUFetchAlign.

(** Fetch-address alignment: [{x[31:1], 1'b0}] clears bit 0 of a word (JALR target [& ~1]). *)
Definition align2_expr (r:signal) : Expr := EConcat 32 (ESel 31 (EVar 32 r) (EConst 5 1)) (EConst 1 0).
Lemma eval_align2 s r x : norm 32 (read_signal s r) = x ->
 eval_expr s (align2_expr r) = Z.land x (Z.lnot 1).
Proof.
 intros Hx. unfold align2_expr. cbn [eval_expr expr_width]. rewrite Hx. change (norm 5 1) with 1. change (norm 1 0) with 0. change (Z.of_nat 1) with 1.
 assert (Hr : 0 <= x < 4294967296) by (rewrite <- Hx; pose proof (norm_bounds 32 (read_signal s r)); change (2 ^ Z.of_nat 32) with 4294967296 in *; lia).
 apply Z.bits_inj'. intros i Hi.
 rewrite testbit_norm by lia. change (Z.of_nat 32) with 32.
 rewrite Z.lor_spec, Z.land_spec, Z.lnot_spec by lia.
 rewrite Z.bits_0, orb_false_r.
 destruct (Z.eq_dec i 0) as [->|Hi0].
 - rewrite Z.shiftl_spec_low by lia. destruct (Z.testbit x 0); reflexivity.
 - rewrite Z.shiftl_spec by lia. rewrite testbit_norm by lia. change (Z.of_nat 31) with 31.
   rewrite Z.shiftr_spec by lia. replace (i - 1 + 1) with i by lia.
   assert (Hb : Z.testbit 1 i = false) by (apply Z.bits_above_log2; [lia|]; change (Z.log2 1) with 0; lia).
   rewrite Hb. cbn [negb].
   destruct (Z.ltb_spec (i - 1) 31) as [H31|H31].
   + assert (E2 : (i <? 32) = true) by (apply Z.ltb_lt; lia).
     rewrite E2. destruct (Z.testbit x i); reflexivity.
   + destruct (Z.ltb_spec i 32) as [H32|H32]; [lia|].
     cbn.
     replace (Z.testbit x i) with false; [reflexivity|].
     symmetry. apply Z.bits_above_log2; [lia|].
     assert (Z.log2 x < 32).
     { destruct (Z.eq_dec x 0) as [Hz|Hz]; [rewrite Hz; rewrite Z.log2_nonpos by lia; lia|]. apply Z.log2_lt_pow2; lia. }
     lia.
Qed.
End CPUFetchAlign.
Print Assumptions CPUFetchAlign.eval_align2.
