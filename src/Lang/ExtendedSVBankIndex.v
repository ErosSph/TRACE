(** Exact register index behind common packed-bank address encodings.
    Alignment alone is insufficient: truncation may select a different lane. *)
From Coq Require Import ZArith Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBankAlignment.
Import ExtendedSV ExtendedSVBankAlignment.
Local Open Scope Z_scope.
Module ExtendedSVBankIndex.

Lemma norm_small_index w value:
 (5<=w)%nat ->0<=value<32 ->norm w value=value.
Proof.
 intros HW HV;rewrite norm_mod;apply Z.mod_small.
 assert(HP:32<=2^Z.of_nat w).
 { change(2^5<=2^Z.of_nat w);apply Z.pow_le_mono_r;lia. }
 lia.
Qed.
Lemma norm_small_offset w value:
 (10<=w)%nat ->0<=value<1024 ->norm w value=value.
Proof.
 intros HW HV;rewrite norm_mod;apply Z.mod_small.
 assert(HP:1024<=2^Z.of_nat w).
 { change(2^10<=2^Z.of_nat w);apply Z.pow_le_mono_r;lia. }
 lia.
Qed.
Theorem multiply_index s width index scale:
 (10<=width)%nat ->(expr_width index<=5)%nat ->literal_eqb scale 32=true ->
 eval_expr s(EBinary width BMul index scale)/32=eval_expr s index.
Proof.
 intros HW HI HC;pose proof(small_operand_bound index s HI)as HB.
 cbn[eval_expr];rewrite(literal_eqb_sound scale 32 HC s).
 rewrite norm_small_offset by lia.
 apply Z.div_mul;lia.
Qed.
Theorem multiply_index_left s width index scale:
 (10<=width)%nat ->(expr_width index<=5)%nat ->literal_eqb scale 32=true ->
 eval_expr s(EBinary width BMul scale index)/32=eval_expr s index.
Proof.
 intros HW HI HC;pose proof(small_operand_bound index s HI)as HB.
 cbn[eval_expr];rewrite(literal_eqb_sound scale 32 HC s),Z.mul_comm.
 rewrite norm_small_offset by lia;apply Z.div_mul;lia.
Qed.
Theorem shifted_index s root:
 eval_expr s(ESel 10
  (EBinary 32 BShiftL(EExtend 32 false(EVar 5 root))(EConst 32 5))
  (EConst 32 0))/32=norm 5(read_signal s root).
Proof.
 pose proof(norm_bounds 5(read_signal s root))as HB.
 change(0<=norm 5(read_signal s root)<32)in HB.
 cbn[eval_expr].
 change(norm 10(Z.shiftr(norm 32(Z.shiftl(norm 32(norm 5(read_signal s root)))5))0)/32=
  norm 5(read_signal s root)).
 rewrite(norm_small_index 32 (norm 5(read_signal s root)) ltac:(lia) HB).
 rewrite Z.shiftl_mul_pow2 by lia;rewrite Z.shiftr_0_r.
 change(norm 10(norm 32(norm 5(read_signal s root)*32))/32=norm 5(read_signal s root)).
 rewrite(norm_small_offset 32 (norm 5(read_signal s root)*32) ltac:(lia) ltac:(lia)).
 rewrite norm_small_offset by lia;apply Z.div_mul;lia.
Qed.
End ExtendedSVBankIndex.
Print Assumptions ExtendedSVBankIndex.multiply_index.
Print Assumptions ExtendedSVBankIndex.shifted_index.
