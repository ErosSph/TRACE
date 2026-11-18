(** Bit-level contracts for the EXISTING normalized SV expression semantics.
    Pure equality lemmas: no alternative evaluator or hardware behaviour.
    These permit symbolic reasoning about discontinuous ISA immediates. *)
From Coq Require Import ZArith Bool Lia.
Require Import Lang.ExtendedSV coqutil.Z.bitblast coqutil.Z.BitOps.
Import ExtendedSV.
Local Open Scope Z_scope.
Module ExtendedSVConcatBits.

Lemma norm_bit width value bit : 0 <= bit ->
  Z.testbit (norm width value) bit =
    andb (Z.testbit value bit) (bit <? Z.of_nat width).
Proof.
  intros Hbit. unfold norm, mask.
  replace (2 ^ Z.of_nat width - 1) with (Z.ones (Z.of_nat width))
    by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_spec, Z.testbit_ones_nonneg by lia. reflexivity.
Qed.

Theorem concat_bit high_width low_width high low bit : 0 <= bit ->
  Z.testbit (norm (high_width + low_width)
    (Z.lor (Z.shiftl (norm high_width high) (Z.of_nat low_width))
      (norm low_width low))) bit =
  if bit <? Z.of_nat low_width then Z.testbit low bit
  else if bit <? Z.of_nat (high_width + low_width)
    then Z.testbit high (bit - Z.of_nat low_width) else false.
Proof.
  intros Hbit. rewrite norm_bit by lia. rewrite Z.lor_spec.
  destruct (Z.ltb_spec bit (Z.of_nat low_width)) as [Hlow|Hlow].
  - rewrite Z.shiftl_spec_low by lia. rewrite norm_bit by lia.
    assert (EL : (bit <? Z.of_nat low_width) = true) by (apply Z.ltb_lt; lia).
    assert (ET : (bit <? Z.of_nat (high_width + low_width)) = true).
    { apply Z.ltb_lt. rewrite Nat2Z.inj_add. lia. }
    rewrite EL, ET. cbn. rewrite !andb_true_r.
    destruct (Z.testbit low bit); reflexivity.
  - rewrite Z.shiftl_spec_high by lia. rewrite !norm_bit by lia.
    assert (EL : (bit <? Z.of_nat low_width) = false) by (apply Z.ltb_ge; lia).
    rewrite EL, andb_false_r, orb_false_r.
    destruct (Z.ltb_spec bit (Z.of_nat (high_width + low_width))) as [Htotal|Htotal].
    + assert (EH : (bit - Z.of_nat low_width <? Z.of_nat high_width) = true).
      { apply Z.ltb_lt. rewrite Nat2Z.inj_add in Htotal. lia. }
      rewrite EH, !andb_true_r. reflexivity.
    + assert (EH : (bit - Z.of_nat low_width <? Z.of_nat high_width) = false).
      { apply Z.ltb_ge. rewrite Nat2Z.inj_add in Htotal. lia. }
      rewrite EH, andb_false_r. reflexivity.
Qed.

Lemma concat_low_bit high_width low_width high low bit :
  0 <= bit < Z.of_nat low_width ->
  Z.testbit (norm (high_width + low_width)
    (Z.lor (Z.shiftl (norm high_width high) (Z.of_nat low_width)) (norm low_width low))) bit =
  Z.testbit (norm low_width low) bit.
Proof.
  intros Hb. rewrite concat_bit, norm_bit by lia.
  assert (E : (bit <? Z.of_nat low_width) = true) by (apply Z.ltb_lt; lia).
  now rewrite E, andb_true_r.
Qed.

Lemma concat_high_bit high_width low_width high low bit :
  Z.of_nat low_width <= bit < Z.of_nat (high_width + low_width) ->
  Z.testbit (norm (high_width + low_width)
    (Z.lor (Z.shiftl (norm high_width high) (Z.of_nat low_width)) (norm low_width low))) bit =
  Z.testbit (norm high_width high) (bit - Z.of_nat low_width).
Proof.
  intros Hb. rewrite concat_bit by lia. rewrite norm_bit.
  2:{ lia. }
  assert (EL : (bit <? Z.of_nat low_width) = false) by (apply Z.ltb_ge; lia).
  assert (ET : (bit <? Z.of_nat (high_width + low_width)) = true) by (apply Z.ltb_lt; lia).
  assert (EH : (bit - Z.of_nat low_width <? Z.of_nat high_width) = true).
  { apply Z.ltb_lt. rewrite Nat2Z.inj_add in Hb. lia. }
  now rewrite EL, ET, EH, andb_true_r.
Qed.

Theorem signed_concat_is_reference extension_width source_width value :
  (0 < source_width)%nat ->
  norm (extension_width + source_width)
    (Z.lor (Z.shiftl (norm extension_width
       (if Z.testbit value (Z.of_nat source_width - 1)
        then Z.ones (Z.of_nat extension_width) else 0)) (Z.of_nat source_width))
      (norm source_width value)) =
  norm (extension_width + source_width) (BitOps.signExtend (Z.of_nat source_width) value).
Proof.
  intros Hwidth. rewrite BitOps.signExtend_alt_bitwise by lia.
  unfold BitOps.signExtend_bitwise.
  destruct (Z.testbit value (Z.of_nat source_width - 1)).
  - apply Z.bits_inj. intros bit. destruct (Z_lt_ge_dec bit 0) as [Hneg|Hbit].
    + rewrite !Z.testbit_neg_r by lia. reflexivity.
    + rewrite concat_bit by lia. rewrite norm_bit by lia.
      rewrite Z.lor_spec, Z.land_spec.
      rewrite (Z.testbit_ones_nonneg (Z.of_nat source_width) bit ltac:(lia) ltac:(lia)).
      destruct (Z.ltb_spec bit (Z.of_nat source_width)) as [Hlow|Hlow].
      * rewrite Z.shiftl_spec_low by lia. rewrite orb_false_r, andb_true_r.
        assert (ET : (bit <? Z.of_nat (extension_width + source_width)) = true).
        { apply Z.ltb_lt. rewrite Nat2Z.inj_add. lia. }
        now rewrite ET, andb_true_r.
      * rewrite Z.shiftl_spec_high, Z.testbit_minus1 by lia.
        rewrite andb_false_r, orb_true_r.
        destruct (Z.ltb_spec bit (Z.of_nat (extension_width + source_width))) as [HT|HT].
        -- rewrite Z.ones_spec_low; [reflexivity|]. rewrite Nat2Z.inj_add in HT. lia.
        -- reflexivity.
  - apply Z.bits_inj. intros bit. destruct (Z_lt_ge_dec bit 0) as [Hneg|Hbit].
    + rewrite !Z.testbit_neg_r by lia. reflexivity.
    + rewrite concat_bit by lia. rewrite norm_bit by lia.
      rewrite Z.land_spec, Z.testbit_ones_nonneg by lia.
      destruct (Z.ltb_spec bit (Z.of_nat source_width)) as [Hlow|Hlow].
      * rewrite andb_true_r.
        assert (ET : (bit <? Z.of_nat (extension_width + source_width)) = true).
        { apply Z.ltb_lt. rewrite Nat2Z.inj_add. lia. }
        now rewrite ET, andb_true_r.
      * rewrite andb_false_r, Z.testbit_0_l.
        destruct (bit <? Z.of_nat (extension_width + source_width)); reflexivity.
Qed.

Print Assumptions concat_bit.
Print Assumptions signed_concat_is_reference.
End ExtendedSVConcatBits.
