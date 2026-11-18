(** Width/sign/concatenation facts for the actual scalar ALU network. *)
From Coq Require Import ZArith Lia Bool btauto.Btauto.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice Ex.External.CV32E40PAddiAdder.
Import ExtendedSV ExtendedSVBitSlice CV32E40PAddiAdder.
Local Open Scope Z_scope.
Module CV32E40PAddiAdderBits.
  Lemma slice_norm x total off width :
    0 <= off -> 0 <= width -> off+width <= Z.of_nat total ->
    read_slice (norm total x) off width = read_slice x off width.
  Proof.
    intros Ho Hw Ht. apply Z.bits_inj. intros bit.
    destruct (Z_lt_ge_dec bit 0).
    - now rewrite !Z.testbit_neg_r by lia.
    - unfold read_slice. rewrite !Z.land_spec.
      destruct (Z_lt_ge_dec bit width).
      + rewrite mask_bit_low by lia. rewrite !Bool.andb_true_r.
        rewrite !Z.shiftr_spec by lia. unfold norm, mask.
        rewrite Z.land_spec, mask_bit_low by lia. now rewrite Bool.andb_true_r.
      + rewrite mask_bit_high by lia. now rewrite !Bool.andb_false_r.
  Qed.
  Lemma unpack_slices x : unpack x = read_slice x 1 8 +
    256*read_slice x 10 8 + 65536*read_slice x 19 8 + 16777216*read_slice x 28 8.
  Proof. rewrite !slice_div by lia. reflexivity. Qed.
  Lemma unpack_norm x w : (36 <= w)%nat -> unpack (norm w x) = unpack x.
  Proof. intros H. rewrite !unpack_slices, !slice_norm by lia. reflexivity. Qed.

  Lemma concat_arith hi lo n : 0 <= n -> 0 <= lo < 2^n ->
    Z.lor (Z.shiftl hi n) lo = 2^n*hi+lo.
  Proof.
    intros Hn Hlo.
    assert (D : Z.land (Z.shiftl hi n) lo = 0).
    { apply Z.bits_inj. intros bit. rewrite Z.land_spec, Z.bits_0.
      destruct (Z_lt_ge_dec bit 0).
      - rewrite !Z.testbit_neg_r by lia. reflexivity.
      - destruct (Z_lt_ge_dec bit n).
        + rewrite Z.shiftl_spec by lia. rewrite Z.testbit_neg_r by lia. reflexivity.
        + assert (L : lo = Z.land lo (2^n-1)).
          { replace (2^n-1) with (Z.ones n) by (rewrite Z.ones_equiv; lia).
            rewrite Z.land_ones by lia. symmetry. now apply Z.mod_small. }
          rewrite L at 1. rewrite Z.land_spec, mask_bit_high by lia. btauto. }
    rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D.
    rewrite Z.shiftl_mul_pow2 by lia. ring.
  Qed.
  Lemma norm_range w x : 0 <= norm w x < 2^Z.of_nat w.
  Proof. rewrite norm_mod. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.
  Lemma norm_small w x : 0 <= x < 2^Z.of_nat w -> norm w x = x.
  Proof. rewrite norm_mod. apply Z.mod_small. Qed.

  Lemma signed_mod36 a b :
    norm 36 (norm 37 (norm 37 (signed_value 36 a) + norm 37 (signed_value 36 b))) =
    norm 36 (a+b).
  Proof.
    unfold signed_value. cbn [Nat.eqb Nat.pred]. change (Z.of_nat 35) with 35.
    destruct (Z.testbit (norm 36 a) 35); destruct (Z.testbit (norm 36 b) 35);
      rewrite !norm_mod; change (2^Z.of_nat 36) with 68719476736;
      change (2^Z.of_nat 37) with 137438953472; div_lia.
  Qed.
End CV32E40PAddiAdderBits.
