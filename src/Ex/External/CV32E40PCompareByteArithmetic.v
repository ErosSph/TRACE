(** Exact nine-bit signed comparison encodings used by RTL bytes. The
    ninth bit is a selected sign bit, not an ISA oracle. *)
From Coq Require Import ZArith Lia Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice
  Ex.External.CV32E40PAddiAdder Ex.External.CV32E40PAddiAdderBits
  Ex.External.CV32E40PAddiIDEXAccept Ex.External.CV32E40PCompareWordPacking.
Import ExtendedSV ExtendedSVBitSlice CV32E40PAddiAdder CV32E40PAddiAdderBits
  CV32E40PAddiIDEXAccept CV32E40PCompareWordPacking.
Local Open Scope Z_scope.
Module CV32E40PCompareByteArithmetic.

Lemma single_bit_range x off : 0 <= off -> 0 <= read_slice x off 1 <= 1.
Proof.
  intros. rewrite slice_div by lia. change (2^1) with 2.
  pose proof (Z.mod_pos_bound (x / 2^off) 2 ltac:(lia)). lia.
Qed.
Lemma signed_byte_from_sign v : 0 <= v < 256 ->
  signed_value 8 v = v - 256 * read_slice v 7 1.
Proof.
  intros HB. unfold signed_value. cbn [Nat.eqb Nat.pred].
  rewrite (norm_small 8 v ltac:(change (2^Z.of_nat 8) with 256; exact HB)).
  change (Z.of_nat 7) with 7. change (2^Z.of_nat 8) with 256.
  rewrite Z.testbit_eqb by lia. rewrite slice_div by lia.
  change (2^7) with 128. change (2^1) with 2.
  pose proof (Z.mod_pos_bound (v/128) 2 ltac:(lia)) as HM.
  destruct (Z.eqb (v/128 mod 2) 1) eqn:HE;
    [apply Z.eqb_eq in HE|apply Z.eqb_neq in HE]; lia.
Qed.

Lemma signed_nine_concat v bit : 0 <= v < 256 -> (bit = 0 \/ bit = 1) ->
  signed_value 9 (norm 9 (Z.lor (Z.shiftl bit 8) v)) = v - 256*bit.
Proof.
  intros HB HH. rewrite concat_arith by lia.
  change (2^8) with 256. unfold signed_value. cbn [Nat.eqb Nat.pred].
  rewrite norm_twice, (norm_small 9 (256*bit+v)
    ltac:(change (2^Z.of_nat 9) with 512; destruct HH; subst; lia)).
  change (Z.of_nat 8) with 8. change (2^Z.of_nat 9) with 512.
  rewrite Z.testbit_eqb by lia. change (2^8) with 256.
  destruct HH as [->| ->].
  - replace ((256*0+v)/256) with 0 by (symmetry; apply Z.div_small; exact HB).
    rewrite Z.mod_0_l by lia. change (0 =? 1) with false. lia.
  - assert ((256*1+v)/256 = 1) as HD.
    { symmetry. apply (Z.div_unique _ _ 1 v); [left; exact HB|ring]. }
    rewrite HD, Z.mod_small by lia. change (1 =? 1) with true. lia.
Qed.

Lemma byte_sign_slice x off : 0 <= off ->
  read_slice (byte_at x off) 7 1 = read_slice x (off+7) 1.
Proof.
  intros HO. change (read_slice (norm 8 (Z.shiftr x off)) 7 1 =
    read_slice x (off+7) 1).
  rewrite slice_norm by lia. unfold read_slice.
  rewrite Z.shiftr_shiftr by lia. replace (off+7) with (7+off) by lia. reflexivity.
Qed.

Definition compare_byte_value x off mode :=
  signed_value 9 (norm 9 (Z.lor
    (Z.shiftl (norm 1 (Z.land (read_slice x (off+7) 1) mode)) 8)
    (byte_at x off))).

Theorem unsigned_comparison_byte x off : 0 <= off ->
  compare_byte_value x off 0 = byte_at x off.
Proof.
  intros HO. unfold compare_byte_value. rewrite Z.land_0_r.
  change (norm 1 0) with 0. rewrite signed_nine_concat;
    [ring|apply byte_range; exact HO|auto].
Qed.
Theorem signed_comparison_byte x off : 0 <= off ->
  compare_byte_value x off 1 = signed_value 8 (byte_at x off).
Proof.
  intros HO. unfold compare_byte_value.
  change (Z.land (read_slice x (off+7) 1) 1) with (norm 1 (read_slice x (off+7) 1)).
  rewrite norm_twice.
  change (norm 1 (read_slice x (off+7) 1)) with
    (norm 1 (norm 1 (Z.shiftr x (off+7)))).
  rewrite norm_twice.
  change (norm 1 (Z.shiftr x (off+7))) with (read_slice x (off+7) 1).
  pose proof (single_bit_range x (off+7) ltac:(lia)) as HR.
  rewrite signed_nine_concat by (try apply byte_range; lia).
  rewrite signed_byte_from_sign by (apply byte_range; exact HO).
  rewrite byte_sign_slice by exact HO. reflexivity.
Qed.
Print Assumptions signed_nine_concat.
Print Assumptions unsigned_comparison_byte.
Print Assumptions signed_comparison_byte.
End CV32E40PCompareByteArithmetic.
