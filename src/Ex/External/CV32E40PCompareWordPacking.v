(** Relate the byte comparator's most-significant signed byte and three
    unsigned low bytes to the actual 32-bit word interpretation. *)
From Coq Require Import ZArith Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice
  Ex.External.CV32E40PAddiAdder Ex.External.CV32E40PAddiAdderBits
  Ex.External.CV32E40PAddiIDEXAccept Ex.External.CV32E40PCompareLexArithmetic.
Import ExtendedSV ExtendedSVBitSlice CV32E40PAddiAdder CV32E40PAddiAdderBits
  CV32E40PAddiIDEXAccept CV32E40PCompareLexArithmetic.
Local Open Scope Z_scope.
Module CV32E40PCompareWordPacking.

Definition byte_at (x off : Z) := read_slice x off 8.
Lemma byte_range x off : 0 <= off -> 0 <= byte_at x off < 256.
Proof.
  intros HO. unfold byte_at. rewrite slice_div by lia.
  change (2^8) with 256. apply Z.mod_pos_bound. lia.
Qed.
Lemma byte_normalized x off : norm 8 (byte_at x off) = byte_at x off.
Proof.
  change (norm 8 (norm 8 (Z.shiftr x off)) = norm 8 (Z.shiftr x off)).
  apply norm_twice.
Qed.

Theorem unsigned_word_is_packed_bytes x :
  norm 32 x = pack4 (byte_at x 24) (byte_at x 16) (byte_at x 8) (byte_at x 0).
Proof.
  pose proof (split_slice x 0 8 24 ltac:(lia) ltac:(lia) ltac:(lia)) as H0.
  pose proof (split_slice x 8 8 16 ltac:(lia) ltac:(lia) ltac:(lia)) as H8.
  pose proof (split_slice x 16 8 8 ltac:(lia) ltac:(lia) ltac:(lia)) as H16.
  change (8+24) with 32 in H0. change (0+8) with 8 in H0.
  change (8+16) with 24 in H8. change (8+8) with 16 in H8.
  change (8+8) with 16 in H16. change (16+8) with 24 in H16.
  change (2^8) with 256 in H0, H8, H16.
  unfold byte_at, pack4.
  replace (norm 32 x) with (read_slice x 0 32)
    by (unfold read_slice; rewrite Z.shiftr_0_r; reflexivity).
  rewrite H0, H8, H16. ring.
Qed.

Lemma top_byte_sign x :
  Z.testbit (norm 8 (byte_at x 24)) 7 = Z.testbit (norm 32 x) 31.
Proof.
  unfold byte_at, read_slice, norm, mask. rewrite !Z.land_spec.
  change (Z.testbit (2^8-1) 7) with true.
  change (Z.testbit (2^Z.of_nat 8-1) 7) with true.
  change (Z.testbit (2^Z.of_nat 32-1) 31) with true.
  cbn [andb]. rewrite Z.shiftr_spec by lia.
  replace (7+24) with 31 by lia. now rewrite !Bool.andb_true_r.
Qed.

Theorem signed_word_is_packed_bytes x :
  signed_value 32 x =
    pack4 (signed_value 8 (byte_at x 24)) (byte_at x 16) (byte_at x 8) (byte_at x 0).
Proof.
  unfold signed_value. cbn [Nat.eqb Nat.pred].
  change (Z.of_nat 31) with 31. change (Z.of_nat 7) with 7.
  rewrite top_byte_sign, byte_normalized.
  destruct (Z.testbit (norm 32 x) 31);
    rewrite unsigned_word_is_packed_bytes; unfold pack4;
    change (2^Z.of_nat 32) with 4294967296;
    change (2^Z.of_nat 8) with 256; ring.
Qed.

Theorem unsigned_byte_lex_less a b :
  negb (orb
    (greater4 (byte_at a 24) (byte_at a 16) (byte_at a 8) (byte_at a 0)
              (byte_at b 24) (byte_at b 16) (byte_at b 8) (byte_at b 0))
    (equal4 (byte_at a 24) (byte_at a 16) (byte_at a 8) (byte_at a 0)
            (byte_at b 24) (byte_at b 16) (byte_at b 8) (byte_at b 0))) =
    Z.ltb (norm 32 a) (norm 32 b).
Proof.
  rewrite scalar_less_is_word_less by (apply byte_range; lia).
  now rewrite <- !unsigned_word_is_packed_bytes.
Qed.

Theorem signed_byte_lex_less a b :
  negb (orb
    (greater4 (signed_value 8 (byte_at a 24)) (byte_at a 16) (byte_at a 8) (byte_at a 0)
              (signed_value 8 (byte_at b 24)) (byte_at b 16) (byte_at b 8) (byte_at b 0))
    (equal4 (signed_value 8 (byte_at a 24)) (byte_at a 16) (byte_at a 8) (byte_at a 0)
            (signed_value 8 (byte_at b 24)) (byte_at b 16) (byte_at b 8) (byte_at b 0))) =
    Z.ltb (signed_value 32 a) (signed_value 32 b).
Proof.
  rewrite scalar_less_is_word_less by (apply byte_range; lia).
  now rewrite <- !signed_word_is_packed_bytes.
Qed.
Print Assumptions unsigned_word_is_packed_bytes.
Print Assumptions signed_word_is_packed_bytes.
Print Assumptions unsigned_byte_lex_less.
Print Assumptions signed_byte_lex_less.
End CV32E40PCompareWordPacking.
