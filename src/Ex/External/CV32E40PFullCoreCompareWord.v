(** Actual FullCore scalar comparator outputs agree with mathematical
    signed/unsigned words. Observed byte bits are derived from the original
    expression and wiring certificates, not supplied as ISA expectations. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice
  Ex.External.CV32E40PCompareExpressionIdentity Ex.External.CV32E40PCompareFullCoreBytes
  Ex.External.CV32E40PCompareFullCoreOutput Ex.External.CV32E40PCompareByteArithmetic
  Ex.External.CV32E40PCompareWordPacking Ex.External.CV32E40PCompareLexArithmetic
  Ex.External.CV32E40PCompareSignedByteEquality Ex.External.CV32E40PAddiAdderBits
  Ex.External.CV32E40PAddiOperandCone.
Import ExtendedSV ExtendedSVBitSlice CV32E40PCompareExpressionIdentity
  CV32E40PCompareFullCoreBytes CV32E40PCompareFullCoreOutput CV32E40PCompareByteArithmetic
  CV32E40PCompareWordPacking CV32E40PCompareLexArithmetic CV32E40PCompareSignedByteEquality
  CV32E40PAddiAdderBits CV32E40PAddiOperandCone.
Local Open Scope Z_scope.
Local Opaque read_signal round.
Module CV32E40PFullCoreCompareWord.
(* Normalize only numeral indices in a specialized wiring equality. *)
Ltac rewrite_indexed lemma :=
  let H := fresh "Hindex" in
  pose proof lemma as H;
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Nat.add Nat.mul] in H;
  rewrite H; clear H.
Lemma boolz_injective a b : boolz a = boolz b -> a = b.
Proof. destruct a,b; cbn [boolz]; congruence. Qed.
Lemma actual_equal_byte_boolean s n : (n < 4)%nat ->
  observed_bit (round s) 1353%nat (Z.of_nat n) =
    Z.eqb (byte_at (read_signal (round s) 1304%nat) (8*Z.of_nat n))
          (byte_at (read_signal (round s) 1305%nat) (8*Z.of_nat n)).
Proof.
  intros HN. apply boolz_injective. rewrite <- observed_bit_value by lia.
  rewrite fullcore_byte_equal by exact HN. now apply original_equal_expression.
Qed.
Lemma actual_greater_byte_boolean s n : (n < 4)%nat ->
  observed_bit (round s) 1354%nat (Z.of_nat n) =
    Z.gtb
      (compare_byte_value (read_signal (round s) 1304%nat) (8*Z.of_nat n)
        (read_slice (read_signal (round s) 1352%nat) (Z.of_nat n) 1))
      (compare_byte_value (read_signal (round s) 1305%nat) (8*Z.of_nat n)
        (read_slice (read_signal (round s) 1352%nat) (Z.of_nat n) 1)).
Proof.
  intros HN. apply boolz_injective. rewrite <- observed_bit_value by lia.
  rewrite fullcore_byte_greater by exact HN. now apply original_greater_expression.
Qed.
Lemma known_compare_mode_bit x mode n : (n < 4)%nat -> norm 4 x = mode ->
  read_slice x (Z.of_nat n) 1 = read_slice mode (Z.of_nat n) 1.
Proof.
  intros HN HM. rewrite <- (slice_norm x 4 (Z.of_nat n) 1 ltac:(lia) ltac:(lia) ltac:(lia)).
  now rewrite HM.
Qed.
Lemma actual_equal_word_bytes s : observed_equal (round s) =
  equal4 (byte_at (read_signal (round s) 1304%nat) 24)
    (byte_at (read_signal (round s) 1304%nat) 16)
    (byte_at (read_signal (round s) 1304%nat) 8)
    (byte_at (read_signal (round s) 1304%nat) 0)
    (byte_at (read_signal (round s) 1305%nat) 24)
    (byte_at (read_signal (round s) 1305%nat) 16)
    (byte_at (read_signal (round s) 1305%nat) 8)
    (byte_at (read_signal (round s) 1305%nat) 0).
Proof.
  unfold observed_equal, equal4.
  rewrite_indexed (actual_equal_byte_boolean s 3 ltac:(lia)).
  rewrite_indexed (actual_equal_byte_boolean s 2 ltac:(lia)).
  rewrite_indexed (actual_equal_byte_boolean s 1 ltac:(lia)).
  rewrite_indexed (actual_equal_byte_boolean s 0 ltac:(lia)). reflexivity.
Qed.
Lemma actual_unsigned_greater_word_bytes s :
  norm 7 (read_signal (round s) 1303%nat) = 3 -> observed_greater (round s) =
  greater4 (byte_at (read_signal (round s) 1304%nat) 24)
    (byte_at (read_signal (round s) 1304%nat) 16)
    (byte_at (read_signal (round s) 1304%nat) 8)
    (byte_at (read_signal (round s) 1304%nat) 0)
    (byte_at (read_signal (round s) 1305%nat) 24)
    (byte_at (read_signal (round s) 1305%nat) 16)
    (byte_at (read_signal (round s) 1305%nat) 8)
    (byte_at (read_signal (round s) 1305%nat) 0).
Proof.
  intros HO. pose proof (fullcore_unsigned_mode s HO) as HM.
  unfold observed_greater, greater4.
  rewrite_indexed (actual_greater_byte_boolean s 3 ltac:(lia)).
  rewrite_indexed (actual_greater_byte_boolean s 2 ltac:(lia)).
  rewrite_indexed (actual_greater_byte_boolean s 1 ltac:(lia)).
  rewrite_indexed (actual_greater_byte_boolean s 0 ltac:(lia)).
  rewrite_indexed (actual_equal_byte_boolean s 3 ltac:(lia)).
  rewrite_indexed (actual_equal_byte_boolean s 2 ltac:(lia)).
  rewrite_indexed (actual_equal_byte_boolean s 1 ltac:(lia)).
  rewrite_indexed (known_compare_mode_bit _ 0 3 ltac:(lia) HM).
  rewrite_indexed (known_compare_mode_bit _ 0 2 ltac:(lia) HM).
  rewrite_indexed (known_compare_mode_bit _ 0 1 ltac:(lia) HM).
  rewrite_indexed (known_compare_mode_bit _ 0 0 ltac:(lia) HM).
  change (read_slice 0 3 1) with 0; change (read_slice 0 2 1) with 0;
    change (read_slice 0 1 1) with 0; change (read_slice 0 0 1) with 0.
  rewrite !unsigned_comparison_byte by lia. reflexivity.
Qed.
Lemma actual_signed_greater_word_bytes s :
  norm 7 (read_signal (round s) 1303%nat) = 2 ->
  norm 2 (read_signal (round s) 1307%nat) = 0 -> observed_greater (round s) =
  greater4 (signed_value 8 (byte_at (read_signal (round s) 1304%nat) 24))
    (byte_at (read_signal (round s) 1304%nat) 16)
    (byte_at (read_signal (round s) 1304%nat) 8)
    (byte_at (read_signal (round s) 1304%nat) 0)
    (signed_value 8 (byte_at (read_signal (round s) 1305%nat) 24))
    (byte_at (read_signal (round s) 1305%nat) 16)
    (byte_at (read_signal (round s) 1305%nat) 8)
    (byte_at (read_signal (round s) 1305%nat) 0).
Proof.
  intros HO HV. pose proof (fullcore_signed_mode s HO HV) as HM.
  unfold observed_greater, greater4.
  rewrite_indexed (actual_greater_byte_boolean s 3 ltac:(lia)).
  rewrite_indexed (actual_greater_byte_boolean s 2 ltac:(lia)).
  rewrite_indexed (actual_greater_byte_boolean s 1 ltac:(lia)).
  rewrite_indexed (actual_greater_byte_boolean s 0 ltac:(lia)).
  rewrite_indexed (actual_equal_byte_boolean s 3 ltac:(lia)).
  rewrite_indexed (actual_equal_byte_boolean s 2 ltac:(lia)).
  rewrite_indexed (actual_equal_byte_boolean s 1 ltac:(lia)).
  rewrite_indexed (known_compare_mode_bit _ 8 3 ltac:(lia) HM).
  rewrite_indexed (known_compare_mode_bit _ 8 2 ltac:(lia) HM).
  rewrite_indexed (known_compare_mode_bit _ 8 1 ltac:(lia) HM).
  rewrite_indexed (known_compare_mode_bit _ 8 0 ltac:(lia) HM).
  change (read_slice 8 3 1) with 1; change (read_slice 8 2 1) with 0;
    change (read_slice 8 1 1) with 0; change (read_slice 8 0 1) with 0.
  rewrite !signed_comparison_byte, !unsigned_comparison_byte by lia.
  rewrite <- signed_byte_equality by (apply byte_range; lia). reflexivity.
Qed.
Theorem fullcore_scalar_sltu s : norm 7 (read_signal (round s) 1303%nat) = 3 ->
  norm 2 (read_signal (round s) 1307%nat) = 0 ->
  norm 32 (read_signal (round s) 1314%nat) =
    boolz (Z.ltb (norm 32 (read_signal (round s) 1304%nat))
                 (norm 32 (read_signal (round s) 1305%nat))).
Proof.
  intros HO HV. rewrite fullcore_scalar_compare_boolean with (op:=3) by (try assumption; tauto).
  rewrite actual_unsigned_greater_word_bytes by exact HO.
  rewrite actual_equal_word_bytes, unsigned_byte_lex_less. reflexivity.
Qed.
Theorem fullcore_scalar_slt s : norm 7 (read_signal (round s) 1303%nat) = 2 ->
  norm 2 (read_signal (round s) 1307%nat) = 0 ->
  norm 32 (read_signal (round s) 1314%nat) =
    boolz (Z.ltb (signed_value 32 (read_signal (round s) 1304%nat))
                 (signed_value 32 (read_signal (round s) 1305%nat))).
Proof.
  intros HO HV. rewrite fullcore_scalar_compare_boolean with (op:=2) by (try assumption; tauto).
  rewrite actual_signed_greater_word_bytes by assumption. rewrite actual_equal_word_bytes.
  unfold equal4. rewrite <- signed_byte_equality by (apply byte_range; lia).
  fold equal4. rewrite signed_byte_lex_less. reflexivity.
Qed.
Print Assumptions fullcore_scalar_sltu.
Print Assumptions fullcore_scalar_slt.
End CV32E40PFullCoreCompareWord.
