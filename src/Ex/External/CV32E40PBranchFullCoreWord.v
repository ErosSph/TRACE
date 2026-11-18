(** Mathematical identity of all six actual scalar branch comparison outputs.
    The comparator word is reconstructed from the original four byte paths.
    Not yet a retirement, redirect, reachability or infinite branch theorem. *)
From Coq Require Import ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice
  Ex.External.CV32E40PBranchCompareControl Ex.External.CV32E40PBranchFullCoreOutput
  Ex.External.CV32E40PFullCoreCompareWord Ex.External.CV32E40PCompareFullCoreOutput
  Ex.External.CV32E40PCompareByteArithmetic Ex.External.CV32E40PCompareWordPacking
  Ex.External.CV32E40PCompareLexArithmetic Ex.External.CV32E40PCompareSignedByteEquality
  Ex.External.CV32E40PAddiAdderBits Ex.External.CV32E40PAddiOperandCone.
Import ExtendedSV ExtendedSVBitSlice CV32E40PBranchCompareControl
  CV32E40PBranchFullCoreOutput CV32E40PFullCoreCompareWord CV32E40PCompareFullCoreOutput
  CV32E40PCompareByteArithmetic CV32E40PCompareWordPacking CV32E40PCompareLexArithmetic
  CV32E40PCompareSignedByteEquality CV32E40PAddiAdderBits CV32E40PAddiOperandCone.
Local Open Scope Z_scope.
Local Opaque read_signal round.
Module CV32E40PBranchFullCoreWord.
Lemma unsigned_greater_from_real_mode s :
  norm 4 (read_signal (round s) 1352%nat) = 0 -> observed_greater (round s) =
  greater4 (byte_at (read_signal (round s) 1304%nat) 24)
    (byte_at (read_signal (round s) 1304%nat) 16)
    (byte_at (read_signal (round s) 1304%nat) 8)
    (byte_at (read_signal (round s) 1304%nat) 0)
    (byte_at (read_signal (round s) 1305%nat) 24)
    (byte_at (read_signal (round s) 1305%nat) 16)
    (byte_at (read_signal (round s) 1305%nat) 8)
    (byte_at (read_signal (round s) 1305%nat) 0).
Proof.
  intros HM.
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
Lemma signed_greater_from_real_mode s :
  norm 4 (read_signal (round s) 1352%nat) = 8 -> observed_greater (round s) =
  greater4 (signed_value 8 (byte_at (read_signal (round s) 1304%nat) 24))
    (byte_at (read_signal (round s) 1304%nat) 16)
    (byte_at (read_signal (round s) 1304%nat) 8)
    (byte_at (read_signal (round s) 1304%nat) 0)
    (signed_value 8 (byte_at (read_signal (round s) 1305%nat) 24))
    (byte_at (read_signal (round s) 1305%nat) 16)
    (byte_at (read_signal (round s) 1305%nat) 8)
    (byte_at (read_signal (round s) 1305%nat) 0).
Proof.
  intros HM.
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

Lemma actual_equal_is_word_equal s : observed_equal (round s) =
  Z.eqb (norm 32 (read_signal (round s) 1304%nat))
    (norm 32 (read_signal (round s) 1305%nat)).
Proof.
  rewrite actual_equal_word_bytes.
  rewrite scalar_equal_is_word_equal by (apply byte_range; lia).
  now rewrite <- !unsigned_word_is_packed_bytes.
Qed.
Lemma branch_signed_less_boolean s op : op = 0 \/ op = 10 ->
  norm 7 (read_signal (round s) 1303%nat) = op ->
  norm 2 (read_signal (round s) 1307%nat) = 0 ->
  negb (orb (observed_greater (round s)) (observed_equal (round s))) =
    Z.ltb (signed_value 32 (read_signal (round s) 1304%nat))
      (signed_value 32 (read_signal (round s) 1305%nat)).
Proof.
  intros HC HO HV.
  rewrite signed_greater_from_real_mode
    by (apply fullcore_branch_signed_mode with (op:=op); assumption).
  rewrite actual_equal_word_bytes.
  unfold equal4. rewrite <- signed_byte_equality by (apply byte_range; lia).
  fold equal4. apply signed_byte_lex_less.
Qed.
Lemma branch_unsigned_less_boolean s op :
  op = 1 \/ op = 11 \/ op = 12 \/ op = 13 ->
  norm 7 (read_signal (round s) 1303%nat) = op ->
  negb (orb (observed_greater (round s)) (observed_equal (round s))) =
    Z.ltb (norm 32 (read_signal (round s) 1304%nat))
      (norm 32 (read_signal (round s) 1305%nat)).
Proof.
  intros HC HO.
  rewrite unsigned_greater_from_real_mode
    by (apply fullcore_branch_unsigned_mode with (op:=op); assumption).
  rewrite actual_equal_word_bytes. apply unsigned_byte_lex_less.
Qed.

Definition branch_word_condition (op x y : Z) : bool :=
  if op =? 12 then Z.eqb (norm 32 x) (norm 32 y) else
  if op =? 13 then negb (Z.eqb (norm 32 x) (norm 32 y)) else
  if op =? 0 then Z.ltb (signed_value 32 x) (signed_value 32 y) else
  if op =? 10 then negb (Z.ltb (signed_value 32 x) (signed_value 32 y)) else
  if op =? 1 then Z.ltb (norm 32 x) (norm 32 y) else
  negb (Z.ltb (norm 32 x) (norm 32 y)).

Theorem fullcore_branch_condition s op : BranchALU op ->
  norm 7 (read_signal (round s) 1303%nat) = op ->
  norm 2 (read_signal (round s) 1307%nat) = 0 ->
  norm 1 (read_signal (round s) 1315%nat) =
    boolz (branch_word_condition op
      (read_signal (round s) 1304%nat) (read_signal (round s) 1305%nat)).
Proof.
  intros HC HO HV. rewrite fullcore_scalar_branch_boolean with (op:=op) by assumption.
  destruct HC as [->| [->| [->| [->| [->| ->]]]]];
    cbn [branch_boolean branch_word_condition Z.eqb Pos.eqb orb].
  - now rewrite actual_equal_is_word_equal.
  - now rewrite actual_equal_is_word_equal.
  - rewrite branch_signed_less_boolean with (op:=0) by (try assumption; tauto).
    reflexivity.
  - rewrite <- (branch_signed_less_boolean s 10 ltac:(tauto) HO HV).
    now rewrite Bool.negb_involutive.
  - rewrite branch_unsigned_less_boolean with (op:=1) by (try assumption; tauto).
    reflexivity.
  - rewrite <- (branch_unsigned_less_boolean s 11 ltac:(tauto) HO).
    now rewrite Bool.negb_involutive.
Qed.
Print Assumptions fullcore_branch_condition.
End CV32E40PBranchFullCoreWord.

