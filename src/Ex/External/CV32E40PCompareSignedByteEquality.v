(** Equality is unaffected by signed byte interpretation. The scalar RTL
    tests raw byte equality even when its greater-than path is signed. *)
From Coq Require Import ZArith Lia Bool.
Require Import Lang.ExtendedSV Ex.External.CV32E40PAddiAdder
  Ex.External.CV32E40PAddiAdderBits Ex.External.CV32E40PCompareByteArithmetic.
Import ExtendedSV CV32E40PAddiAdder CV32E40PAddiAdderBits CV32E40PCompareByteArithmetic.
Local Open Scope Z_scope.
Module CV32E40PCompareSignedByteEquality.

Lemma signed_byte_normalized v : norm 8 (signed_value 8 v) = norm 8 v.
Proof.
  unfold signed_value. cbn [Nat.eqb Nat.pred].
  destruct (Z.testbit (norm 8 v) (Z.of_nat 7)); [|apply CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice].
  rewrite !norm_mod. change (2^Z.of_nat 8) with 256.
  replace (v mod 256 - 256) with (v mod 256 + (-1)*256) by ring.
  rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.
Theorem signed_byte_equality a b : 0 <= a < 256 -> 0 <= b < 256 ->
  Z.eqb (signed_value 8 a) (signed_value 8 b) = Z.eqb a b.
Proof.
  intros HA HB. apply Bool.eq_true_iff_eq.
  rewrite !Z.eqb_eq. split.
  - intros H. apply (f_equal (norm 8)) in H. rewrite !signed_byte_normalized in H.
    rewrite (norm_small 8 a ltac:(change (2^Z.of_nat 8) with 256; exact HA)),
      (norm_small 8 b ltac:(change (2^Z.of_nat 8) with 256; exact HB)) in H. exact H.
  - intros ->. reflexivity.
Qed.
Print Assumptions signed_byte_equality.
End CV32E40PCompareSignedByteEquality.
