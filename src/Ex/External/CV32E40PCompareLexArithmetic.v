(** Arithmetic bridge for the RTL scalar lexicographic byte comparator.
    The most significant byte may be signed; lower bytes are unsigned.
    These facts still require the actual byte-output wiring certificates. *)
From Coq Require Import ZArith Bool Lia btauto.Btauto.
Local Open Scope Z_scope.
Module CV32E40PCompareLexArithmetic.

Lemma pair_equal base ah al bh bl :
  0 < base -> 0 <= al < base -> 0 <= bl < base ->
  Z.eqb (ah*base+al) (bh*base+bl) = andb (Z.eqb ah bh) (Z.eqb al bl).
Proof.
  intros HB HA HL.
  destruct (Z.eqb ah bh) eqn:HH; destruct (Z.eqb al bl) eqn:HLB; cbn [andb].
  all: match type of HH with _ = true => apply Z.eqb_eq in HH
    | _ = false => apply Z.eqb_neq in HH end.
  all: match type of HLB with _ = true => apply Z.eqb_eq in HLB
    | _ = false => apply Z.eqb_neq in HLB end.
  all: (match goal with |- _ = true => apply Z.eqb_eq
    | |- _ = false => apply Z.eqb_neq end);
    destruct (Z_lt_ge_dec ah bh); nia.
Qed.
Lemma pair_greater base ah al bh bl :
  0 < base -> 0 <= al < base -> 0 <= bl < base ->
  Z.gtb (ah*base+al) (bh*base+bl) =
    orb (Z.gtb ah bh) (andb (Z.eqb ah bh) (Z.gtb al bl)).
Proof.
  intros HB HA HL. rewrite !Z.gtb_ltb.
  destruct (Z.ltb bh ah) eqn:HH; destruct (Z.eqb ah bh) eqn:HE;
    destruct (Z.ltb bl al) eqn:HLB; cbn [orb andb].
  all: match type of HH with _ = true => apply Z.ltb_lt in HH
    | _ = false => apply Z.ltb_ge in HH end.
  all: match type of HE with _ = true => apply Z.eqb_eq in HE
    | _ = false => apply Z.eqb_neq in HE end.
  all: match type of HLB with _ = true => apply Z.ltb_lt in HLB
    | _ = false => apply Z.ltb_ge in HLB end.
  all: (match goal with |- _ = true => apply Z.ltb_lt
    | |- _ = false => apply Z.ltb_ge end); nia.
Qed.

Definition pack4 a3 a2 a1 a0 := ((a3*256+a2)*256+a1)*256+a0.
Definition equal4 a3 a2 a1 a0 b3 b2 b1 b0 :=
  andb (andb (andb (Z.eqb a3 b3) (Z.eqb a2 b2)) (Z.eqb a1 b1)) (Z.eqb a0 b0).
Definition greater4 a3 a2 a1 a0 b3 b2 b1 b0 :=
  orb (Z.gtb a3 b3) (andb (Z.eqb a3 b3)
    (orb (Z.gtb a2 b2) (andb (Z.eqb a2 b2)
      (orb (Z.gtb a1 b1) (andb (Z.eqb a1 b1) (Z.gtb a0 b0)))))).

Theorem scalar_equal_is_word_equal a3 a2 a1 a0 b3 b2 b1 b0 :
  0 <= a0 < 256 -> 0 <= a1 < 256 -> 0 <= a2 < 256 ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  equal4 a3 a2 a1 a0 b3 b2 b1 b0 = Z.eqb (pack4 a3 a2 a1 a0) (pack4 b3 b2 b1 b0).
Proof.
  intros. unfold pack4, equal4. rewrite !pair_equal by lia. reflexivity.
Qed.
Theorem scalar_greater_is_word_greater a3 a2 a1 a0 b3 b2 b1 b0 :
  0 <= a0 < 256 -> 0 <= a1 < 256 -> 0 <= a2 < 256 ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  greater4 a3 a2 a1 a0 b3 b2 b1 b0 = Z.gtb (pack4 a3 a2 a1 a0) (pack4 b3 b2 b1 b0).
Proof.
  intros. unfold pack4, greater4.
  rewrite !pair_greater, !pair_equal by lia. btauto.
Qed.
Theorem scalar_less_is_word_less a3 a2 a1 a0 b3 b2 b1 b0 :
  0 <= a0 < 256 -> 0 <= a1 < 256 -> 0 <= a2 < 256 ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  negb (orb (greater4 a3 a2 a1 a0 b3 b2 b1 b0)
    (equal4 a3 a2 a1 a0 b3 b2 b1 b0)) =
    Z.ltb (pack4 a3 a2 a1 a0) (pack4 b3 b2 b1 b0).
Proof.
  intros.
  rewrite scalar_greater_is_word_greater, scalar_equal_is_word_equal by assumption.
  rewrite Z.gtb_ltb. destruct (Z.ltb (pack4 b3 b2 b1 b0) (pack4 a3 a2 a1 a0)) eqn:HG;
    destruct (Z.eqb (pack4 a3 a2 a1 a0) (pack4 b3 b2 b1 b0)) eqn:HE; cbn [orb negb].
  all: match type of HG with _ = true => apply Z.ltb_lt in HG
    | _ = false => apply Z.ltb_ge in HG end.
  all: match type of HE with _ = true => apply Z.eqb_eq in HE
    | _ = false => apply Z.eqb_neq in HE end.
  all: symmetry; (match goal with |- _ = true => apply Z.ltb_lt
    | |- _ = false => apply Z.ltb_ge end); lia.
Qed.
Print Assumptions scalar_equal_is_word_equal.
Print Assumptions scalar_greater_is_word_greater.
Print Assumptions scalar_less_is_word_less.
End CV32E40PCompareLexArithmetic.
