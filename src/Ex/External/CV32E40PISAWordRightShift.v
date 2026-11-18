(** The actual FullCore right-shift interpretation agrees with the abstract
    reference word interface. Amount bounds are ISA legality, not an oracle
    for an RTL result. *)
From Coq Require Import ZArith Lia.
Require Import Lang.ExtendedSV Ex.External.CV32E40PISAWordInterpretation
  Ex.External.CV32E40PAddiAdder Ex.External.CV32E40PAddiAdderBits.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Import ExtendedSV CV32E40PISAWordInterpretation CV32E40PAddiAdder
  CV32E40PAddiAdderBits.
Local Open Scope Z_scope.
Module CV32E40PISAWordRightShift.
Section Word32.
Context {word : Interface.word 32} {BW : Bitwidth 32} {word_ok : word.ok word}.

Theorem reference_logical_right_shift (x : word) a : 0 <= a < 32 ->
  norm 32 (Z.shiftr (norm 32 (word.unsigned x)) a) =
    word.unsigned (word.sru x (word.of_Z a)).
Proof.
  intros HA. rewrite (norm_small 32 (word.unsigned x)) by apply word.unsigned_range.
  rewrite <- word.unsigned_sru_shamtZ by exact HA.
  apply norm_small, word.unsigned_range.
Qed.

Theorem reference_arithmetic_right_shift (x : word) a : 0 <= a < 32 ->
  norm 32 (Z.shiftr (signed_value 32 (word.unsigned x)) a) =
    word.unsigned (word.srs x (word.of_Z a)).
Proof.
  intros HA. rewrite reference_signed_word.
  rewrite <- word.signed_srs_shamtZ by exact HA.
  rewrite norm_mod.
  change (word.wrap (word.signed (word.srs x (word.of_Z a))) =
    word.unsigned (word.srs x (word.of_Z a))).
  rewrite <- word.unsigned_of_Z, word.of_Z_signed. reflexivity.
Qed.
End Word32.
Print Assumptions reference_logical_right_shift.
Print Assumptions reference_arithmetic_right_shift.
End CV32E40PISAWordRightShift.
