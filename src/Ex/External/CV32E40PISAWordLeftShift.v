(** Mathematical left-shift bridge for the existing generic ISA word
    interface. Operand freshness and actual RTL execution are separate. *)
From Coq Require Import ZArith Lia.
Require Import Lang.ExtendedSV Ex.External.CV32E40PISAWordInterpretation
  Ex.External.CV32E40PAddiAdder Ex.External.CV32E40PAddiAdderBits.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Import ExtendedSV CV32E40PISAWordInterpretation CV32E40PAddiAdder CV32E40PAddiAdderBits.
Local Open Scope Z_scope.
Module CV32E40PISAWordLeftShift.
Section Word32.
Context {word : Interface.word 32} {BW : Bitwidth 32} {word_ok : word.ok word}.
Theorem reference_left_shift (x : word) a : 0 <= a < 32 ->
  norm 32 (Z.shiftl (norm 32 (word.unsigned x)) a) =
    word.unsigned (word.slu x (word.of_Z a)).
Proof.
  intros HA. rewrite (norm_small 32 (word.unsigned x)) by apply word.unsigned_range.
  rewrite word.unsigned_slu_shamtZ by exact HA. exact (norm_mod 32 _).
Qed.
End Word32.
Print Assumptions reference_left_shift.
End CV32E40PISAWordLeftShift.
