(** Exact bridge between ExtendedSV's 32-bit signed interpretation and
    the reference ISA's abstract coqutil word interface. *)
From Coq Require Import ZArith Bool Lia.
Require Import Lang.ExtendedSV Ex.External.CV32E40PAddiAdder
  Ex.External.CV32E40PAddiAdderBits.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Import ExtendedSV CV32E40PAddiAdder CV32E40PAddiAdderBits.
Local Open Scope Z_scope.
Module CV32E40PISAWordInterpretation.
Section Word32.
Context {word : Interface.word 32} {BW : Bitwidth 32} {word_ok : word.ok word}.

Theorem reference_signed_word (x : word) : signed_value 32 (word.unsigned x) = word.signed x.
Proof.
  pose proof (word.unsigned_range x) as HR.
  unfold signed_value. cbn [Nat.eqb Nat.pred].
  rewrite norm_small by exact HR. change (Z.of_nat 31) with 31.
  rewrite word.signed_eq_swrap_unsigned. unfold word.swrap.
  change ((if Z.testbit (word.unsigned x) 31 then word.unsigned x - 4294967296
    else word.unsigned x) =
    (word.unsigned x + 2147483648) mod 4294967296 - 2147483648).
  change (0 <= word.unsigned x < 4294967296) in HR.
  rewrite Z.testbit_eqb by lia. change (2^31) with 2147483648.
  destruct (Z_lt_ge_dec (word.unsigned x) 2147483648) as [HL|HH].
  - rewrite Z.div_small by lia. rewrite Z.mod_0_l by lia.
    change (0 =? 1) with false. rewrite Z.mod_small by lia. lia.
  - assert (word.unsigned x / 2147483648 = 1) as HD.
    { symmetry. apply (Z.div_unique _ _ 1 (word.unsigned x - 2147483648));
      [left; lia|ring]. }
    rewrite HD, Z.mod_small by lia. change (1 =? 1) with true.
    assert ((word.unsigned x + 2147483648) mod 4294967296 =
      word.unsigned x - 2147483648) as HM.
    { symmetry. apply (Z.mod_unique _ _ 1); [left; lia|ring]. }
    rewrite HM. lia.
Qed.
Theorem reference_signed_less (a b : word) :
  Z.ltb (signed_value 32 (word.unsigned a)) (signed_value 32 (word.unsigned b)) =
    word.lts a b.
Proof. rewrite !reference_signed_word. symmetry. apply word.signed_lts. Qed.
Theorem reference_unsigned_less (a b : word) :
  Z.ltb (norm 32 (word.unsigned a)) (norm 32 (word.unsigned b)) = word.ltu a b.
Proof.
  rewrite !norm_small by apply word.unsigned_range. symmetry. apply word.unsigned_ltu.
Qed.
End Word32.
Print Assumptions reference_signed_word.
Print Assumptions reference_signed_less.
Print Assumptions reference_unsigned_less.
End CV32E40PISAWordInterpretation.
