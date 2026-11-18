(** CPU-independent signed arithmetic-shift composition. Separate from the
    frozen base interface so existing RTL consumers need not be rebuilt. *)
From Coq Require Import ZArith Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant
 Ex.External.CPUArrayContracts Ex.External.CPUSequentialShiftMath.
Import ExtendedSV ExtendedSVWordInvariant CPUArrayContracts CPUSequentialShiftMath.
Local Open Scope Z_scope.
Module CPUSequentialArithmeticShiftMath.
Lemma signed_normalized x:signed_value 32(norm 32 x)=signed_value 32 x.
Proof. unfold signed_value;rewrite norm_idempotent;reflexivity. Qed.
Lemma signed32_range x:-(2^31)<=signed_value 32 x<2^31.
Proof.
 pose proof(index_dtype_covers_bank 32 x)as HR.
 unfold signed_value;cbn[Nat.eqb Nat.pred].
 change(-(2147483648)<=
  (if Z.testbit(norm 32 x)31 then norm 32 x-4294967296 else norm 32 x)<2147483648).
 change(0<=norm 32 x<4294967296)in HR.
 rewrite Z.testbit_eqb by lia;change(2^31)with 2147483648.
 destruct(Z_lt_ge_dec(norm 32 x)2147483648)as[HL|HH].
 - rewrite Z.div_small by lia;cbn;lia.
 - assert(HD:norm 32 x/2147483648=1).
   { symmetry;apply(Z.div_unique _ _ 1(norm 32 x-2147483648));[left;lia|ring]. }
   rewrite HD;cbn;lia.
Qed.
Lemma signed32_small x:-(2^31)<=x<2^31->signed_value 32 x=x.
Proof.
 intro HR;unfold signed_value;cbn[Nat.eqb Nat.pred].
 rewrite norm_as_mod;change(2^Z.of_nat 32)with 4294967296.
 change(Z.of_nat 31)with 31;rewrite Z.testbit_eqb by lia.
 change(2^31)with 2147483648 in *.
 destruct(Z_le_gt_dec 0 x)as[HP|HN].
 - rewrite(Z.mod_small x 4294967296)by lia.
   rewrite(Z.div_small x 2147483648)by lia;reflexivity.
 - assert(HM:x mod 4294967296=x+4294967296).
   { symmetry;apply(Z.mod_unique _ _ (-1));[left;lia|ring]. }
   rewrite HM.
   assert(HD:(x+4294967296)/2147483648=1).
   { symmetry;apply(Z.div_unique _ _ 1(x+2147483648));[left;lia|ring]. }
   rewrite HD;cbn;lia.
Qed.
Lemma arithmetic_right_range x a:0<=a->-(2^31)<=x<2^31->
 -(2^31)<=Z.shiftr x a<2^31.
Proof.
 intros HA HX;rewrite Z.shiftr_div_pow2 by exact HA.
 assert(HP:0<2^a)by(apply Z.pow_pos_nonneg;lia).
 split.
 - apply Z.div_le_lower_bound;nia.
 - apply Z.div_lt_upper_bound;nia.
Qed.
Theorem arithmetic_right_shift_composes x a b:0<=a->0<=b->
 shift_math ShiftRightArithmetic(shift_math ShiftRightArithmetic x a)b=
 shift_math ShiftRightArithmetic x(a+b).
Proof.
 intros HA HB;unfold shift_math;rewrite signed_normalized.
 rewrite signed32_small.
 - rewrite Z.shiftr_shiftr by exact HB;reflexivity.
 - apply arithmetic_right_range;[exact HA|apply signed32_range].
Qed.
Theorem sequential_shift_composes kind x a b:0<=a->0<=b->
 shift_math kind(shift_math kind x a)b=shift_math kind x(a+b).
Proof.
 destruct kind;[apply left_shift_composes|apply logical_right_shift_composes|apply arithmetic_right_shift_composes].
Qed.
End CPUSequentialArithmeticShiftMath.
Print Assumptions CPUSequentialArithmeticShiftMath.arithmetic_right_shift_composes.
Print Assumptions CPUSequentialArithmeticShiftMath.sequential_shift_composes.
