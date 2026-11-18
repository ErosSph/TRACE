(** CPU-independent 32-bit sequential-shift arithmetic and concrete 4/1 rank.
    No CPU state, signal number, RTL AST or ISA correctness premise occurs. *)
From Coq Require Import ZArith Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Ex.External.CPUArrayContracts.
Import ExtendedSV ExtendedSVWordInvariant CPUArrayContracts.
Local Open Scope Z_scope.
Module CPUSequentialShiftMath.
Inductive ShiftKind:=ShiftLeft|ShiftRightLogical|ShiftRightArithmetic.
Definition shift_math kind x amount:=norm 32(match kind with
 |ShiftLeft=>Z.shiftl(norm 32 x)amount
 |ShiftRightLogical=>Z.shiftr(norm 32 x)amount
 |ShiftRightArithmetic=>Z.shiftr(signed_value 32 x)amount end).
Lemma shift_math_norm kind x a:norm 32(shift_math kind x a)=shift_math kind x a.
Proof. unfold shift_math;apply norm_idempotent. Qed.
Lemma norm_as_mod width x:norm width x=x mod 2^Z.of_nat width.
Proof.
 unfold norm,mask;replace(2^Z.of_nat width-1)with(Z.ones(Z.of_nat width))
 by(rewrite Z.ones_equiv;reflexivity).
 rewrite Z.land_ones by lia;reflexivity.
Qed.
Lemma normalized_left_shift x a:0<=a->
 norm 32(Z.shiftl(norm 32 x)a)=norm 32(Z.shiftl x a).
Proof.
 intro HA;rewrite !norm_as_mod,!Z.shiftl_mul_pow2 by exact HA.
 rewrite Z.mul_mod_idemp_l by discriminate;reflexivity.
Qed.
Theorem left_shift_composes x a b:0<=a->0<=b->
 shift_math ShiftLeft(shift_math ShiftLeft x a)b=shift_math ShiftLeft x(a+b).
Proof.
 intros HA HB;unfold shift_math;rewrite norm_idempotent,normalized_left_shift by exact HB.
 rewrite Z.shiftl_shiftl by exact HA;reflexivity.
Qed.
Lemma logical_right_range x a:0<=a->0<=x<2^32->0<=Z.shiftr x a<2^32.
Proof.
 intros HA HX;rewrite Z.shiftr_div_pow2 by exact HA.
 assert(HP:0<2^a)by(apply Z.pow_pos_nonneg;lia).
 split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;nia].
Qed.
Theorem logical_right_shift_composes x a b:0<=a->0<=b->
 shift_math ShiftRightLogical(shift_math ShiftRightLogical x a)b=
 shift_math ShiftRightLogical x(a+b).
Proof.
 intros HA HB;unfold shift_math;rewrite norm_idempotent.
 rewrite(norm_in_range 32(Z.shiftr(norm 32 x)a)).
 - rewrite Z.shiftr_shiftr by exact HB;reflexivity.
 - apply logical_right_range;[exact HA|apply index_dtype_covers_bank].
Qed.
Lemma left_shift_zero x:shift_math ShiftLeft x 0=norm 32 x.
Proof. unfold shift_math;rewrite Z.shiftl_0_r;apply norm_idempotent. Qed.
Definition step_width remaining:=if 4<=?remaining then 4 else 1.
Definition remaining_rank_z remaining:=remaining/4+remaining mod 4.
Definition remaining_rank remaining:=Z.to_nat(remaining_rank_z remaining).
Lemma remaining_rank_z_positive remaining:0<remaining->0<remaining_rank_z remaining.
Proof.
 intro HR;unfold remaining_rank_z.
 pose proof(Z.div_pos remaining 4 ltac:(lia)ltac:(lia)).
 pose proof(Z.mod_pos_bound remaining 4 ltac:(lia)).
 pose proof(Z.div_mod remaining 4 ltac:(lia));lia.
Qed.
Theorem remaining_rank_z_step remaining:0<remaining->
 remaining_rank_z(remaining-step_width remaining)=remaining_rank_z remaining-1.
Proof.
 intro HR;unfold step_width;destruct(4<=?remaining)eqn:HB.
 - apply Z.leb_le in HB;unfold remaining_rank_z.
   replace(remaining-4)with(remaining+(-1)*4)by lia.
   rewrite Z.div_add,Z.mod_add by lia;ring.
 - apply Z.leb_gt in HB;unfold remaining_rank_z.
   rewrite !Z.div_small,!Z.mod_small by lia;lia.
Qed.
Theorem remaining_rank_strictly_decreases remaining:0<remaining->
 (remaining_rank(remaining-step_width remaining)<remaining_rank remaining)%nat.
Proof.
 intro HR;unfold remaining_rank.
 pose proof(remaining_rank_z_positive remaining HR).
 rewrite remaining_rank_z_step by exact HR.
 apply Z2Nat.inj_lt;lia.
Qed.
Lemma remaining_step_in_range remaining:0<remaining<32->
 0<=remaining-step_width remaining<32.
Proof. intro HR;unfold step_width;destruct(4<=?remaining)eqn:HB;
 first[apply Z.leb_le in HB|apply Z.leb_gt in HB];lia. Qed.
Lemma remaining_step_normalized remaining:0<remaining<32->
 norm 5(remaining-step_width remaining)=remaining-step_width remaining.
Proof. intro HR;apply norm_in_range;exact(remaining_step_in_range remaining HR). Qed.
End CPUSequentialShiftMath.
Print Assumptions CPUSequentialShiftMath.left_shift_composes.
Print Assumptions CPUSequentialShiftMath.logical_right_shift_composes.
Print Assumptions CPUSequentialShiftMath.remaining_rank_strictly_decreases.
