(** Narrow LLM-authored: OpenAI Codex. Design-independent concatenation
    stages used by bounded barrel shifters; original SV normalization. *)
From Coq Require Import ZArith Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBankAlignment
 Lang.ExtendedSVWordInvariant Ex.External.CPUCarryIsolatedExpr
 Ex.External.CPUSequentialShiftMath Ex.External.CPUArrayContracts
 Ex.External.CPUSequentialArithmeticShiftMath.
Import ExtendedSV ExtendedSVBankAlignment ExtendedSVWordInvariant
 CPUCarryIsolatedExpr CPUSequentialShiftMath CPUArrayContracts CPUSequentialArithmeticShiftMath.
Local Open Scope Z_scope.
Module CPUBarrelShiftMath.
Definition right_stage x fill k :=
 norm 32(Z.lor(Z.shiftl(norm k fill)(Z.of_nat(32-k)))
  (norm(32-k)(Z.shiftr(norm 32 x)(Z.of_nat k)))).
Definition left_stage x k :=
 norm 32(Z.lor(Z.shiftl(norm(32-k)(norm 32 x))(Z.of_nat k))(norm k 0)).
Lemma norm_zero width : norm width 0=0.
Proof. unfold norm. apply Z.land_0_l. Qed.
Lemma norm_minus_one width : norm width (-1)=2^Z.of_nat width-1.
Proof. unfold norm,mask. apply Z.land_m1_l. Qed.
Lemma stage_powers k : (k<=32)%nat ->
 2^Z.of_nat(32-k)*2^Z.of_nat k=4294967296.
Proof.
 intro HK. rewrite <-Z.pow_add_r by lia.
 rewrite <-Nat2Z.inj_add. replace(32-k+k)%nat with 32%nat by lia. reflexivity.
Qed.
Lemma shifted_range x k : (k<=32)%nat ->
 0<=Z.shiftr(norm 32 x)(Z.of_nat k)<2^Z.of_nat(32-k).
Proof.
 intro HK. pose proof(norm_bounds 32 x)as HX.
 rewrite Z.shiftr_div_pow2 by lia.
 assert(HP:0<2^Z.of_nat k)by(apply Z.pow_pos_nonneg;lia).
 split;[apply Z.div_pos;lia|]. apply Z.div_lt_upper_bound;[exact HP|].
 rewrite Z.mul_comm,(stage_powers k HK). exact(proj2 HX).
Qed.
Lemma right_stage_value x fill k : (k<=32)%nat ->
 right_stage x fill k=norm 32(Z.shiftr(norm 32 x)(Z.of_nat k)+
   norm k fill*2^Z.of_nat(32-k)).
Proof.
 intro HK. unfold right_stage. rewrite Z.lor_comm.
 rewrite lor_add_disjoint by (try lia;apply norm_bounds).
 rewrite(norm_in_range (32-k)(Z.shiftr(norm 32 x)(Z.of_nat k))) by now apply shifted_range.
 reflexivity.
Qed.
Theorem logical_right_stage x k : (k<=32)%nat ->
 right_stage x 0 k=shift_math ShiftRightLogical x(Z.of_nat k).
Proof. intro HK. rewrite right_stage_value by exact HK. rewrite norm_zero,Z.mul_0_l,Z.add_0_r. reflexivity. Qed.
Theorem arithmetic_right_stage x k : (k<=32)%nat ->
 right_stage x (if Z.testbit(norm 32 x)31 then -1 else 0) k=
 shift_math ShiftRightArithmetic x(Z.of_nat k).
Proof.
 intro HK. rewrite right_stage_value by exact HK.
 unfold shift_math,signed_value;cbn[Nat.eqb Nat.pred].
 change(Z.of_nat 31)with 31. change(2^Z.of_nat 32)with 4294967296.
 set(y:=norm 32 x).
 destruct(Z.testbit(y)31).
 - rewrite norm_minus_one. rewrite !norm_mod,!Z.shiftr_div_pow2 by lia.
   change(2^Z.of_nat 32)with 4294967296.
   assert(HP:2^Z.of_nat k<>0)by(apply Z.pow_nonzero;lia).
   pose proof(stage_powers k HK)as HM.
   replace(y-4294967296)with(y+(-2^Z.of_nat(32-k))*2^Z.of_nat k)by nia.
   rewrite Z.div_add by exact HP.
   replace(y/2^Z.of_nat k+(2^Z.of_nat k-1)*2^Z.of_nat(32-k))
    with((y/2^Z.of_nat k+-2^Z.of_nat(32-k))+1*4294967296)by nia.
   rewrite Z.mod_add by discriminate. reflexivity.
 - rewrite norm_zero,Z.mul_0_l,Z.add_0_r. reflexivity.
Qed.
Theorem left_stage_correct x k : (k<=32)%nat ->
 left_stage x k=shift_math ShiftLeft x(Z.of_nat k).
Proof.
 intro HK. unfold left_stage,shift_math. rewrite norm_zero,Z.lor_0_r.
 set(y:=norm 32 x). rewrite !norm_mod,!Z.shiftl_mul_pow2 by lia.
 change(2^Z.of_nat 32)with 4294967296.
 pose proof(stage_powers k HK)as HM.
 assert(HP:2^Z.of_nat(32-k)<>0)by(apply Z.pow_nonzero;lia).
 pose proof(Z.div_mod y (2^Z.of_nat(32-k)) HP)as HD.
 replace(y*2^Z.of_nat k)with
  ((y mod 2^Z.of_nat(32-k))*2^Z.of_nat k+(y/2^Z.of_nat(32-k))*4294967296)
 by(rewrite <-HM;transitivity((2^Z.of_nat(32-k)*(y/2^Z.of_nat(32-k))+y mod 2^Z.of_nat(32-k))*2^Z.of_nat k);[ring|now rewrite <-HD]).
 rewrite Z.mod_add by discriminate. reflexivity.
Qed.
Lemma sign_is_negative x :
 Z.testbit(norm 32 x)31=(signed_value 32 x<?0).
Proof.
 pose proof(norm_bounds 32 x)as HX.
 unfold signed_value;cbn[Nat.eqb Nat.pred].
 change(Z.of_nat 31)with 31. change(2^Z.of_nat 32)with 4294967296 in *.
 destruct(Z.testbit(norm 32 x)31).
 - symmetry. apply Z.ltb_lt. lia.
 - symmetry. apply Z.ltb_ge. lia.
Qed.
Lemma division_negative z p : 0<p -> (z/p<?0)=(z<?0).
Proof.
 intro HP. apply Bool.eq_true_iff_eq. rewrite !Z.ltb_lt. split.
 - intro HD. destruct(Z_lt_ge_dec z 0);[assumption|].
   assert(0<=z/p)by(apply Z.div_pos;lia). lia.
 - intro HZ. apply Z.div_lt_upper_bound;lia.
Qed.
Theorem arithmetic_shift_sign x amount : 0<=amount ->
 Z.testbit(norm 32(shift_math ShiftRightArithmetic x amount))31=
 Z.testbit(norm 32 x)31.
Proof.
 intro HA. rewrite !sign_is_negative.
 unfold shift_math. rewrite signed_normalized,signed32_small.
 - rewrite Z.shiftr_div_pow2 by exact HA. apply division_negative.
   apply Z.pow_pos_nonneg;lia.
 - apply arithmetic_right_range;[exact HA|apply signed32_range].
Qed.
End CPUBarrelShiftMath.
