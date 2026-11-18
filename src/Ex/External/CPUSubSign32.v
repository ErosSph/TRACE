(** Narrow LLM-authored: OpenAI Codex. Design-independent split-sign
    comparison using a 32-bit subtractor, extending CPUSubSign33. *)
From Coq Require Import ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBankAlignment Ex.External.CPUSubSign33.
Import ExtendedSV ExtendedSVBankAlignment CPUSubSign33.
Local Open Scope Z_scope.
Module CPUSubSign32.
Definition sign32 a := norm 1 (Z.shiftr a 31).
Lemma sign32_threshold a : 0<=a<4294967296 ->
 sign32 a=if 2147483648<=?a then 1 else 0.
Proof.
 intro HA. unfold sign32. rewrite n1 by (change(0<=a<4294967296);exact HA).
 destruct(Z.testbit a 31)eqn:HT;destruct(2147483648<=?a)eqn:HC;try reflexivity.
 - apply tb31 in HT;[|change(0<=a<4294967296);exact HA]. apply Z.leb_gt in HC. change(2147483648<=a)in HT. lia.
 - apply Z.leb_le in HC. assert(Z.testbit a 31=true)by(apply tb31;[change(0<=a<4294967296);exact HA|change(2147483648<=a);exact HC]). congruence.
Qed.
Lemma subtraction_sign D : -2147483648<D<2147483648 ->
 sign32(norm 32 D)=boolz(D<?0).
Proof.
 intro HD. unfold sign32. rewrite !norm_mod,Z.shiftr_div_pow2 by lia.
 change ((D mod 4294967296 / 2147483648) mod 2=boolz(D<?0)).
 destruct(Z_lt_dec D 0)as[HN|HP].
 - assert(HM:D mod 4294967296=D+4294967296)by(symmetry;apply Z.mod_unique with(q:= -1);lia).
   rewrite HM. assert(HQ:(D+4294967296)/2147483648=1).
   { apply Z.le_antisymm;[apply Z.lt_succ_r;apply Z.div_lt_upper_bound|apply Z.div_le_lower_bound];lia. }
   rewrite HQ. unfold boolz.
   destruct(D<?0)eqn:E;[reflexivity|apply Z.ltb_ge in E;lia].
 - rewrite (Z.mod_small D 4294967296) by lia. rewrite Z.div_small by lia. unfold boolz.
   destruct(D<?0)eqn:E;[apply Z.ltb_lt in E;lia|reflexivity].
Qed.
Lemma compare_difference a b c : (a-c<?b-c)=(a-b<?0).
Proof. apply Bool.eq_true_iff_eq. rewrite !Z.ltb_lt. lia. Qed.
Theorem split_sign_signed_less a b :
 0<=a<4294967296 -> 0<=b<4294967296 ->
 (if Z.eqb(sign32 a)(sign32 b) then sign32(norm 32(a-b)) else sign32 a)=
 boolz(signed_value 32 a<?signed_value 32 b).
Proof.
 intros HA HB. rewrite(sign32_threshold a HA),(sign32_threshold b HB).
 rewrite(sv_def a ltac:(change(0<=a<4294967296);exact HA)),
  (sv_def b ltac:(change(0<=b<4294967296);exact HB)).
 change (2^31)with 2147483648. change(2^32)with 4294967296.
 destruct(2147483648<=?a)eqn:EA;destruct(2147483648<=?b)eqn:EB;
 apply Z.leb_le in EA||apply Z.leb_gt in EA;
 apply Z.leb_le in EB||apply Z.leb_gt in EB;cbn[Z.eqb].
 - rewrite subtraction_sign by lia. now rewrite compare_difference.
 - unfold boolz. destruct(a-4294967296<?b)eqn:E;[reflexivity|apply Z.ltb_ge in E;lia].
 - unfold boolz. destruct(a<?b-4294967296)eqn:E;[apply Z.ltb_lt in E;lia|reflexivity].
 - rewrite subtraction_sign by lia. replace(a<?b)with(a-b<?0);[reflexivity|].
   apply Bool.eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
Qed.
End CPUSubSign32.
