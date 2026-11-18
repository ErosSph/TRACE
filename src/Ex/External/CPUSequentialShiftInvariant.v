(** Pure remaining-work invariant; real process/scheduler binding is separate. *)
From Coq Require Import ZArith Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Ex.External.CPUSequentialShiftMath
 Ex.External.CPUSequentialArithmeticShiftMath.
Import ExtendedSV ExtendedSVWordInvariant CPUSequentialShiftMath CPUSequentialArithmeticShiftMath.
Local Open Scope Z_scope.
Module CPUSequentialShiftInvariant.
Definition Remaining kind current amount target:=shift_math kind current amount=target.
Lemma signed_low32 x:norm 32(signed_value 32 x)=norm 32 x.
Proof.
 unfold signed_value;cbn[Nat.eqb Nat.pred].
 destruct(Z.testbit(norm 32 x)(Z.of_nat 31));[|apply norm_idempotent].
 rewrite norm_as_mod;change((norm 32 x-4294967296)mod 4294967296=norm 32 x).
 replace(norm 32 x-4294967296)with(norm 32 x+(-1)*4294967296)by ring.
 rewrite Z.mod_add by discriminate.
 change(norm 32 x mod 2^Z.of_nat 32=norm 32 x).
 rewrite <-norm_as_mod;apply norm_idempotent.
Qed.
Theorem shift_zero kind x:shift_math kind x 0=norm 32 x.
Proof.
 destruct kind;unfold shift_math;rewrite ?Z.shiftl_0_r,?Z.shiftr_0_r;
 [apply norm_idempotent|apply norm_idempotent|apply signed_low32].
Qed.
Theorem remaining_initial kind current amount:
 Remaining kind current amount(shift_math kind current amount).
Proof. reflexivity. Qed.
Theorem remaining_advance kind current amount target:0<amount->
 Remaining kind current amount target->
 Remaining kind(shift_math kind current(step_width amount))(amount-step_width amount)target.
Proof.
 intros HA HR;unfold Remaining in *.
 assert(HS:0<=step_width amount /\0<=amount-step_width amount).
 { unfold step_width;destruct(4<=?amount)eqn:HC;
   first[apply Z.leb_le in HC|apply Z.leb_gt in HC];lia. }
 rewrite sequential_shift_composes by tauto.
 replace(step_width amount+(amount-step_width amount))with amount by lia;exact HR.
Qed.
Theorem remaining_advance_and_rank kind current amount target:0<amount->
 Remaining kind current amount target->
 Remaining kind(shift_math kind current(step_width amount))(amount-step_width amount)target /\
 (remaining_rank(amount-step_width amount)<remaining_rank amount)%nat.
Proof.
 intros HA HR;split;[exact(remaining_advance kind current amount target HA HR)|
 exact(remaining_rank_strictly_decreases amount HA)].
Qed.
Theorem remaining_finished kind current target:Remaining kind current 0 target->norm 32 current=target.
Proof. unfold Remaining;rewrite shift_zero;tauto. Qed.
End CPUSequentialShiftInvariant.
Print Assumptions CPUSequentialShiftInvariant.remaining_advance_and_rank.
Print Assumptions CPUSequentialShiftInvariant.remaining_finished.
