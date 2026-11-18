(** Preserve an existing field's exact ISA cut when an older prefix retires
    and new tokens are admitted. Actual queue/control transitions are separate
    hardware evidence; arbitrary deletion or reordering is not permitted. *)
From Coq Require Import List Arith Lia.
Require Import Ex.External.CPUReferenceCuts Ex.External.CPUGeneratedJointTemplate.
Import ListNotations CPUReferenceCuts CPUGeneratedJointTemplate.
Module CPUReferenceCutTransfer.
Section Transfer.
Context {Architecture Token:Type}.
Variable effect:Token->Architecture->option Architecture.

Theorem before_retire retiring kept index token before initial advanced:
 EffectChain effect initial retiring advanced ->
 BeforeToken effect initial(retiring++kept)(length retiring+index)token before ->
 BeforeToken effect advanced kept index token before.
Proof.
 revert initial advanced;induction retiring as[|head rest IH];intros initial advanced HC HT.
 - cbn in HT;inversion HC;subst;exact HT.
 - inversion HC as[|a t middle ts final HE HR];subst.
   destruct HT as[HN [HB HP]]. cbn in HN,HB,HP.
   inversion HP as[|a t other ts final HE' HR'];subst.
   assert(middle=other)by congruence;subst other.
   apply(IH middle advanced HR);split;[exact HN|];split;[cbn;lia|exact HR'].
Qed.

Theorem before_append initial pending index token before added:
 BeforeToken effect initial pending index token before ->
 BeforeToken effect initial(pending++added)index token before.
Proof.
 intros[HN [HB HC]];split.
 - rewrite nth_error_app1;[exact HN|].
   apply nth_error_Some;rewrite HN;discriminate.
 - split;[rewrite app_length;lia|].
   rewrite firstn_app.
   assert(HZ:index-length pending=0)by lia.
   rewrite HZ;cbn;now rewrite app_nil_r.
Qed.

Theorem before_cycle initial advanced retiring kept added index token before:
 EffectChain effect initial retiring advanced ->
 BeforeToken effect initial(retiring++kept)(length retiring+index)token before ->
 BeforeToken effect advanced(kept++added)index token before.
Proof. intros HC HT;apply before_append;exact(before_retire retiring kept index token before initial advanced HC HT). Qed.

Theorem field_cycle {Value:Type}(project:Architecture->Value)
 initial advanced retiring kept added index token value:
 EffectChain effect initial retiring advanced ->
 FieldAtToken effect project initial(retiring++kept)(length retiring+index)token value ->
 FieldAtToken effect project advanced(kept++added)index token value.
Proof.
 intros HC[before[HT HV]];exists before;split;[|exact HV].
 exact(before_cycle initial advanced retiring kept added index token before HC HT).
Qed.
End Transfer.
End CPUReferenceCutTransfer.
Print Assumptions CPUReferenceCutTransfer.before_cycle.
Print Assumptions CPUReferenceCutTransfer.field_cycle.
