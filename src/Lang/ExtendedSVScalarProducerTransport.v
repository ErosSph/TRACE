(** True execution transport for scalar producers. Foreign captured updates
    commute with the producer only if they avoid its written root AND inputs. *)
From Coq Require Import List Bool PeanoNat.
Require Import Lang.ExtendedSV Lang.ExtendedSVAssignment
 Lang.ExtendedSVProducerAssignment Lang.ExtendedSVCombIdempotence
 Lang.ExtendedSVBlockingReplay Lang.ExtendedSVProcessSlice.
Import ExtendedSV ExtendedSVAssignment ExtendedSVProducerAssignment
 ExtendedSVCombIdempotence ExtendedSVBlockingReplay ExtendedSVProcessSlice ListNotations.
Module ExtendedSVScalarProducerTransport.
Theorem scalar_producer_commutes_foreign_update p proc nba expr width root update state:
 process_body proc=SAssign nba expr(LVar width root)->
 (0<statement_fuel p)%nat->update_signal update<>root->
 NoInputRoot(update_signal update)expr->
 run_process p(apply_update state update)proc=apply_update(run_process p state proc)update.
Proof.
 intros HB HF HW HI.
 rewrite !assignment_run_process with(nba:=nba)(rhs:=expr)(lhs:=LVar width root)by assumption.
 rewrite invisible_update_keeps_expression by exact HI.
 cbn[resolve_update resolve_lvalue]. apply apply_update_commute.
 cbn[update_signal]. exact HW.
Qed.
Theorem scalar_fixed_preserved_by_captured_updates p proc nba expr width root updates:
 process_body proc=SAssign nba expr(LVar width root)->
 (0<statement_fuel p)%nat->
 (forall u,In u updates->update_signal u<>root /\ NoInputRoot(update_signal u)expr)->
 forall state,ProducerFixed p proc state->ProducerFixed p proc(apply_updates state updates).
Proof.
 intros HB HF HA. induction updates as[|u us IH];intros state HS;[exact HS|].
 cbn[apply_updates]. apply IH.
 - intros v HV. apply HA. now right.
 - unfold ProducerFixed in *. rewrite scalar_producer_commutes_foreign_update with
    (nba:=nba)(expr:=expr)(width:=width)(root:=root).
   + now rewrite HS.
   + exact HB.
   + exact HF.
   + apply (proj1(HA u(or_introl eq_refl))).
   + apply (proj2(HA u(or_introl eq_refl))).
Qed.
Theorem actual_later_blocking_preserves_scalar_fixed p first later nba expr width root:
 process_body first=SAssign nba expr(LVar width root)->
 (0<statement_fuel p)%nat->
 Lang.ExtendedSVBlocking.ExtendedSVBlocking.blocking_onlyb(process_body later)=true->
 (forall r,In r(process_writers later)->r<>root /\ NoInputRoot r expr)->
 LaterPreservesFixed p first later.
Proof.
 intros HB HF HL HA state HS. unfold ProducerFixed.
 rewrite (actual_blocking_process_replays p later state HL).
 apply scalar_fixed_preserved_by_captured_updates with(nba:=nba)(expr:=expr)(width:=width)(root:=root);
 try assumption.
 intros u HU. apply HA. now apply process_emitted_writers in HU.
Qed.
Definition scalar_transportb first later:=match process_body first with
 |SAssign _ expr(LVar _ root)=>
 Lang.ExtendedSVBlocking.ExtendedSVBlocking.blocking_onlyb(process_body later)&&
 forallb(fun r=>negb(Nat.eqb r root)&&no_input_rootb r expr)(process_writers later)
 |_=>false end.
Theorem scalar_transportb_sound p first later:
 (0<statement_fuel p)%nat->scalar_transportb first later=true->
 LaterPreservesFixed p first later.
Proof.
 intros HF HC. destruct first as[k ev body line].
 destruct body as[|nba expr lhs|ss|g y n|e arms];try discriminate.
 destruct lhs;try discriminate. cbn[scalar_transportb process_body]in HC.
 apply andb_true_iff in HC as[HL HA].
 eapply actual_later_blocking_preserves_scalar_fixed;
 [reflexivity|exact HF|exact HL|].
 intros r HR. apply forallb_forall with(x:=r)in HA;[|exact HR].
 apply andb_true_iff in HA as[HW HI]. split.
 - apply Bool.negb_true_iff in HW. now apply Nat.eqb_neq.
 - now apply no_input_rootb_sound.
Qed.
End ExtendedSVScalarProducerTransport.
Print Assumptions ExtendedSVScalarProducerTransport.actual_later_blocking_preserves_scalar_fixed.
