(** One ordered combinational pass is a real fixed point when each actual
    producer is idempotent and later producers preserve its established fixed
    state. Not a graph-only claim: concrete run_process obligations remain. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV.
Import ExtendedSV ListNotations.
Module ExtendedSVCombIdempotence.
Definition ProducerFixed p proc state:=run_process p state proc=state.
Definition ProducerIdempotent p proc:=forall state,
 run_process p(run_process p state proc)proc=run_process p state proc.
Definition LaterPreservesFixed p first later:=forall state,
 ProducerFixed p first state->ProducerFixed p first(run_process p state later).
Fixpoint OrderedProducerCertificate p order:Prop:=match order with
 |[]=>True|first::rest=>ProducerIdempotent p first /\
 Forall(LaterPreservesFixed p first)rest /\ OrderedProducerCertificate p rest end.
Lemma fold_preserves_producer_fixed p first order:
 Forall(LaterPreservesFixed p first)order->forall state,
 ProducerFixed p first state->ProducerFixed p first(fold_left(run_process p)order state).
Proof.
 intros H. induction H;intros state HS;[exact HS|].
 cbn[fold_left]. apply IHForall. now apply H.
Qed.
Theorem ordered_producers_make_pass_idempotent p order:
 OrderedProducerCertificate p order->forall state,
 fold_left(run_process p)order(fold_left(run_process p)order state)=
 fold_left(run_process p)order state.
Proof.
 induction order as[|first rest IH];intros H state;[reflexivity|].
 destruct H as[Hfirst[Hlater Htail]]. cbn[fold_left].
 pose proof(fold_preserves_producer_fixed p first rest Hlater
 (run_process p state first)(Hfirst state))as Hfixed.
 unfold ProducerFixed in Hfixed. rewrite Hfixed. now apply IH.
Qed.
Theorem certified_original_comb_round_is_idempotent p:
 OrderedProducerCertificate p(filter is_comb(processes p))->forall state,
 comb_round p(comb_round p state)=comb_round p state.
Proof. unfold comb_round. apply ordered_producers_make_pass_idempotent. Qed.
Theorem certified_original_fuel1_candidate_is_LFP p:
 lfp_fuel p=1%nat->OrderedProducerCertificate p(filter is_comb(processes p))->
 forall seed,CombLFP p seed(lfp_candidate p seed).
Proof.
 intros Hfuel Hcert seed. apply CombLFP_intro with(n:=1%nat).
 - unfold lfp_candidate. now rewrite Hfuel.
 - unfold lfp_candidate. rewrite Hfuel. cbn[comb_iter].
   apply certified_original_comb_round_is_idempotent. exact Hcert.
Qed.
End ExtendedSVCombIdempotence.
Print Assumptions ExtendedSVCombIdempotence.certified_original_fuel1_candidate_is_LFP.
