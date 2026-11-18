(** Complete multi-output actual process idempotence: output-free capture plus
    coherent root widths and priority-preserving masked replay algebra. *)
From Coq Require Import List Bool PeanoNat.
Require Import Lang.ExtendedSV Lang.ExtendedSVOutputsFree
 Lang.ExtendedSVMaskedReplayIdempotence Lang.ExtendedSVBlocking Lang.ExtendedSVBlockingReplay
 Lang.ExtendedSVCombIdempotence Lang.ExtendedSVRootProjection.
Import ExtendedSV ExtendedSVOutputsFree ExtendedSVMaskedReplayIdempotence
 ExtendedSVBlocking ExtendedSVBlockingReplay ExtendedSVCombIdempotence ExtendedSVRootProjection ListNotations.
Module ExtendedSVOutputsFreeProducer.
Definition CoherentSpec(spec:OutputSpec):=forall w1 r1 w2 r2,
 In(w1,r1)spec->In(w2,r2)spec->r1=r2->w1=w2.
Definition coherent_specb(spec:OutputSpec):=
 forallb(fun a=>forallb(fun b=>negb(Nat.eqb(snd a)(snd b))||Nat.eqb(fst a)(fst b))spec)spec.
Lemma coherent_specb_sound spec:coherent_specb spec=true->CoherentSpec spec.
Proof.
 intros H w1 r1 w2 r2 H1 H2 HR. unfold coherent_specb in H.
 apply forallb_forall with(x:=(w1,r1))in H;[|exact H1].
 apply forallb_forall with(x:=(w2,r2))in H;[|exact H2]. cbn in H.
 subst r2. rewrite Nat.eqb_refl in H. cbn in H. now apply Nat.eqb_eq.
Qed.
Lemma supported_updates_have_coherent_masks spec updates:
 CoherentSpec spec->Forall(SupportedUpdate spec)updates->SameRootSameMask updates.
Proof.
 intros HC HT u v HU HV HR. apply Forall_forall with(x:=u)in HT as Htu;[|exact HU].
 apply Forall_forall with(x:=v)in HT as Htv;[|exact HV].
 destruct Htu as[HOu HIu],Htv as[HOv HIv]. split;[congruence|].
 exact(HC(update_width u)(update_signal u)(update_width v)(update_signal v)HIu HIv HR).
Qed.
Lemma supported_replay_preserves_outside spec updates:
 Forall(SupportedUpdate spec)updates->forall state,
 OutsideOutputs spec(apply_updates state updates)state.
Proof.
 intro H. induction H;intros state r HR;cbn;[reflexivity|].
 rewrite IHForall by exact HR. rewrite read_signal_apply_update_other;[reflexivity|].
 destruct H as[HO HI]. intro E. subst r.
 pose proof(support_owns spec(update_width x)(update_signal x)HI). congruence.
Qed.
Theorem actual_outputs_free_producer_idempotent spec p proc:
 coherent_specb spec=true->output_free_stmtb spec(process_body proc)=true->
 blocking_onlyb(process_body proc)=true->ProducerIdempotent p proc.
Proof.
 intros HM HC HB state.
 assert(HT:Forall(SupportedUpdate spec)(process_updates p state proc)).
 { exact(proj2(actual_outputs_free_captured_updates spec p proc state state HC(fun r HR=>eq_refl))). }
 rewrite !actual_blocking_process_replays by exact HB.
 assert(HE:process_updates p(apply_updates state(process_updates p state proc))proc=
  process_updates p state proc).
 { exact(proj1(actual_outputs_free_captured_updates spec p proc
    (apply_updates state(process_updates p state proc))state HC
    (supported_replay_preserves_outside spec(process_updates p state proc)HT state))). }
 rewrite HE. apply original_mask_consistent_replay_is_idempotent.
 apply supported_updates_have_coherent_masks with(spec:=spec);[now apply coherent_specb_sound|exact HT].
Qed.
End ExtendedSVOutputsFreeProducer.
Print Assumptions ExtendedSVOutputsFreeProducer.actual_outputs_free_producer_idempotent.
