(** Actual-fuel definite assignment plus coherent captured masks proves a
    state-threaded blocking producer idempotent. Not a fuel-independent rule. *)
From Coq Require Import List Bool PeanoNat ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVKnownInputs Lang.ExtendedSVKnownCapture
 Lang.ExtendedSVExprAgreement Lang.ExtendedSVInferredDependencies
 Lang.ExtendedSVInferredProducerCertificate Lang.ExtendedSVOutputsFree
 Lang.ExtendedSVOutputsFreeProducer Lang.ExtendedSVBlocking
 Lang.ExtendedSVBlockingReplay Lang.ExtendedSVMaskedReplayIdempotence
 Lang.ExtendedSVCombIdempotence.
Import ListNotations ExtendedSV ExtendedSVKnownInputs ExtendedSVKnownCapture
 ExtendedSVExprAgreement ExtendedSVInferredDependencies ExtendedSVInferredProducerCertificate
 ExtendedSVOutputsFree ExtendedSVOutputsFreeProducer ExtendedSVBlocking
 ExtendedSVBlockingReplay ExtendedSVMaskedReplayIdempotence ExtendedSVCombIdempotence.
Module ExtendedSVKnownProducer.

Fixpoint whole_outputsb spec st := match st with
 | SSkip => true
 | SAssign _ _ (LVar w r) => supports_outputb spec w r
 | SAssign _ _ _ => false
 | SSeq xs => forallb (whole_outputsb spec) xs
 | SIf _ yes no => whole_outputsb spec yes && whole_outputsb spec no
 | SCase _ arms => forallb (fun arm => whole_outputsb spec (snd arm)) arms
 end.

Lemma selected_whole_outputs spec s value arms default :
 forallb (fun arm=>whole_outputsb spec (snd arm)) arms=true ->
 whole_outputsb spec default=true ->
 whole_outputsb spec (select_case_stmt s value arms default)=true.
Proof.
 induction arms as [|[key body] rest IH] in default |- *; cbn; [auto|].
 intros HC HD. apply andb_true_iff in HC as [HB HR].
 destruct key as [e|]; [destruct (Z.eqb value (eval_expr s e))|]; auto.
Qed.

Theorem actual_whole_output_execution spec fuel st es :
 whole_outputsb spec st=true -> Forall (SupportedUpdate spec) (emitted_updates es) ->
 Forall (SupportedUpdate spec) (emitted_updates (exec_stmt fuel st es)).
Proof.
 induction fuel as [|fuel IH] in st,es |- *; [auto|].
 destruct st as [|nba rhs lhs|xs|guard yes no|scr arms]; cbn; intros HC HT.
 - exact HT.
 - destruct lhs as [w r|]; [|discriminate]. apply support_sound in HC.
   destruct nba; cbn.
   + apply Forall_app. split; [exact HT|].
     constructor; [split; [reflexivity|exact HC]|constructor].
   + apply Forall_app. split; [exact HT|].
     constructor; [split; [reflexivity|exact HC]|constructor].
 - induction xs as [|st xs IHr] in es,HC,HT |- *; cbn in *; [exact HT|].
   apply andb_true_iff in HC as [HS HR]. apply IHr; [exact HR|now apply IH].
 - apply andb_true_iff in HC as [HY HN].
   destruct (Z.eqb (eval_expr (blocking_state es) guard) 0); apply IH; assumption.
 - apply IH; [apply selected_whole_outputs; [exact HC|reflexivity]|exact HT].
Qed.

Theorem actual_whole_output_updates spec p proc s :
 whole_outputsb spec (process_body proc)=true ->
 Forall (SupportedUpdate spec) (process_updates p s proc).
Proof.
 intro HC. unfold process_updates.
 apply actual_whole_output_execution; [exact HC|constructor].
Qed.

Lemma external_inputs_outside proc w r :
 In (w,r) (external_inputs proc) ->
 owns_rootb (inferred_outputs (process_body proc)) r=false.
Proof.
 intro HI. unfold external_inputs in HI. apply filter_In in HI as [HI HN].
 apply negb_true_iff in HN. cbn in HN. unfold owns_rootb.
 assert (HE:forall xs:list(nat*signal),
   existsb (fun out=>Nat.eqb (snd out) r) xs=existsb (fun out=>Nat.eqb r (snd out)) xs).
 { intro xs. induction xs as [|a xs IH]; cbn; [reflexivity|].
   now rewrite Nat.eqb_sym,IH. }
 rewrite HE. exact HN.
Qed.

Definition known_producerb p proc :=
 let spec:=inferred_outputs (process_body proc) in
 coherent_specb spec && whole_outputsb spec (process_body proc) &&
 blocking_onlyb (process_body proc) &&
 match infer_known (statement_fuel p) (external_inputs proc) (process_body proc) with
 | Some _=>true | None=>false end.

Theorem known_producerb_sound p proc : known_producerb p proc=true -> ProducerIdempotent p proc.
Proof.
 unfold known_producerb. intro H.
 apply andb_true_iff in H as [H HK]. apply andb_true_iff in H as [H HB].
 apply andb_true_iff in H as [HM HT].
 destruct (infer_known (statement_fuel p) (external_inputs proc) (process_body proc))
   as [output|] eqn:HC; [|discriminate].
 intro s.
 pose proof (actual_whole_output_updates (inferred_outputs (process_body proc)) p proc s HT) as HU.
 assert (HA:InputsAgree (apply_updates s (process_updates p s proc)) s (external_inputs proc)).
 { intros w r HI.
   rewrite (supported_replay_preserves_outside (inferred_outputs (process_body proc))
     (process_updates p s proc) HU s r (external_inputs_outside proc w r HI)).
   reflexivity. }
 pose proof (actual_known_captured_updates p proc (external_inputs proc) output
   (apply_updates s (process_updates p s proc)) s HC HA) as HE.
 rewrite !actual_blocking_process_replays by exact HB.
 rewrite HE. apply original_mask_consistent_replay_is_idempotent.
 apply supported_updates_have_coherent_masks with (spec:=inferred_outputs (process_body proc));
   [now apply coherent_specb_sound|exact HU].
Qed.

Theorem checked_known_producers p order :
 Forall (ProducerIdempotent p) (filter (known_producerb p) order).
Proof.
 apply Forall_forall. intros proc HI. apply filter_In in HI as [_ HC].
 exact (known_producerb_sound p proc HC).
Qed.

Theorem known_residual_complete p order :
 filter (fun proc=>negb(known_producerb p proc)) order=[] ->
 Forall (ProducerIdempotent p) order.
Proof.
 intro HE. apply complete_filtered_exception with (f:=known_producerb p).
 - exact (checked_known_producers p order).
 - rewrite HE. constructor.
Qed.
End ExtendedSVKnownProducer.
Print Assumptions ExtendedSVKnownProducer.actual_whole_output_updates.
Print Assumptions ExtendedSVKnownProducer.known_producerb_sound.
Print Assumptions ExtendedSVKnownProducer.checked_known_producers.
Print Assumptions ExtendedSVKnownProducer.known_residual_complete.
