(** Output-independent nonblocking trees, preserving original priority and masks.
    No CPU identifiers, reachable-state or word-format premises are used. *)
From Coq Require Import List Bool PeanoNat ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVOutputsFree
 Lang.ExtendedSVOutputsFreeProducer Lang.ExtendedSVMaskedReplayIdempotence
 Lang.ExtendedSVNBACaseProjection Lang.ExtendedSVCombIdempotence
 Lang.ExtendedSVInferredProducerCertificate.
Import ListNotations ExtendedSV ExtendedSVOutputsFree ExtendedSVOutputsFreeProducer
 ExtendedSVMaskedReplayIdempotence ExtendedSVNBACaseProjection
 ExtendedSVCombIdempotence ExtendedSVInferredProducerCertificate.
Module ExtendedSVNBAOutputsFreeProducer.

Fixpoint nba_output_free_stmtb spec st := match st with
 | SSkip => true
 | SAssign nba rhs (LVar w r) =>
     nba && supports_outputb spec w r && output_free_exprb spec rhs
 | SAssign _ _ _ => false
 | SSeq xs => forallb (nba_output_free_stmtb spec) xs
 | SIf guard yes no => output_free_exprb spec guard &&
     nba_output_free_stmtb spec yes && nba_output_free_stmtb spec no
 | SCase scr arms => output_free_exprb spec scr &&
     forallb (fun arm => output_free_keyb spec (fst arm) &&
       nba_output_free_stmtb spec (snd arm)) arms
 end.

Lemma selected_nba_output_free spec s value arms default :
 forallb (fun arm => output_free_keyb spec (fst arm) &&
   nba_output_free_stmtb spec (snd arm)) arms = true ->
 nba_output_free_stmtb spec default = true ->
 nba_output_free_stmtb spec (select_case_stmt s value arms default) = true.
Proof.
 induction arms as [|[key body] rest IH] in default |- *; cbn; [auto|].
 intros HC HD. apply andb_true_iff in HC as [HB HR].
 apply andb_true_iff in HB as [HK HF].
 destruct key as [e|]; [destruct (Z.eqb value (eval_expr s e))|]; auto.
Qed.

Definition ExecNBAOutputs spec es et :=
 OutsideOutputs spec (blocking_state es) (blocking_state et) /\
 pending_nba es = pending_nba et /\ emitted_updates es = emitted_updates et /\
 Forall (SupportedUpdate spec) (emitted_updates es).

Theorem actual_nba_outputs_free_execution spec fuel st es et :
 nba_output_free_stmtb spec st = true -> ExecNBAOutputs spec es et ->
 ExecNBAOutputs spec (exec_stmt fuel st es) (exec_stmt fuel st et).
Proof.
 induction fuel as [|fuel IH] in st,es,et |- *; [auto|].
 destruct st as [|nba rhs lhs|xs|guard yes no|scr arms]; cbn; intros HC HE.
 - exact HE.
 - destruct lhs as [w r|]; [|discriminate]. destruct nba; [|discriminate].
   apply andb_true_iff in HC as [HC HX].
   apply support_sound in HC.
   destruct HE as [HB [HP [HU HT]]].
   rewrite (outside_outputs_eval spec rhs (blocking_state es) (blocking_state et) HX HB).
   unfold ExecNBAOutputs; cbn. split; [exact HB|].
   split; [now rewrite HP|]. split; [now rewrite HU|].
   apply Forall_app. split; [exact HT|].
   constructor; [split; [reflexivity|exact HC]|constructor].
 - induction xs as [|st xs IHr] in es,et,HC,HE |- *; cbn in *; [exact HE|].
   apply andb_true_iff in HC as [HS HR]. apply IHr; [exact HR|now apply IH].
 - apply andb_true_iff in HC as [HG HN]. apply andb_true_iff in HG as [HG HY].
   destruct HE as [HB [HP [HU HT]]].
   rewrite (outside_outputs_eval spec guard (blocking_state es) (blocking_state et) HG HB).
   destruct (Z.eqb (eval_expr (blocking_state et) guard) 0); apply IH;
   [exact HN|repeat split; assumption|exact HY|repeat split; assumption].
 - apply andb_true_iff in HC as [HS HA]. destruct HE as [HB [HP [HU HT]]].
   rewrite (outside_outputs_eval spec scr (blocking_state es) (blocking_state et) HS HB).
   assert (HK : forallb (fun arm => output_free_keyb spec (fst arm)) arms = true).
   { apply forallb_forall. intros arm HI. apply forallb_forall with (x:=arm) in HA; [|exact HI].
     now apply andb_true_iff in HA as [HA _]. }
   rewrite (outputs_select_agree spec (blocking_state es) (blocking_state et)
     (eval_expr (blocking_state et) scr) arms SSkip HK HB).
   apply IH; [apply selected_nba_output_free; [exact HA|reflexivity]|repeat split; assumption].
Qed.

Lemma nba_pending_equals_emitted fuel st es :
 nba_onlyb st = true -> pending_nba es = emitted_updates es ->
 pending_nba (exec_stmt fuel st es) = emitted_updates (exec_stmt fuel st es).
Proof.
 induction fuel as [|fuel IH] in st,es |- *; [auto|].
 destruct st as [|nba rhs lhs|xs|guard yes no|scr arms]; cbn; intros HC HE.
 - exact HE.
 - subst nba. cbn. now rewrite HE.
 - induction xs as [|st xs IHr] in es,HC,HE |- *; cbn in *; [exact HE|].
   apply andb_true_iff in HC as [HS HR]. apply IHr; [exact HR|now apply IH].
 - apply andb_true_iff in HC as [HY HN].
   destruct (Z.eqb (eval_expr (blocking_state es) guard) 0); apply IH; assumption.
 - apply IH; [apply selected_nba; [exact HC|reflexivity]|exact HE].
Qed.

Theorem actual_nba_process_replays p proc s :
 nba_onlyb (process_body proc) = true ->
 run_process p s proc = apply_updates s (process_updates p s proc).
Proof.
 intro HC. unfold run_process,process_updates.
 pose proof (proj1 (nba_root_sound (statement_fuel p) (process_body proc)
   {|blocking_state:=s; pending_nba:=[]; emitted_updates:=[]|} 0%nat 0 HC)) as HB.
 pose proof (nba_pending_equals_emitted (statement_fuel p) (process_body proc)
   {|blocking_state:=s; pending_nba:=[]; emitted_updates:=[]|} HC eq_refl) as HP.
 cbn in HB. rewrite HB,HP. reflexivity.
Qed.

Theorem actual_nba_outputs_free_captured_updates spec p proc s t :
 nba_output_free_stmtb spec (process_body proc) = true -> OutsideOutputs spec s t ->
 process_updates p s proc = process_updates p t proc /\
 Forall (SupportedUpdate spec) (process_updates p s proc).
Proof.
 intros HC HS. unfold process_updates.
 pose proof (actual_nba_outputs_free_execution spec (statement_fuel p) (process_body proc)
   {|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|}
   {|blocking_state:=t;pending_nba:=[];emitted_updates:=[]|} HC
   ltac:(split; [exact HS|split; [reflexivity|split; [reflexivity|constructor]]])) as HE.
 exact (proj2 (proj2 HE)).
Qed.

Theorem actual_nba_outputs_free_producer_idempotent spec p proc :
 coherent_specb spec = true -> nba_onlyb (process_body proc) = true ->
 nba_output_free_stmtb spec (process_body proc) = true -> ProducerIdempotent p proc.
Proof.
 intros HM HN HC s.
 assert (HT : Forall (SupportedUpdate spec) (process_updates p s proc)).
 { exact (proj2 (actual_nba_outputs_free_captured_updates spec p proc s s HC (fun r HR=>eq_refl))). }
 rewrite !actual_nba_process_replays by exact HN.
 assert (HE : process_updates p (apply_updates s (process_updates p s proc)) proc = process_updates p s proc).
 { exact (proj1 (actual_nba_outputs_free_captured_updates spec p proc
     (apply_updates s (process_updates p s proc)) s HC
     (supported_replay_preserves_outside spec (process_updates p s proc) HT s))). }
 rewrite HE. apply original_mask_consistent_replay_is_idempotent.
 apply supported_updates_have_coherent_masks with (spec:=spec);
   [now apply coherent_specb_sound|exact HT].
Qed.

Definition inferred_nba_producerb proc :=
 let spec := inferred_outputs (process_body proc) in
 coherent_specb spec && nba_onlyb (process_body proc) &&
 nba_output_free_stmtb spec (process_body proc).

Theorem inferred_nba_producerb_sound p proc :
 inferred_nba_producerb proc = true -> ProducerIdempotent p proc.
Proof.
 unfold inferred_nba_producerb. intro H.
 apply andb_true_iff in H as [H HC]. apply andb_true_iff in H as [HM HN].
 exact (actual_nba_outputs_free_producer_idempotent
   (inferred_outputs (process_body proc)) p proc HM HN HC).
Qed.
End ExtendedSVNBAOutputsFreeProducer.
Print Assumptions ExtendedSVNBAOutputsFreeProducer.actual_nba_process_replays.
Print Assumptions ExtendedSVNBAOutputsFreeProducer.actual_nba_outputs_free_captured_updates.
Print Assumptions ExtendedSVNBAOutputsFreeProducer.actual_nba_outputs_free_producer_idempotent.
Print Assumptions ExtendedSVNBAOutputsFreeProducer.inferred_nba_producerb_sound.
