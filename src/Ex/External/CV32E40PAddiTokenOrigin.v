(** Unbounded provenance of the real retirement monitor's pending token.
    No operand correctness, no-overwrite or future-retirement premise is used.
    This does NOT assert that the physical ID/EX slot follows the monitor. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Ex.External.CV32E40PReq39Trace
  Ex.External.CV32E40PAddiReachability.
Import ExtendedSV CV32E40PReq39Trace CV32E40PAddiReachability.
Module CV32E40PAddiTokenOrigin.
  #[local] Opaque full_cycle_image environment_state_image.
  Definition issued image s := issue_at (environment_state_image image (physical_state s)).
  Definition completed image s := alu_completes (environment_state_image image (physical_state s)).
  Lemma pending_next image s : pending_token (advance_retirement image s) =
    match issued image s with
    | Some t => Some t
    | None => if completed image s then None else pending_token s
    end.
  Proof. reflexivity. Qed.
  #[local] Opaque advance_retirement reset_retirement issued completed.
  Inductive TokenResidence image (origin : RetirementState) (token : IssueToken) :
      nat -> RetirementState -> Prop :=
  | residence_accept : issued image origin = Some token ->
      TokenResidence image origin token 1 (advance_retirement image origin)
  | residence_wait : forall n s,
      TokenResidence image origin token n s ->
      issued image s = None -> completed image s = false ->
      TokenResidence image origin token (S n) (advance_retirement image s).

  Theorem residence_is_actual_cycle_path image origin token n s :
    TokenResidence image origin token n s ->
    0 < n /\ s = retirement_cycles image n origin.
  Proof.
    intros H. induction H as [Hissue|n s Hres [Hpositive Hpath] Hnone Hwait].
    - split; [lia|reflexivity].
    - split; [lia|]. rewrite Hpath. apply retirement_cycles_snoc.
  Qed.
  Theorem residence_keeps_pending_token image origin token n s :
    TokenResidence image origin token n s -> pending_token s = Some token.
  Proof.
    intros H. induction H as [Hissue|n s Hres IH Hnone Hwait];
      rewrite pending_next.
    - now rewrite Hissue.
    - now rewrite Hnone, Hwait.
  Qed.
  Theorem residence_has_actual_issue image origin token n s :
    TokenResidence image origin token n s -> issued image origin = Some token.
  Proof. intros H. induction H; assumption. Qed.

  (** The induction is over ALL ResetReachable states, not over a test bound. *)
  Theorem every_pending_token_has_reachable_origin image s :
    ResetReachable image s -> forall token, pending_token s = Some token ->
    exists origin n, ResetReachable image origin /\ TokenResidence image origin token n s.
  Proof.
    intros Hreach. induction Hreach as [|s Hreach IH]; intros token Htoken.
    - change (None = Some token) in Htoken. discriminate.
    - rewrite pending_next in Htoken.
      destruct (issued image s) as [fresh|] eqn:Hissue.
      + inversion Htoken; subst fresh. exists s, 1. split; [exact Hreach|].
        constructor. exact Hissue.
      + destruct (completed image s) eqn:Hcomplete; [discriminate|].
        destruct (IH token Htoken) as (origin&n&Horigin&Hres).
        exists origin, (S n). split; [exact Horigin|].
        econstructor; eassumption.
  Qed.

  Lemma retired_token_was_pending image s token :
    retiring_token image s = Some token -> pending_token s = Some token.
  Proof.
    unfold retiring_token. destruct (alu_completes (environment_state_image image (physical_state s)));
      [trivial|discriminate].
  Qed.
  Theorem every_retirement_has_reachable_issue image pre n token post :
    NextRetirement image pre n token post -> ResetReachable image pre ->
    exists origin, ResetReachable image origin /\ issued image origin = Some token.
  Proof.
    intros Hnext. induction Hnext as [s token Hretire|s n token post Hwait Hnext IH]; intros Hreach.
    - destruct (every_pending_token_has_reachable_origin image s Hreach token
        (retired_token_was_pending image s token Hretire)) as (origin&k&Horigin&Hres).
      exists origin. split; [exact Horigin|]. eapply residence_has_actual_issue; exact Hres.
    - apply IH. now constructor.
  Qed.
  #[local] Transparent issued.
  Theorem issued_token_records_actual_id_ports image s token : issued image s = Some token ->
    token_pc token = read_signal (environment_state_image image (physical_state s)) 121 /\
    token_instruction token = read_signal (environment_state_image image (physical_state s)) 718.
  Proof.
    unfold issued, issue_at.
    destruct (andb _ _); [intros H; inversion H; subst; split; reflexivity|discriminate].
  Qed.
  Print Assumptions every_pending_token_has_reachable_origin.
  Print Assumptions every_retirement_has_reachable_issue.
End CV32E40PAddiTokenOrigin.
