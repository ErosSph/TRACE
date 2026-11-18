(** Connect checked RTL observations to first-retirement and prefix safety.
    No ISA/post-effect certificate is assumed in these theorems. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CV32E40PReq39Trace.
Require Import Ex.External.CV32E40PAddiReachability.
Require Import Ex.External.CV32E40PAddiCommitTrace.
Import ListNotations CV32E40PReq39Trace CV32E40PAddiReachability CV32E40PAddiCommitTrace.
Local Open Scope Z_scope.

Module CV32E40PAddiCommitSchedule.
  #[local] Opaque full_cycle_image environment_state_image advance_retirement reset_retirement
    observation issue_at alu_completes.
  Definition cycle n := retirement_cycles image n reset_retirement.

  Lemma cycle_next : forall n, advance_retirement image (cycle n) = cycle (S n).
  Proof. intros. apply retirement_cycles_snoc. Qed.
  #[local] Opaque cycle.

  Lemma nth_observations : forall n k s, (k < n)%nat ->
      nth k (observations n s) empty_observation =
      observation (retirement_cycles image k s).
  Proof.
    intros n. induction n; intros k s H; [lia|].
    destruct k; cbn [observations nth retirement_cycles]; [reflexivity|].
    apply IHn. lia.
  Qed.

  Theorem observation_at_cycle : forall k, (k < 9)%nat ->
      observation (cycle k) = nth k expected empty_observation.
  Proof.
    intros k Hk. Transparent cycle. unfold cycle.
    rewrite <- nth_observations with (n := 9%nat) by exact Hk.
    now rewrite real_reset_execution_observations.
  Qed.
  #[local] Opaque cycle.

  Definition no_overwriteb (o : Observation) :=
    let '(issued, completed, pending, _, _, _, _) := o in
    match issued, pending with Some _, Some _ => completed | _, _ => true end.
  Definition retired_observation (o : Observation) :=
    let '(_, completed, pending, _, _, _, _) := o in
    if completed then pending else None.

  Lemma observation_no_overwrite_sound : forall s,
      no_overwriteb (observation s) = true -> NoTokenOverwrite image s.
  Proof.
    intros s. Transparent observation issue_at alu_completes.
    unfold observation, no_overwriteb, NoTokenOverwrite.
    destruct (issue_at (environment_state_image image (physical_state s)));
      destruct (pending_token s); cbn; congruence.
  Qed.
  #[local] Opaque observation issue_at alu_completes.

  Lemma retiring_is_observed : forall s,
      retiring_token image s = retired_observation (observation s).
  Proof. Transparent observation. reflexivity. Qed.
  #[local] Opaque observation.

  Theorem no_token_overwrite_in_checked_prefix : forall k, (k < 9)%nat ->
      NoTokenOverwrite image (cycle k).
  Proof.
    intros k Hk. apply observation_no_overwrite_sound.
    rewrite observation_at_cycle by exact Hk.
    do 9 (destruct k as [|k]; [reflexivity|]). lia.
  Qed.

  Definition NoSpuriousCompletion (s : RetirementState) : Prop :=
    alu_completes (environment_state_image image (physical_state s)) = true ->
    pending_token s <> None.
  Definition completion_matchedb (o : Observation) :=
    let '(_, completed, pending, _, _, _, _) := o in
    match pending with Some _ => true | None => negb completed end.
  Lemma observation_completion_matched_sound : forall s,
      completion_matchedb (observation s) = true -> NoSpuriousCompletion s.
  Proof.
    intros s. Transparent observation.
    unfold observation, completion_matchedb, NoSpuriousCompletion.
    destruct (pending_token s);
      destruct (alu_completes (environment_state_image image (physical_state s)));
      cbn; congruence.
  Qed.
  #[local] Opaque observation.
  Theorem no_spurious_completion_in_checked_prefix : forall k, (k < 9)%nat ->
      NoSpuriousCompletion (cycle k).
  Proof.
    intros k Hk. apply observation_completion_matched_sound.
    rewrite observation_at_cycle by exact Hk.
    do 9 (destruct k as [|k]; [reflexivity|]). lia.
  Qed.

  Theorem token_safety_in_checked_prefix : forall k, (k < 9)%nat ->
      NoTokenOverwrite image (cycle k) /\ NoSpuriousCompletion (cycle k).
  Proof.
    intros. split; [apply no_token_overwrite_in_checked_prefix|
      apply no_spurious_completion_in_checked_prefix]; assumption.
  Qed.

  Lemma retirement_at_cycle : forall k, (k < 9)%nat ->
      retiring_token image (cycle k) =
        retired_observation (nth k expected empty_observation).
  Proof. intros. rewrite retiring_is_observed, observation_at_cycle by assumption. reflexivity. Qed.

  Lemma wait_at_cycle : forall k n t post,
      retiring_token image (cycle k) = None ->
      NextRetirement image (cycle (S k)) n t post ->
      NextRetirement image (cycle k) (S n) t post.
  Proof. intros. apply retire_wait; [assumption|]. now rewrite cycle_next. Qed.
  Lemma retire_at_cycle : forall k t,
      retiring_token image (cycle k) = Some t ->
      NextRetirement image (cycle k) 1 t (cycle (S k)).
  Proof. intros. rewrite <- cycle_next. now apply retire_now. Qed.

  Theorem first_real_retirement :
      NextRetirement image (cycle 0) 6 (token 0 1048723) (cycle 6).
  Proof.
    do 5 (apply wait_at_cycle; [rewrite retirement_at_cycle by lia; reflexivity|]).
    apply retire_at_cycle. rewrite retirement_at_cycle by lia. reflexivity.
  Qed.
  Theorem second_real_retirement :
      NextRetirement image (cycle 6) 1 (token 4 1081491) (cycle 7).
  Proof. apply retire_at_cycle. rewrite retirement_at_cycle by lia. reflexivity. Qed.

  Theorem entire_prefix_is_reset_reachable : forall k, ResetReachable image (cycle k).
  Proof. intros. Transparent cycle. unfold cycle. apply reachable_after_cycles. constructor. Qed.
  #[local] Opaque cycle.

  Theorem two_commits_do_not_assume_a_poststate_certificate :
      ResetReachable image (cycle 0) /\
      NextRetirement image (cycle 0) 6 (token 0 1048723) (cycle 6) /\
      ResetReachable image (cycle 6) /\ NoTokenOverwrite image (cycle 6) /\
      NextRetirement image (cycle 6) 1 (token 4 1081491) (cycle 7) /\
      ResetReachable image (cycle 7) /\ NoTokenOverwrite image (cycle 7).
  Proof.
    split; [apply entire_prefix_is_reset_reachable|].
    split; [exact first_real_retirement|].
    split; [apply entire_prefix_is_reset_reachable|].
    split; [apply no_token_overwrite_in_checked_prefix; lia|].
    split; [exact second_real_retirement|].
    split; [apply entire_prefix_is_reset_reachable|].
    apply no_token_overwrite_in_checked_prefix. lia.
  Qed.
End CV32E40PAddiCommitSchedule.
