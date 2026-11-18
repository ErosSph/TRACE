(** Reset reachability and first retirement, independent of ISA correctness.
    A ghost token carries the PC/instruction accepted by ID until EX completes.
    In particular rd=x0 still retires; RF write-enable is not a commit signal.
    These definitions do NOT assert that the pipeline never loses a token or
    that the ALU result is correct. Those are separate invariants to prove. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV.
Require Import Ex.External.CV32E40PReq39Trace.
Import ExtendedSV CV32E40PReq39Trace.

Module CV32E40PAddiReachability.
  #[local] Opaque full_cycle_image environment_state_image trace0.
  Record IssueToken := { token_pc : Z; token_instruction : Z }.
  Record RetirementState := {
    physical_state : TraceState;
    pending_token : option IssueToken;
    architectural_cursor : Z
  }.

  Definition issue_at (driven : State) : option IssueToken :=
    if andb (negb (Z.eqb (read_signal driven 222) 0))
            (negb (Z.eqb (read_signal driven 122) 0))
    then Some {| token_pc := read_signal driven 121;
                 token_instruction := read_signal driven 718 |}
    else None.

  Definition alu_completes (driven : State) : bool :=
    andb (negb (Z.eqb (read_signal driven 223) 0))
         (negb (Z.eqb (read_signal driven 135) 0)).

  Definition retiring_token (image : InstructionImage) (s : RetirementState)
      : option IssueToken :=
    if alu_completes (environment_state_image image (physical_state s))
    then pending_token s else None.

  Definition advance_retirement (image : InstructionImage) (s : RetirementState)
      : RetirementState :=
    let driven := environment_state_image image (physical_state s) in
    {| physical_state := full_cycle_image image (physical_state s);
       architectural_cursor :=
         if alu_completes driven then
           match pending_token s with
           | Some t => (token_pc t + 4) mod 2^32
           | None => architectural_cursor s
           end
         else architectural_cursor s;
       pending_token := match issue_at driven with
         | Some t => Some t
         | None => if alu_completes driven then None else pending_token s
         end |}.

  Definition reset_retirement : RetirementState :=
    {| physical_state := trace0; pending_token := None; architectural_cursor := 0 |}.

  Lemma advance_physical : forall image s,
      physical_state (advance_retirement image s) =
        full_cycle_image image (physical_state s).
  Proof. reflexivity. Qed.

  #[local] Opaque advance_retirement reset_retirement.

  Inductive ResetReachable (image : InstructionImage) : RetirementState -> Prop :=
  | reachable_reset : ResetReachable image reset_retirement
  | reachable_cycle : forall s, ResetReachable image s ->
      ResetReachable image (advance_retirement image s).

  Fixpoint retirement_cycles (image : InstructionImage) (n : nat)
      (s : RetirementState) : RetirementState :=
    match n with
    | O => s
    | S n' => retirement_cycles image n' (advance_retirement image s)
    end.

  Lemma retirement_cycles_snoc : forall image k s,
      advance_retirement image (retirement_cycles image k s) =
      retirement_cycles image (S k) s.
  Proof.
    intros image k. induction k; intros s.
    - reflexivity.
    - change (advance_retirement image
        (retirement_cycles image k (advance_retirement image s)) =
        retirement_cycles image (S k) (advance_retirement image s)).
      exact (IHk (advance_retirement image s)).
  Qed.

  Lemma reachable_after_cycles : forall image n s,
      ResetReachable image s ->
      ResetReachable image (retirement_cycles image n s).
  Proof.
    intros image n. induction n; intros s H.
    - exact H.
    - apply IHn. now apply reachable_cycle.
  Qed.

  Theorem reachable_exactly_real_reset_execution : forall image s,
      ResetReachable image s <->
      exists n, s = retirement_cycles image n reset_retirement.
  Proof.
    intros image s. split.
    - intros H. induction H as [|s H [n Hn]].
      + exists 0. reflexivity.
      + exists (S n). subst s. apply retirement_cycles_snoc.
    - intros [n ->]. apply reachable_after_cycles. constructor.
  Qed.

  Theorem monitored_execution_is_original_scheduler : forall image n s,
      physical_state (retirement_cycles image n s) =
        cycles_image image n (physical_state s).
  Proof.
    intros image n. induction n; intros s.
    - reflexivity.
    - cbn [retirement_cycles cycles_image].
      rewrite IHn, advance_physical. reflexivity.
  Qed.

  (** This is the first observed retirement, not just an arbitrary positive
      number of cycles. Wait constructors explicitly rule out earlier events. *)
  Inductive NextRetirement (image : InstructionImage) :
      RetirementState -> nat -> IssueToken -> RetirementState -> Prop :=
  | retire_now : forall s token,
      retiring_token image s = Some token ->
      NextRetirement image s 1 token (advance_retirement image s)
  | retire_wait : forall s n token post,
      retiring_token image s = None ->
      NextRetirement image (advance_retirement image s) n token post ->
      NextRetirement image s (S n) token post.

  Theorem next_retirement_has_real_positive_path : forall image pre n token post,
      NextRetirement image pre n token post ->
      (0 < n)%nat /\ post = retirement_cycles image n pre.
  Proof.
    intros image pre n token post H. induction H; cbn; intuition lia.
  Qed.

  Theorem next_retirement_preserves_reachability : forall image pre n token post,
      NextRetirement image pre n token post ->
      ResetReachable image pre -> ResetReachable image post.
  Proof.
    intros image pre n token post H. induction H; auto using reachable_cycle.
  Qed.

  Theorem next_retirement_unique : forall image pre n token post,
      NextRetirement image pre n token post ->
      forall n' token' post', NextRetirement image pre n' token' post' ->
        n = n' /\ token = token' /\ post = post'.
  Proof.
    intros image pre n token post H. induction H; intros n' token' post' H'.
    - inversion H'; subst; try congruence. repeat split; congruence.
    - inversion H'; subst; try congruence.
      match goal with
      | Hnext : NextRetirement image (advance_retirement image s) _ _ _ |- _ =>
        specialize (IHNextRetirement _ _ _ Hnext)
      end.
      intuition congruence.
  Qed.

  (** An independently stated safety obligation: ID cannot overwrite an
      outstanding instruction unless EX completes it on this same edge. *)
  Definition NoTokenOverwrite image s : Prop :=
    pending_token s <> None ->
    issue_at (environment_state_image image (physical_state s)) <> None ->
    alu_completes (environment_state_image image (physical_state s)) = true.

  Theorem a_waiting_token_is_preserved : forall image s token,
      pending_token s = Some token ->
      issue_at (environment_state_image image (physical_state s)) = None ->
      alu_completes (environment_state_image image (physical_state s)) = false ->
      pending_token (advance_retirement image s) = Some token.
  Proof.
    intros image s token Htoken Hissue Hwait.
    Transparent advance_retirement.
    unfold advance_retirement. cbn [pending_token]. now rewrite Hissue, Hwait.
  Qed.

  Theorem no_completion_preserves_architectural_cursor : forall image s,
      alu_completes (environment_state_image image (physical_state s)) = false ->
      architectural_cursor (advance_retirement image s) = architectural_cursor s.
  Proof.
    intros image s H. unfold advance_retirement. cbn [architectural_cursor].
    now rewrite H.
  Qed.
End CV32E40PAddiReachability.
