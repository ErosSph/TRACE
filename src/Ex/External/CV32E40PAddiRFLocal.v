(** Symbolic RF process contracts, checked against the actual elaborated AST.
    No expected CPU post-state or reachability certificate is a premise. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV.
Require Import Ex.Generated.CV32E40PExtendedAST.
Import ListNotations ExtendedSV CV32E40PExtendedAST.
Local Open Scope Z_scope.

Module CV32E40PAddiRFLocal.

  Definition rf_lane_lvalue (r : nat) : LValue :=
    LSel 32 (LVar 1024 902%nat) (EConst 10 (32 * Z.of_nat r)).

  Definition rf_lane_process (r : nat) : Process :=
    {| process_kind := Sequential;
       process_events := [{| event_edge := Posedge; event_signal := 884%nat |};
                          {| event_edge := Negedge; event_signal := 885%nat |}];
       process_body := SSeq [SSeq [SIf (EVar 1 885%nat)
         (SSeq [SIf (ESel 1 (EVar 32 907%nat) (EConst 5 (Z.of_nat r)))
           (SAssign true (EVar 32 897%nat) (rf_lane_lvalue r))
           (SIf (ESel 1 (EVar 32 906%nat) (EConst 5 (Z.of_nat r)))
             (SAssign true (EVar 32 894%nat) (rf_lane_lvalue r)) SSkip)])
         (SSeq [SAssign true (EConst 32 0) (rf_lane_lvalue r)])]];
       process_source_line := 129 |}.

  (** Only the lane index is enumerated here: state, old RF bits, write
      enables, and both write-data ports remain universally quantified. *)
  Theorem actual_rf_process_is_template : forall r,
      (1 <= r < 32)%nat ->
      nth (44 + r) (processes cv32e40p_program) process_0 =
        rf_lane_process r.
  Proof.
    intros r Hr.
    do 32 (destruct r as [|r]; [try lia; reflexivity|]). lia.
  Qed.

  Definition lane_enabled (s : State) (port : signal) (r : nat) : Z :=
    norm 1 (Z.shiftr (norm 32 (read_signal s port))
                     (norm 5 (Z.of_nat r))).

  Definition lane_update (r : nat) (value : Z) : Update :=
    {| update_signal := 902%nat;
       update_offset := norm 10 (32 * Z.of_nat r);
       update_width := 32%nat; update_value := norm 32 value |}.

  Definition local_lane_updates (s : State) (r : nat) : list Update :=
    if Z.eqb (norm 1 (read_signal s 885%nat)) 0 then [lane_update r 0]
    else if Z.eqb (lane_enabled s 907%nat r) 0
         then if Z.eqb (lane_enabled s 906%nat r) 0 then []
              else [lane_update r (norm 32 (read_signal s 894%nat))]
         else [lane_update r (norm 32 (read_signal s 897%nat))].

  Lemma template_exec_updates_are_local : forall fuel s r,
      (8 <= fuel)%nat ->
      emitted_updates (exec_stmt fuel (process_body (rf_lane_process r))
        {| blocking_state := s; pending_nba := []; emitted_updates := [] |}) =
        local_lane_updates s r.
  Proof.
    intros fuel s r Hfuel.
    do 8 (destruct fuel as [|fuel]; [lia|]).
    unfold rf_lane_process, local_lane_updates,
      lane_enabled, lane_update, rf_lane_lvalue.
    cbv beta iota zeta delta [statement_fuel process_body exec_stmt fold_left blocking_state
      pending_nba emitted_updates eval_expr resolve_update resolve_lvalue].
    destruct (Z.eqb (norm 1 (read_signal s 885%nat)) 0);
      destruct (Z.eqb (norm 1 (Z.shiftr (norm 32 (read_signal s 907%nat))
        (norm 5 (Z.of_nat r)))) 0);
      destruct (Z.eqb (norm 1 (Z.shiftr (norm 32 (read_signal s 906%nat))
        (norm 5 (Z.of_nat r)))) 0); reflexivity.
  Qed.

  Theorem template_updates_are_local : forall s r,
      process_updates cv32e40p_program s (rf_lane_process r) =
        local_lane_updates s r.
  Proof.
    intros s r. apply template_exec_updates_are_local. cbn. lia.
  Qed.

  Theorem actual_rf_updates_are_local : forall s r,
      (1 <= r < 32)%nat ->
      process_updates cv32e40p_program s
        (nth (44 + r) (processes cv32e40p_program) process_0) =
        local_lane_updates s r.
  Proof.
    intros s r Hr. rewrite actual_rf_process_is_template by exact Hr.
    apply template_updates_are_local.
  Qed.

  Theorem actual_rf_port_b_priority : forall s r,
      (1 <= r < 32)%nat -> norm 1 (read_signal s 885%nat) <> 0 ->
      lane_enabled s 907%nat r <> 0 ->
      process_updates cv32e40p_program s
        (nth (44 + r) (processes cv32e40p_program) process_0) =
        [lane_update r (norm 32 (read_signal s 897%nat))].
  Proof.
    intros s r Hr Hreset Hb. rewrite actual_rf_updates_are_local by exact Hr.
    unfold local_lane_updates. apply Z.eqb_neq in Hreset, Hb.
    now rewrite Hreset, Hb.
  Qed.

  Theorem actual_rf_lane_stalls : forall s r,
      (1 <= r < 32)%nat -> norm 1 (read_signal s 885%nat) <> 0 ->
      lane_enabled s 907%nat r = 0 -> lane_enabled s 906%nat r = 0 ->
      process_updates cv32e40p_program s
        (nth (44 + r) (processes cv32e40p_program) process_0) = [].
  Proof.
    intros s r Hr Hreset Hb Ha.
    rewrite actual_rf_updates_are_local by exact Hr.
    unfold local_lane_updates. apply Z.eqb_neq in Hreset.
    now rewrite Hreset, Hb, Ha.
  Qed.

  Theorem actual_rf_lane_resets : forall s r,
      (1 <= r < 32)%nat -> norm 1 (read_signal s 885%nat) = 0 ->
      process_updates cv32e40p_program s
        (nth (44 + r) (processes cv32e40p_program) process_0) =
        [lane_update r 0].
  Proof.
    intros s r Hr Hreset. rewrite actual_rf_updates_are_local by exact Hr.
    unfold local_lane_updates. now rewrite Hreset.
  Qed.

  Theorem actual_x0_always_writes_zero : forall s,
      process_updates cv32e40p_program s process_44 = [lane_update 0 0].
  Proof.
    intros s. unfold process_updates.
    assert (Hfuel : (5 <= statement_fuel cv32e40p_program)%nat) by (cbn; lia).
    generalize dependent (statement_fuel cv32e40p_program).
    intros fuel Hfuel. do 5 (destruct fuel as [|fuel]; [lia|]).
    unfold process_44, lane_update.
    cbv beta iota zeta delta [statement_fuel process_body exec_stmt fold_left blocking_state
      pending_nba emitted_updates eval_expr resolve_update resolve_lvalue].
    destruct (Z.eqb (norm 1 (read_signal s 885%nat)) 0); reflexivity.
  Qed.
End CV32E40PAddiRFLocal.
