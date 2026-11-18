(** Actual ID/EX process stall contract. No expected post-state is assumed.
    Source: cv32e40p_id_stage.sv:1426-1631. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice.
Require Import Ex.Generated.CV32E40PExtendedAST.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice CV32E40PExtendedAST.
Local Open Scope Z_scope.
Module CV32E40PAddiIDEXHold.
  Definition stalled_inputs (s : State) : Prop :=
    norm 1 (read_signal s 561%nat) = 1 /\
    norm 1 (read_signal s 662%nat) = 0 /\
    norm 1 (read_signal s 696%nat) = 0 /\
    norm 1 (read_signal s 586%nat) = 0 /\
    norm 1 (read_signal s 584%nat) = 0 /\
    norm 1 (read_signal s 637%nat) = 0.

  Lemma stalled_exec_has_no_updates : forall fuel s,
      (10 <= fuel)%nat -> stalled_inputs s ->
      emitted_updates (exec_stmt fuel (process_body process_23)
        {| blocking_state := s; pending_nba := []; emitted_updates := [] |}) = [].
  Proof.
    intros fuel s Hfuel (Hr & Hmis & Hmult & Hid & Hex & Hcsr).
    do 10 (destruct fuel as [|fuel]; [lia|]).
    unfold process_23.
    cbv beta iota zeta delta [process_body exec_stmt fold_left blocking_state
      pending_nba emitted_updates eval_expr].
    rewrite Hr. cbn [Z.eqb].
    rewrite Hmis. cbn [Z.eqb].
    rewrite Hmult. cbn [Z.eqb].
    rewrite Hid. cbn [Z.eqb].
    rewrite Hex. cbn [Z.eqb].
    rewrite Hcsr. reflexivity.
  Qed.

  Theorem actual_stalled_idex_has_no_updates : forall s,
      stalled_inputs s -> process_updates cv32e40p_program s process_23 = [].
  Proof.
    intros s H. apply stalled_exec_has_no_updates; [cbn; lia|exact H].
  Qed.

  Definition idex_roots : list signal := [589%nat;590%nat;598%nat;599%nat;600%nat;601%nat].
  Theorem idex_unique_writers : forall root, In root idex_roots ->
      filter (writes_rootb root) (processes cv32e40p_program) = [process_23].
  Proof.
    intros root H. cbn [idex_roots In] in H.
    repeat destruct H as [H|H]; try contradiction; subst root; vm_compute; reflexivity.
  Qed.
  Theorem idex_comb_unwritten : forall root, In root idex_roots ->
      comb_root_unwrittenb cv32e40p_program root = true.
  Proof.
    intros root H. cbn [idex_roots In] in H.
    repeat destruct H as [H|H]; try contradiction; subst root; vm_compute; reflexivity.
  Qed.

  Theorem fullcore_stalled_idex_preserved : forall ev pre root,
      In root idex_roots -> changed_signal ev <> root ->
      stalled_inputs (phase_driven_state cv32e40p_program ev pre) ->
      read_signal (PhaseSemantics cv32e40p_program ev pre) root = read_signal pre root.
  Proof.
    intros ev pre root Hroot Hev Hstall.
    rewrite phase_root_projection by (auto using idex_comb_unwritten).
    unfold phase_update_chain, selected_on_transition.
    rewrite process_slice_sound, filter_swap, idex_unique_writers by exact Hroot.
    cbn [filter].
    destruct (process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_23).
    - cbn [flat_map]. rewrite actual_stalled_idex_has_no_updates by exact Hstall.
      reflexivity.
    - reflexivity.
  Qed.
  Print Assumptions fullcore_stalled_idex_preserved.

  (** In the id_valid=0, ex_ready=1 branch the RTL clears controls but
      preserves operands/destination. id_valid=0 is a latch condition, NOT
      equivalent to the retirement monitor having no instruction to issue. *)
  Definition operand_roots : list signal := [589%nat;590%nat;598%nat].
  Definition normal_no_issue (s : State) : Prop :=
    norm 1 (read_signal s 561%nat) = 1 /\
    norm 1 (read_signal s 662%nat) = 0 /\
    norm 1 (read_signal s 696%nat) = 0 /\
    norm 1 (read_signal s 586%nat) = 0.

  Lemma no_issue_operand_exec : forall fuel s root value,
      (12 <= fuel)%nat -> normal_no_issue s -> In root operand_roots ->
      apply_updates_root_value root value
        (emitted_updates (exec_stmt fuel (process_body process_23)
          {| blocking_state := s; pending_nba := []; emitted_updates := [] |})) = value.
  Proof.
    intros fuel s root value Hfuel (Hr & Hmis & Hmult & Hid) Hroot.
    do 10 (destruct fuel as [|fuel]; [lia|]).
    unfold process_23.
    cbv beta iota zeta delta [process_body exec_stmt fold_left blocking_state
      pending_nba emitted_updates eval_expr].
    rewrite Hr. cbn [Z.eqb].
    rewrite Hmis. cbn [Z.eqb].
    rewrite Hmult. cbn [Z.eqb].
    rewrite Hid. cbn [Z.eqb].
    destruct (Z.eqb (norm 1 (read_signal s 584%nat)) 0);
      destruct (Z.eqb (norm 1 (read_signal s 637%nat)) 0);
      do 2 (destruct fuel as [|fuel]; [lia|]);
      cbn [operand_roots In] in Hroot;
      repeat destruct Hroot as [Hroot|Hroot]; try contradiction; subst root;
      reflexivity.
  Qed.

  Theorem fullcore_no_issue_preserves_operands : forall ev pre root,
      In root operand_roots -> changed_signal ev <> root ->
      normal_no_issue (phase_driven_state cv32e40p_program ev pre) ->
      read_signal (PhaseSemantics cv32e40p_program ev pre) root = read_signal pre root.
  Proof.
    intros ev pre root Hroot Hev Hnone.
    assert (Hidex : In root idex_roots).
    { cbn [operand_roots In] in Hroot. cbn [idex_roots In]. tauto. }
    rewrite phase_root_projection by (auto using idex_comb_unwritten).
    unfold phase_update_chain, selected_on_transition.
    rewrite process_slice_sound, filter_swap, idex_unique_writers by exact Hidex.
    cbn [filter].
    destruct (process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_23).
    - cbn [flat_map]. rewrite app_nil_r. apply no_issue_operand_exec;
        [cbn; lia|exact Hnone|exact Hroot].
    - reflexivity.
  Qed.
  Print Assumptions fullcore_no_issue_preserves_operands.
End CV32E40PAddiIDEXHold.
