(** Posedge acceptance after a real asynchronous-reset/release prefix. *)
From Coq Require Import ZArith List.
Require Import Lang.ExtendedSV.
Require Import Ex.Generated.CV32E40PExtendedAST.
Require Import Ex.External.CV32E40PReq38Phase.
Import ListNotations.
Import ExtendedSV CV32E40PExtendedAST.
Import CV32E40PReq38Phase.

Module CV32E40PReq38Clock.

  Definition reset_release : Event :=
    {| changed_signal := 8; old_value := 0; new_value := 1 |}.

  Definition released : State :=
    PhaseSemantics cv32e40p_program reset_release post_reset.

  Definition clock_rise : Event :=
    {| changed_signal := 7; old_value := 0; new_value := 1 |}.

  Definition clock_driven : State :=
    phase_driven_state cv32e40p_program clock_rise released.

  Definition clock_processes : list Process :=
    selected_on_transition cv32e40p_program released clock_driven.

  Definition clock_updates : list Update :=
    flat_map (process_updates cv32e40p_program clock_driven) clock_processes.

  Definition clock_updates_compact : list Update :=
    Eval vm_compute in clock_updates.

  Theorem release_selects_no_edge_process :
    List.length
      (selected_on_transition cv32e40p_program post_reset
        (phase_driven_state cv32e40p_program reset_release post_reset)) = 0%nat.
  Proof. vm_compute. reflexivity. Qed.

  Theorem release_comb_lfp_checked :
    lfp_checked cv32e40p_program (write_signal post_reset 8 1) = true.
  Proof. vm_compute. reflexivity. Qed.

  Theorem clock_selects_two_enabled_processes :
    List.length clock_processes = 2%nat.
  Proof. vm_compute. reflexivity. Qed.

  Theorem clock_runtime_update_count :
    List.length clock_updates_compact = 3%nat.
  Proof. vm_compute. reflexivity. Qed.

  Theorem clock_updates_materialized :
    flat_map
      (process_updates cv32e40p_program
        (phase_driven_state cv32e40p_program clock_rise released))
      (selected_on_transition cv32e40p_program released
        (phase_driven_state cv32e40p_program clock_rise released)) =
    clock_updates_compact.
  Proof. vm_compute. reflexivity. Qed.

  Theorem clock_grouped_certificate :
    grouped_updates_commuteb clock_updates_compact = true.
  Proof. vm_compute. reflexivity. Qed.

  Theorem clock_updates_are_pairwise_commuting :
    GroupedPhaseUpdatesCommuteAt cv32e40p_program clock_rise released.
  Proof.
    eapply grouped_phase_updates_from_materialized_certificate
      with (certificate := clock_updates_compact).
    - exact clock_updates_materialized.
    - exact clock_grouped_certificate.
  Qed.

  Theorem clock_phase_schedule_independent :
    PhaseIndependentAt cv32e40p_program clock_rise released.
  Proof.
    apply grouped_phase_updates_commute_implies_independent.
    exact clock_updates_are_pairwise_commuting.
  Qed.

  Theorem clock_phase_extended_standard_equiv : forall post,
    post = PhaseSemantics cv32e40p_program clock_rise released <->
    StandardSVPhaseExecution cv32e40p_program clock_rise released post.
  Proof.
    apply extended_standard_phase_equiv_at.
    exact clock_phase_schedule_independent.
  Qed.

  Theorem clock_phase_standard_confluent : forall post1 post2,
    StandardSVPhaseExecution cv32e40p_program clock_rise released post1 ->
    StandardSVPhaseExecution cv32e40p_program clock_rise released post2 ->
    post1 = post2.
  Proof.
    apply extended_standard_phase_confluence_at.
    exact clock_phase_schedule_independent.
  Qed.

  Theorem clock_post_comb_lfp_checked :
    lfp_checked cv32e40p_program
      (execute_process_order cv32e40p_program clock_driven clock_processes) = true.
  Proof. vm_compute. reflexivity. Qed.

  Theorem cv32e40p_clock_mtrs_uses_phase_scheduler :
    mtrs_event_transition cv32e40p_mtrs clock_rise released =
    PhaseSemantics cv32e40p_program clock_rise released.
  Proof. reflexivity. Qed.

End CV32E40PReq38Clock.
