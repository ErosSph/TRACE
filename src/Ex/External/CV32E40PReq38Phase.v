(** Kernel-checked runtime acceptance for the pinned CV32E40P configuration. *)
From Coq Require Import ZArith List.
Require Import Lang.ExtendedSV.
Require Import Ex.Generated.CV32E40PExtendedAST.
Import ListNotations.
Import ExtendedSV CV32E40PExtendedAST.

Module CV32E40PReq38Phase.

  Definition initialized_zero : State :=
    initialize cv32e40p_program (List.repeat 0%Z 1800).

  (** IDs 7 and 8 are generated from the top-level provenance table, where
      they denote [clk_i] and active-low [rst_ni].  No semantic function
      contains these constants or CV32E40P names. *)
  Definition pre_reset : State :=
    lfp_candidate cv32e40p_program (write_signal initialized_zero 8 1).

  Definition reset_fall : Event :=
    {| changed_signal := 8; old_value := 1; new_value := 0 |}.

  Definition reset_driven : State :=
    phase_driven_state cv32e40p_program reset_fall pre_reset.

  Definition reset_processes : list Process :=
    selected_on_transition cv32e40p_program pre_reset reset_driven.

  Definition reset_updates : list Update :=
    flat_map
      (process_updates cv32e40p_program
        (phase_driven_state cv32e40p_program reset_fall pre_reset))
      (selected_on_transition cv32e40p_program pre_reset
        (phase_driven_state cv32e40p_program reset_fall pre_reset)).

  (** Materialise the finite event cone once.  Without this proof firewall,
      each pairwise compatibility query re-evaluates the complete CPU cone. *)
  Definition reset_updates_compact : list Update :=
    Eval vm_compute in reset_updates.

  Theorem reset_updates_materialized :
    flat_map
      (process_updates cv32e40p_program
        (phase_driven_state cv32e40p_program reset_fall pre_reset))
      (selected_on_transition cv32e40p_program pre_reset
        (phase_driven_state cv32e40p_program reset_fall pre_reset)) =
    reset_updates_compact.
  Proof. vm_compute. reflexivity. Qed.

  Definition reset_grouped_compatibility : bool :=
    Eval vm_compute in grouped_updates_commuteb reset_updates_compact.

  Example reset_grouped_compatibility_checked :
    reset_grouped_compatibility = true.
  Proof. reflexivity. Qed.

  (** Keep the unreduced checker expression in the theorem type.  This is a
      proof-engineering boundary: consumers can reuse the VM certificate
      without asking conversion to unfold the 175-update event cone again. *)
  Theorem reset_grouped_certificate :
    grouped_updates_commuteb reset_updates_compact = true.
  Proof. vm_compute. reflexivity. Qed.

  Example reset_selects_all_async_processes :
    List.length reset_processes = 60%nat.
  Proof. vm_compute. reflexivity. Qed.

  Example reset_runtime_update_count :
    List.length reset_updates_compact = 175%nat.
  Proof. vm_compute. reflexivity. Qed.

  Theorem reset_updates_are_pairwise_commuting :
    GroupedPhaseUpdatesCommuteAt cv32e40p_program reset_fall pre_reset.
  Proof.
    eapply grouped_phase_updates_from_materialized_certificate
      with (certificate := reset_updates_compact).
    - exact reset_updates_materialized.
    - exact reset_grouped_certificate.
  Qed.

  Theorem reset_phase_schedule_independent :
    PhaseIndependentAt cv32e40p_program reset_fall pre_reset.
  Proof.
    apply grouped_phase_updates_commute_implies_independent.
    exact reset_updates_are_pairwise_commuting.
  Qed.

  Theorem reset_phase_extended_standard_equiv : forall post,
    post = PhaseSemantics cv32e40p_program reset_fall pre_reset <->
    StandardSVPhaseExecution cv32e40p_program reset_fall pre_reset post.
  Proof.
    apply extended_standard_phase_equiv_at.
    exact reset_phase_schedule_independent.
  Qed.

  Theorem reset_phase_standard_confluent : forall post1 post2,
    StandardSVPhaseExecution cv32e40p_program reset_fall pre_reset post1 ->
    StandardSVPhaseExecution cv32e40p_program reset_fall pre_reset post2 ->
    post1 = post2.
  Proof.
    apply extended_standard_phase_confluence_at.
    exact reset_phase_schedule_independent.
  Qed.

  Definition post_reset : State :=
    PhaseSemantics cv32e40p_program reset_fall pre_reset.

  Theorem pre_reset_comb_lfp_checked :
    lfp_checked cv32e40p_program (write_signal initialized_zero 8 1) = true.
  Proof. vm_compute. reflexivity. Qed.

  Theorem post_reset_comb_lfp_checked :
    lfp_checked cv32e40p_program
      (execute_process_order cv32e40p_program reset_driven reset_processes) = true.
  Proof. vm_compute. reflexivity. Qed.

  Theorem cv32e40p_mtrs_is_real_phase_scheduler :
    mtrs_event_transition cv32e40p_mtrs reset_fall pre_reset =
    PhaseSemantics cv32e40p_program reset_fall pre_reset.
  Proof. reflexivity. Qed.

End CV32E40PReq38Phase.
