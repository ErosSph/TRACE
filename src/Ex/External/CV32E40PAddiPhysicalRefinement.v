(** Real first-retirement boundaries + same-state RF/RAM projections.
    This closes the two dependent ADDI regression using the new retirement
    relation. It is deliberately NOT named a theorem for arbitrary programs. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CV32E40PAddiReachability.
Require Import Ex.External.CV32E40PAddiCommitTrace.
Require Import Ex.External.CV32E40PAddiCommitSchedule.
Require Import Ex.External.CV32E40PReq39Trace.
Require Import Ex.External.CV32E40PReq40StateRel.
Require Import Ex.External.CV32E40PReq40NextCommit.
Require Import Ex.External.CV32E40PReq40Windows.
Require Import Ex.External.CV32E40PReq40ConcreteRefinement.
Require Import Ex.RvCore.FormalSpec.
Import CV32E40PAddiReachability CV32E40PAddiCommitTrace CV32E40PAddiCommitSchedule.
Import CV32E40PReq39Trace CV32E40PReq40StateRel CV32E40PReq40NextCommit.
Import CV32E40PReq40Windows CV32E40PReq40ConcreteRefinement.
Local Open Scope Z_scope.

Module CV32E40PAddiPhysicalRefinement.
  #[local] Opaque full_cycle_image environment_state_image.

  Definition boundary_pc (s : RetirementState) :=
    architectural_cursor s.

  (** PC is the retirement monitor's architectural cursor, not the fetch/ID
      PC. It holds during bubbles. No future RF state is used: RF and data
      memory are read from s itself. Instruction-order and hardware redirect
      alignment for arbitrary executions remain separate open obligations. *)
  Definition physical_projection (s : RetirementState) : RTLArchitecturalState :=
    {| rtl_arch_pc := boundary_pc s;
       rtl_arch_next_pc := (boundary_pc s + 4) mod 2^32;
       rtl_arch_rf := fun r => if (0 <=? r) && (r <? 32)
         then rf_register (trace_rtl (physical_state s)) (Z.to_nat r) else 0;
       rtl_arch_imem := image_formal_imem image;
       rtl_arch_dmem := word_formal_dmem (trace_memory_word (physical_state s)) |}.

  Lemma physical_at_cycle : forall k,
      physical_state (cycle k) = cycles_image image k trace0.
  Proof.
    intros. unfold cycle. rewrite monitored_execution_is_original_scheduler.
    reflexivity.
  Qed.
  Lemma physical_first_boundary : physical_state (cycle 5) = window_rf_state first_window.
  Proof. rewrite physical_at_cycle. reflexivity. Qed.
  Lemma physical_second_boundary : physical_state (cycle 6) = window_rf_state second_window.
  Proof. rewrite physical_at_cycle. reflexivity. Qed.
  Lemma physical_final_boundary : physical_state (cycle 7) = window_rf_state final_window.
  Proof. rewrite physical_at_cycle. reflexivity. Qed.

  Definition observed_cursor (o : Observation) :=
    let '(_, _, _, _, _, _, cursor) := o in cursor.
  Lemma cursor_at_cycle : forall k, (k < 9)%nat ->
      architectural_cursor (cycle k) = observed_cursor (nth k expected empty_observation).
  Proof.
    intros k Hk.
    change (observed_cursor (observation (cycle k)) =
      observed_cursor (nth k expected empty_observation)).
    now rewrite observation_at_cycle by exact Hk.
  Qed.

  Theorem physical_initial_related : StateRel (physical_projection (cycle 5)) isa0.
  Proof.
    destruct initial_state_related as (Hpc & Hnext & Hrf & Hrom & Hram).
    unfold StateRel, physical_projection. cbn [rtl_arch_pc rtl_arch_next_pc
      rtl_arch_rf rtl_arch_imem rtl_arch_dmem].
    unfold boundary_pc. rewrite cursor_at_cycle by lia.
    cbn [observed_cursor nth expected token token_pc].
    split; [reflexivity|]. split; [reflexivity|]. split.
    - intros r Hr. rewrite physical_first_boundary. exact (Hrf r Hr).
    - split; [exact Hrom|]. rewrite physical_first_boundary. exact Hram.
  Qed.

  Theorem physical_first_post_related : StateRel (physical_projection (cycle 6)) isa1.
  Proof.
    destruct two_real_commits_refine_two_run1_steps as [_ [Hrel _]].
    destruct Hrel as (Hpc & Hnext & Hrf & Hrom & Hram).
    unfold StateRel, physical_projection. cbn [rtl_arch_pc rtl_arch_next_pc
      rtl_arch_rf rtl_arch_imem rtl_arch_dmem].
    unfold boundary_pc. rewrite cursor_at_cycle by lia.
    cbn [observed_cursor nth expected token token_pc].
    split; [reflexivity|]. split; [reflexivity|]. split.
    - intros r Hr. rewrite physical_second_boundary. exact (Hrf r Hr).
    - split; [exact Hrom|]. rewrite physical_second_boundary. exact Hram.
  Qed.

  Theorem physical_second_post_related : StateRel (physical_projection (cycle 7)) isa2.
  Proof.
    destruct two_real_commits_refine_two_run1_steps as [_ [_ [_ Hrel]]].
    destruct Hrel as (Hpc & Hnext & Hrf & Hrom & Hram).
    unfold StateRel, physical_projection. cbn [rtl_arch_pc rtl_arch_next_pc
      rtl_arch_rf rtl_arch_imem rtl_arch_dmem].
    unfold boundary_pc. rewrite cursor_at_cycle by lia.
    cbn [observed_cursor nth expected token token_pc].
    split; [reflexivity|]. split; [reflexivity|]. split.
    - intros r Hr. rewrite physical_final_boundary. exact (Hrf r Hr).
    - split; [exact Hrom|]. rewrite physical_final_boundary. exact Hram.
  Qed.

  Theorem two_real_retirements_refine_two_run1_steps :
      ResetReachable image (cycle 5) /\
      StateRel (physical_projection (cycle 5)) isa0 /\
      NextRetirement image (cycle 5) 1 (token 0 1048723) (cycle 6) /\
      FormalSpec.run1 isa0 = (Some tt, isa1) /\
      StateRel (physical_projection (cycle 6)) isa1 /\
      NoTokenOverwrite image (cycle 6) /\
      NextRetirement image (cycle 6) 1 (token 4 1081491) (cycle 7) /\
      FormalSpec.run1 isa1 = (Some tt, isa2) /\
      StateRel (physical_projection (cycle 7)) isa2 /\
      NoTokenOverwrite image (cycle 7).
  Proof.
    destruct two_real_commits_refine_two_run1_steps as (Hrun0 & _ & Hrun1 & _).
    split; [apply entire_prefix_is_reset_reachable|].
    split; [exact physical_initial_related|].
    split.
    { apply retire_at_cycle. rewrite retirement_at_cycle by lia. reflexivity. }
    split; [exact Hrun0|].
    split; [exact physical_first_post_related|].
    split; [apply no_token_overwrite_in_checked_prefix; lia|].
    split; [exact second_real_retirement|].
    split; [exact Hrun1|].
    split; [exact physical_second_post_related|].
    apply no_token_overwrite_in_checked_prefix. lia.
  Qed.
End CV32E40PAddiPhysicalRefinement.
