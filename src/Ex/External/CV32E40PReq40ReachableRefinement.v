(** Req40: non-circular reachable-state ADDI refinement.

    The reachability record mentions only real pipeline labels, wiring roots,
    local update-chain values and the OBI data-request endpoint.  Generic
    ExtendedSV projection theorems derive the architectural post-state from
    those obligations. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV.
Require Import Ex.External.CV32E40PReq39Trace.
Require Import Ex.External.CV32E40PReq40StateRel.
Require Import Ex.External.CV32E40PReq40NextCommit.
Require Import Ex.External.CV32E40PReq40RootProjection.
Require Import Ex.External.BzeenoBaselineDataOps.
Require Import Ex.RvCore.FormalSpec.

Import ExtendedSV CV32E40PReq39Trace CV32E40PReq40StateRel.
Import CV32E40PReq40NextCommit CV32E40PReq40RootProjection.
Import BzeenoBaselineDataOps.
Local Open Scope Z_scope.

Module CV32E40PReq40ReachableRefinement.

  Definition rf_value_from_root (root_value r : Z) : Z :=
    if (0 <=? r) && (r <? 32)
    then norm 32
      (Z.shiftr root_value (Z.of_nat (32 * Z.to_nat r)))
    else 0.

  Lemma rf_value_from_root_congr : forall left right r,
      left = right ->
      rf_value_from_root left r = rf_value_from_root right r.
  Proof. intros left right r ->. reflexivity. Qed.

  Definition local_rf_after_cycle (w : CommitWindow) (r : Z) : Z :=
    rf_value_from_root
      (shared_context_root_value rf_root
        (build_shared_cycle_context (window_image w) (window_rf_state w))) r.

  (** No field below states an equality about
      [window_pre_projection (advance_window w)]. *)
  Record ADDIReachableCommitInvariant
      (w : CommitWindow) (rd rs1 imm : Z) : Prop := {
    reachable_addi_label : ADDICommitLabel w rd rs1 imm;
    reachable_pc_update_chain :
      shared_context_root_value stateful_pc_root
        (build_shared_cycle_context (window_image w) (window_cursor w)) =
          window_pre_next_pc w;
    reachable_rf_update_chain : forall r, legal_reg r ->
      local_rf_after_cycle w r = addi_expected_post_rf w rd rs1 imm r;
    reachable_no_data_request :
      capture_data_request
        (environment_state_image (window_image w) (window_rf_state w)) = None
  }.

  Lemma window_cursor_advance : forall w,
      window_cursor (advance_window w) = window_rf_state w.
  Proof. reflexivity. Qed.

  Lemma window_image_advance : forall w,
      window_image (advance_window w) = window_image w.
  Proof. reflexivity. Qed.

  Lemma window_rf_state_advance : forall w,
      window_rf_state (advance_window w) =
        full_cycle_image (window_image w) (window_rf_state w).
  Proof. reflexivity. Qed.

  Lemma full_cycle_memory_no_request : forall image s,
      capture_data_request (environment_state_image image s) = None ->
      trace_memory_word (full_cycle_image image s) = trace_memory_word s.
  Proof.
    intros image s Hnone.
    unfold full_cycle_image. cbn [trace_memory_word].
    now rewrite Hnone.
  Qed.

  Lemma legal_reg_bounds_test : forall r,
      legal_reg r -> (0 <=? r) && (r <? 32) = true.
  Proof.
    intros r Hr. unfold legal_reg in Hr.
    apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
  Qed.

  Lemma rf_register_as_root_value : forall s r,
      legal_reg r ->
      rf_register s (Z.to_nat r) =
        rf_value_from_root (read_signal s rf_root) r.
  Proof.
    intros s r Hr.
    unfold rf_register, rf_value_from_root, rf_root.
    rewrite legal_reg_bounds_test by exact Hr.
    reflexivity.
  Qed.

  (** The architectural RF view at a commit window is not an independently
      materialised post-state.  It is exactly the RF-root projection of the
      one physical cycle starting at that window's cursor. *)
  Lemma window_pre_rf_from_cursor_root : forall w r,
      legal_reg r ->
      window_pre_rf w r =
        rf_value_from_root
          (shared_context_root_value rf_root
            (build_shared_cycle_context (window_image w)
              (window_cursor w))) r.
  Proof.
    intros w r Hr.
    unfold window_pre_rf, window_rf_state.
    rewrite legal_reg_bounds_test by exact Hr.
    rewrite rf_register_as_root_value by exact Hr.
    rewrite built_shared_context_root_projection by exact rf_comb_unwritten.
    reflexivity.
  Qed.

  Theorem reachable_invariant_implies_addi_effect :
      forall w rd rs1 imm,
      ADDIReachableCommitInvariant w rd rs1 imm ->
      ADDIArchitecturalEffect w (advance_window w) rd rs1 imm.
  Proof.
    intros w rd rs1 imm Hreachable.
    destruct Hreachable as
      [Hlabel Hpc_chain Hrf_chain Hno_data].
    assert (Hpc_effect :
      window_pre_pc (advance_window w) = window_pre_next_pc w).
    { unfold window_pre_pc.
      rewrite window_cursor_advance.
      unfold window_rf_state.
      rewrite built_shared_context_root_projection
        by exact stateful_pc_comb_unwritten.
      exact Hpc_chain. }
    constructor.
    - unfold addi_expected_post_pc. exact Hpc_effect.
    - unfold addi_expected_post_next_pc, window_pre_next_pc.
      now rewrite Hpc_effect.
    - intros r Hr.
      unfold window_pre_rf.
      rewrite legal_reg_bounds_test by exact Hr.
      rewrite window_rf_state_advance.
      rewrite rf_register_as_root_value by exact Hr.
      rewrite built_shared_context_root_projection by exact rf_comb_unwritten.
      exact (Hrf_chain r Hr).
    - reflexivity.
    - unfold window_pre_dmem.
      rewrite window_rf_state_advance.
      apply word_formal_dmem_congr.
      now apply full_cycle_memory_no_request.
  Qed.

  Theorem cv32e40p_reachable_addi_next_commit_preserves_StateRel :
      forall w isa rd rs1 imm,
        legal_reg rd -> legal_reg rs1 -> legal_addi_imm imm ->
        ADDIAtPC isa rd rs1 imm ->
        CV32StateRel w isa ->
        ADDIReachableCommitInvariant w rd rs1 imm ->
        exists isa',
          FormalSpec.run1 isa = (Some tt, isa') /\
          CV32StateRel (advance_window w) isa'.
  Proof.
    intros w isa rd rs1 imm Hrd Hrs Himm Hfetch Hrel Hreachable.
    exact (cv32e40p_addi_effect_preserves_StateRel
      w (advance_window w) isa rd rs1 imm
      Hrd Hrs Himm Hfetch Hrel
      (advance_window_is_real_execution w)
      (reachable_invariant_implies_addi_effect w rd rs1 imm Hreachable)).
  Qed.

  Definition option_is_noneb {A : Type} (value : option A) : bool :=
    match value with
    | None => true
    | Some _ => false
    end.

  Lemma option_is_noneb_sound : forall A (value : option A),
      option_is_noneb value = true -> value = None.
  Proof. intros A [value|] H; [discriminate|reflexivity]. Qed.

  (** The scheduler binds every driven LFP, item update list and post LFP
      exactly once.  The first successor becomes the second phase input with
      no reset and no fixture reconstruction. *)
  Definition addi_reachable_shared_context_checkb
      (w : CommitWindow) (rd rs1 imm : Z) : bool :=
    let image := window_image w in
    let cursor := window_cursor w in
    let first_context := build_shared_cycle_context image cursor in
    let first_successor :=
      successor_from_shared_context image cursor first_context in
    let second_context :=
      build_shared_cycle_context image first_successor in
    let pc_chain := shared_context_root_value stateful_pc_root first_context in
    let rf_chain := shared_context_root_value rf_root second_context in
    let actual_rf := fun r => rf_value_from_root rf_chain r in
    andb (Z.eqb (nthz (window_issue w) 1) 1)
    (andb (Z.eqb (nthz (window_issue w) 2)
                   (enc_i (Decode.Addi rd rs1 imm)))
    (andb (Z.eqb pc_chain (window_pre_next_pc w))
    (andb (rf_projection_checkb actual_rf
             (addi_expected_post_rf w rd rs1 imm))
      (option_is_noneb
        (capture_data_request
          (shared_environment second_context)))))).

  #[local] Opaque full_cycle_root_value full_cycle_image
    environment_state_image
    build_shared_cycle_context successor_from_shared_context
    shared_context_root_value.

  Theorem addi_reachable_shared_context_checkb_sound : forall w rd rs1 imm,
      addi_reachable_shared_context_checkb w rd rs1 imm = true ->
      ADDIReachableCommitInvariant w rd rs1 imm.
  Proof.
    intros w rd rs1 imm Hcheck.
    unfold addi_reachable_shared_context_checkb in Hcheck.
    apply andb_true_iff in Hcheck as [Hvalid Hcheck].
    apply andb_true_iff in Hcheck as [Hinstruction Hcheck].
    apply andb_true_iff in Hcheck as [Hpc_chain Hcheck].
    apply andb_true_iff in Hcheck as [Hrf Hdata].
    apply Z.eqb_eq in Hvalid, Hinstruction, Hpc_chain.
    constructor.
    - constructor; assumption.
    - exact Hpc_chain.
    - intros r Hr.
      pose proof (rf_projection_checkb_sound _ _ Hrf r Hr) as Hfield.
      unfold local_rf_after_cycle, window_rf_state.
      rewrite <- built_shared_context_successor.
      exact Hfield.
    - apply option_is_noneb_sound in Hdata.
      rewrite built_shared_context_environment in Hdata.
      unfold window_rf_state.
      rewrite <- built_shared_context_successor.
      exact Hdata.
  Qed.

End CV32E40PReq40ReachableRefinement.
