(** Req40: two adjacent, non-reset ADDI reachable-state certificates.

    Expensive RTL evaluation is sealed in projection-specific compilation
    units.  This file only composes their PC/RF/OBI facts with the generic
    root-projection soundness theorem; it never materialises a full post
    state and never re-runs the CPU. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CV32E40PReq40ReachableRefinement.
Require Import Ex.External.CV32E40PReq40NextCommit.
Require Import Ex.External.CV32E40PReq40RootProjection.
Require Import Ex.External.BzeenoBaselineDataOps.
Require Import Ex.External.CV32E40PReq40ConcreteTrace.
Require Import Ex.External.CV32E40PReq40StateRel.
Require Import Ex.External.CV32E40PReq40Windows.
Require Import Ex.External.CV32E40PReq40CertBoundaryFirst.
Require Import Ex.External.CV32E40PReq40CertBoundarySecond.
Require Import Ex.External.CV32E40PReq40CertPCFirst.
Require Import Ex.External.CV32E40PReq40CertPCSecond.
Require Import Ex.External.CV32E40PReq40CertRFPre.
Require Import Ex.External.CV32E40PReq40CertRFFirst.
Require Import Ex.External.CV32E40PReq40CertRFSecond.
Require Import Ex.External.CV32E40PReq40CertNoDataFirst.
Require Import Ex.External.CV32E40PReq40CertNoDataSecond.

Import CV32E40PReq40ReachableRefinement CV32E40PReq40Windows.
Import CV32E40PReq40CertBoundaryFirst CV32E40PReq40CertBoundarySecond.
Import CV32E40PReq40CertPCFirst CV32E40PReq40CertPCSecond.
Import CV32E40PReq40CertRFPre CV32E40PReq40CertRFFirst.
Import CV32E40PReq40CertRFSecond.
Import CV32E40PReq40CertNoDataFirst CV32E40PReq40CertNoDataSecond.
Import CV32E40PReq40NextCommit CV32E40PReq40RootProjection.
Import BzeenoBaselineDataOps CV32E40PReq40ConcreteTrace.
Import CV32E40PReq40StateRel.
Local Open Scope Z_scope.

Module CV32E40PReq40ReachableTrace.

  Lemma packed_one_shiftr_ge_two : forall n,
      Z.shiftr 4294967296 (Z.of_nat (32 * S (S n))) = 0.
  Proof.
    intros n. apply Z.shiftr_eq_0; [lia|].
    change (32 < Z.of_nat (32 * S (S n))).
    rewrite Nat2Z.inj_mul. cbn. lia.
  Qed.

  Lemma packed_two_shiftr_ge_two : forall n,
      Z.shiftr 8589934592 (Z.of_nat (32 * S (S n))) = 0.
  Proof.
    intros n. apply Z.shiftr_eq_0; [lia|].
    change (33 < Z.of_nat (32 * S (S n))).
    rewrite Nat2Z.inj_mul. cbn. lia.
  Qed.

  (** The old executable checker is used only for the issue label.  None of
      its post/effect fields participates in the new reachable invariant. *)
  Lemma first_commit_label : ADDICommitLabel first_window 1 0 1.
  Proof.
    destruct (checked_addi_next_commit_certificate first_window 1 0 1
      first_real_addi_checker) as [post Hexec Hlabel Heffect].
    exact Hlabel.
  Qed.

  Lemma second_commit_label : ADDICommitLabel second_window 1 1 1.
  Proof.
    destruct (checked_addi_next_commit_certificate second_window 1 1 1
      second_real_addi_checker) as [post Hexec Hlabel Heffect].
    exact Hlabel.
  Qed.

  Lemma second_rf_pre_chain_scalar :
      shared_context_root_value rf_root
        (build_shared_cycle_context (window_image second_window)
          (window_cursor second_window)) = 4294967296.
  Proof.
    unfold second_window.
    rewrite window_cursor_advance, window_image_advance.
    exact first_rf_chain_scalar.
  Qed.

  Lemma first_pre_rf_scalar : forall r,
      legal_reg r ->
      window_pre_rf first_window r = rf_value_from_root 0 r.
  Proof.
    intros r Hr.
    transitivity (rf_value_from_root
      (shared_context_root_value rf_root
        (build_shared_cycle_context (window_image first_window)
          (window_cursor first_window))) r).
    - exact (window_pre_rf_from_cursor_root first_window r Hr).
    - apply rf_value_from_root_congr. exact first_rf_pre_chain_scalar.
  Qed.

  Lemma second_pre_rf_scalar : forall r,
      legal_reg r ->
      window_pre_rf second_window r = rf_value_from_root 4294967296 r.
  Proof.
    intros r Hr.
    transitivity (rf_value_from_root
      (shared_context_root_value rf_root
        (build_shared_cycle_context (window_image second_window)
          (window_cursor second_window))) r).
    - exact (window_pre_rf_from_cursor_root second_window r Hr).
    - apply rf_value_from_root_congr. exact second_rf_pre_chain_scalar.
  Qed.

  Theorem first_reachable_invariant :
      ADDIReachableCommitInvariant first_window 1 0 1.
  Proof.
    constructor.
    - exact first_commit_label.
    - transitivity 4; [exact first_pc_chain_scalar|].
      symmetry. exact first_pre_next_pc_scalar.
    - intros r Hr.
      unfold local_rf_after_cycle.
      transitivity (rf_value_from_root 4294967296 r).
      + apply rf_value_from_root_congr. exact first_rf_chain_scalar.
      + unfold addi_expected_post_rf.
        destruct (Z.eq_dec 1 0) as [Heq|Hneq]; [lia|].
        rewrite (first_pre_rf_scalar 0) by (unfold legal_reg; lia).
        rewrite (first_pre_rf_scalar r Hr).
        unfold rf_value_from_root.
        repeat rewrite legal_reg_bounds_test by (unfold legal_reg; lia).
        unfold legal_reg in Hr.
        remember (Z.to_nat r) as n eqn:Hnr.
        assert (Hrnat : r = Z.of_nat n).
        { subst n. symmetry. apply Z2Nat.id. lia. }
        rewrite Hrnat.
        assert (Hn : (n < 32)%nat).
        { subst n.
          apply (proj1 (Z2Nat.inj_lt r 32 ltac:(lia) ltac:(lia))). lia. }
        repeat rewrite Nat2Z.id.
        destruct n as [|[|n]].
        * vm_compute. reflexivity.
        * vm_compute. reflexivity.
        * destruct (Z.eq_dec (Z.of_nat (S (S n))) 1) as [Heq|Hneqr];
            [lia|].
          rewrite packed_one_shiftr_ge_two, Z.shiftr_0_l. reflexivity.
    - exact first_no_data_request.
  Qed.

  Theorem second_reachable_invariant :
      ADDIReachableCommitInvariant second_window 1 1 1.
  Proof.
    constructor.
    - exact second_commit_label.
    - transitivity 8; [exact second_pc_chain_scalar|].
      symmetry. exact second_pre_next_pc_scalar.
    - intros r Hr.
      unfold local_rf_after_cycle.
      transitivity (rf_value_from_root 8589934592 r).
      + apply rf_value_from_root_congr. exact second_rf_chain_scalar.
      + unfold addi_expected_post_rf.
        destruct (Z.eq_dec 1 0) as [Heq|Hneq]; [lia|].
        rewrite (second_pre_rf_scalar 1) by (unfold legal_reg; lia).
        rewrite (second_pre_rf_scalar r Hr).
        unfold rf_value_from_root.
        repeat rewrite legal_reg_bounds_test by (unfold legal_reg; lia).
        unfold legal_reg in Hr.
        remember (Z.to_nat r) as n eqn:Hnr.
        assert (Hrnat : r = Z.of_nat n).
        { subst n. symmetry. apply Z2Nat.id. lia. }
        rewrite Hrnat.
        assert (Hn : (n < 32)%nat).
        { subst n.
          apply (proj1 (Z2Nat.inj_lt r 32 ltac:(lia) ltac:(lia))). lia. }
        repeat rewrite Nat2Z.id.
        destruct n as [|[|n]].
        * vm_compute. reflexivity.
        * vm_compute. reflexivity.
        * destruct (Z.eq_dec (Z.of_nat (S (S n))) 1) as [Heq|Hneqr];
            [lia|].
          rewrite packed_two_shiftr_ge_two, packed_one_shiftr_ge_two.
          reflexivity.
    - exact second_no_data_request.
  Qed.

End CV32E40PReq40ReachableTrace.
