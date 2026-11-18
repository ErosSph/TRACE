(** Kernel-computed first issue/architectural-PC boundary certificate. *)
From Coq Require Import ZArith List Bool.
Require Import Ex.External.BzeenoBaselineDataOps.
Require Import Ex.External.CV32E40PReq39Trace.
Require Import Ex.External.CV32E40PReq40NextCommit.
Require Import Ex.External.CV32E40PReq40Windows.
Import BzeenoBaselineDataOps CV32E40PReq39Trace.
Import CV32E40PReq40NextCommit CV32E40PReq40Windows.
Local Open Scope Z_scope.
Module CV32E40PReq40CertBoundaryFirst.
  Transparent full_cycle_image environment_state_image window_rf_state
    advance_window window_pre_pc window_issue.
  Theorem first_pre_next_pc_scalar : window_pre_next_pc first_window = 4.
  Proof. vm_compute. reflexivity. Qed.
End CV32E40PReq40CertBoundaryFirst.
