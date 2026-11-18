(** Kernel-computed RF root before the first commit. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSVRootProjection.
Require Import Ex.External.CV32E40PReq39Trace.
Require Import Ex.External.CV32E40PReq40NextCommit.
Require Import Ex.External.CV32E40PReq40RootProjection.
Require Import Ex.External.CV32E40PReq40Windows.
Import CV32E40PReq39Trace CV32E40PReq40NextCommit.
Import CV32E40PReq40RootProjection CV32E40PReq40Windows.
Import ExtendedSVRootProjection.
Local Open Scope Z_scope.
Module CV32E40PReq40CertRFPre.
  Transparent full_cycle_image environment_state_image window_rf_state
    advance_window build_shared_cycle_context successor_from_shared_context
    shared_context_root_value build_phase_execution_context
    phase_execution_root_value.
  Theorem first_rf_pre_chain_scalar :
      shared_context_root_value rf_root
        (build_shared_cycle_context (window_image first_window)
          (window_cursor first_window)) = 0.
  Proof. vm_compute. reflexivity. Qed.
End CV32E40PReq40CertRFPre.
