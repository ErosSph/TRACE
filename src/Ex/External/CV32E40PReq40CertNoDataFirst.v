(** Kernel-computed first-commit OBI no-data-request certificate. *)
From Coq Require Import ZArith List Bool.
Require Import Ex.External.CV32E40PReq39Trace.
Require Import Ex.External.CV32E40PReq40NextCommit.
Require Import Ex.External.CV32E40PReq40Windows.
Import CV32E40PReq39Trace CV32E40PReq40NextCommit.
Import CV32E40PReq40Windows.
Local Open Scope Z_scope.
Module CV32E40PReq40CertNoDataFirst.
  Transparent full_cycle_image environment_state_image window_rf_state
    advance_window.
  Theorem first_no_data_request :
      capture_data_request
        (environment_state_image (window_image first_window)
          (window_rf_state first_window)) = None.
  Proof. vm_compute. reflexivity. Qed.
End CV32E40PReq40CertNoDataFirst.
