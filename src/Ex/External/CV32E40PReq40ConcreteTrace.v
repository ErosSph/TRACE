(** Kernel-evaluated, no-reset two-commit witness for Req40.

    This file is intentionally the expensive proof firewall.  Both Boolean
    facts reduce the real 1,800-signal CV32E40P scheduler.  Downstream ISA
    proofs import the resulting opaque constants and never repeat the CPU
    reduction. *)
From Coq Require Import ZArith List.
Require Import Ex.External.CV32E40PReq39Trace.
Require Import Ex.External.CV32E40PReq40NextCommit.
Require Import Ex.External.CV32E40PReq40Windows.

Import ListNotations.
Import CV32E40PReq39Trace CV32E40PReq40NextCommit.
Import CV32E40PReq40Windows.
Local Open Scope Z_scope.

Module CV32E40PReq40ConcreteTrace.

  (** The shared evaluator binds each physical successor once.  It is
      propositionally identical to [addi_window_checkb], but avoids repeated
      materialisation of the same full state. *)
  Theorem first_real_addi_checker_shared :
      addi_window_checkb_shared first_window 1 0 1 = true.
  Proof. vm_compute. reflexivity. Qed.

  Theorem second_real_addi_checker_shared :
      addi_window_checkb_shared second_window 1 1 1 = true.
  Proof. vm_compute. reflexivity. Qed.

  Corollary first_real_addi_checker :
      CV32ADDICheckedNextCommit first_window 1 0 1.
  Proof.
    unfold CV32ADDICheckedNextCommit.
    rewrite <- addi_window_checkb_shared_equiv.
    exact first_real_addi_checker_shared.
  Qed.

  Corollary second_real_addi_checker :
      CV32ADDICheckedNextCommit second_window 1 1 1.
  Proof.
    unfold CV32ADDICheckedNextCommit.
    rewrite <- addi_window_checkb_shared_equiv.
    exact second_real_addi_checker_shared.
  Qed.

End CV32E40PReq40ConcreteTrace.
