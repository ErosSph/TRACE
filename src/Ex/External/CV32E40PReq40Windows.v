(** Req40 persistent two-commit fixture without proof payloads.

    Keeping the sliding windows in a small compilation unit lets each
    projection certificate import the real trace definition without also
    loading another large computed proof. *)
From Coq Require Import ZArith List.
Require Import Ex.External.CV32E40PReq39Trace.
Require Import Ex.External.CV32E40PReq40NextCommit.

Import ListNotations.
Import CV32E40PReq39Trace CV32E40PReq40NextCommit.
Local Open Scope Z_scope.

Module CV32E40PReq40Windows.

  Definition second_addi : Z := 1081491. (* addi x1,x1,1 *)
  Definition two_addi_image : InstructionImage :=
    [addi_x1_x0_1; second_addi].

  (** Reset occurs only in [trace0].  Every state below is obtained by
      applying the persistent-image scheduler to its predecessor. *)
  Definition first_cursor : TraceState :=
    cycles_image two_addi_image 4 trace0.

  Definition first_window : CommitWindow :=
    {| window_image := two_addi_image;
       window_cursor := first_cursor |}.

  Definition second_window : CommitWindow := advance_window first_window.
  Definition final_window : CommitWindow := advance_window second_window.

  Theorem second_window_is_first_real_post :
      second_window = advance_window first_window.
  Proof. reflexivity. Qed.

  Theorem final_window_is_second_real_post :
      final_window = advance_window second_window.
  Proof. reflexivity. Qed.

End CV32E40PReq40Windows.
