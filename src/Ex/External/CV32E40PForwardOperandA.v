(** Source-A-only operand projection for register data operations.
    The older ADDI cone bundled A forwarding with the immediate B choice;
    register-register instructions need the same real A cone without that
    unrelated B-side premise. *)
From Coq Require Import ZArith.
Require Import Lang.ExtendedSV Ex.Generated.CV32E40PExtendedAST
  Ex.External.CV32E40PAddiOperandCone.
Import ExtendedSV CV32E40PExtendedAST CV32E40PAddiOperandCone.
Local Open Scope Z_scope.
Module CV32E40PForwardOperandA.

Definition RegisterAOperandChoice ev pre :=
  norm 3 (read_signal (cut 1628 (round (round6 ev pre))) 781%nat) = 0.

Theorem driven_register_a ev pre : RegisterAOperandChoice ev pre ->
  norm 32
    (read_signal (phase_driven_state cv32e40p_program ev pre) 844%nat) =
  actual_forward_input ev pre.
Proof.
  intros HA. rewrite driven_two_rounds.
  rewrite round_a_value by exact HA.
  apply round_forward_value.
Qed.

Print Assumptions driven_register_a.
End CV32E40PForwardOperandA.
