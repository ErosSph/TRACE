(** Exact EX dependency comparison, including x0 suppression.  These are local
    hardware facts, not an assertion that an arbitrary matching EX value is the
    newest architectural value. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection.
Require Import Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiOperands.
Import ExtendedSV ExtendedSVRootProjection CV32E40PExtendedAST CV32E40PAddiOperands
  CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PAddiHazards.
  Definition hazard_expr := match process_body process_1623 with
    | SAssign false rhs _ => rhs | _ => EConst 1 0 end.
  Lemma ex_match_expression s :
    norm 1 (read_signal (run_process cv32e40p_program s process_1623) 868%nat) =
    norm 1 (eval_expr s hazard_expr).
  Proof.
    change (norm 1 (read_signal (write_signal s 868%nat
      (write_slice (read_signal s 868%nat) 0 1 (norm 1 (eval_expr s hazard_expr)))) 868%nat) =
      norm 1 (eval_expr s hazard_expr)).
    rewrite read_signal_write_same, norm_write_low, norm_twice. reflexivity.
  Qed.
  Theorem ex_never_forwards_x0 s : norm 6 (read_signal s 765%nat) = 0 ->
    norm 1 (read_signal (run_process cv32e40p_program s process_1623) 868%nat) = 0.
  Proof.
    intros H. rewrite ex_match_expression.
    unfold hazard_expr. cbv beta iota zeta delta [process_1623 process_body eval_expr].
    rewrite H. change (norm 6 0) with 0.
    change (norm 1 (boolz (negb (0 =? 0)))) with 0.
    rewrite Z.land_0_r. reflexivity.
  Qed.
  Theorem ex_matching_used_nonzero s :
    norm 6 (read_signal s 692%nat) = norm 6 (read_signal s 765%nat) ->
    norm 6 (read_signal s 765%nat) <> 0 -> norm 1 (read_signal s 728%nat) = 1 ->
    norm 1 (read_signal (run_process cv32e40p_program s process_1623) 868%nat) = 1.
  Proof.
    intros Hmatch Hnonzero Hused. rewrite ex_match_expression.
    unfold hazard_expr. cbv beta iota zeta delta [process_1623 process_body eval_expr].
    rewrite Hmatch, Z.eqb_refl, Hused. change (norm 6 0) with 0.
    assert (Hnz : (0 =? norm 6 (read_signal s 765%nat)) = false).
    { apply Z.eqb_neq. congruence. }
    rewrite Hnz. reflexivity.
  Qed.
  Theorem ex_unused_source_never_forwards s : norm 1 (read_signal s 728%nat) = 0 ->
    norm 1 (read_signal (run_process cv32e40p_program s process_1623) 868%nat) = 0.
  Proof.
    intros H. rewrite ex_match_expression.
    unfold hazard_expr. cbv beta iota zeta delta [process_1623 process_body eval_expr].
    rewrite H, Z.land_0_r. change (norm 1 0) with 0.
    rewrite Z.land_0_l. reflexivity.
  Qed.
  Print Assumptions ex_never_forwards_x0.
  Print Assumptions ex_matching_used_nonzero.
End CV32E40PAddiHazards.
