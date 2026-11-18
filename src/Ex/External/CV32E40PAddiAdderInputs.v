(** Operand preparation in real ALU processes 621--623. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVBlocking
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiOperands
  Ex.External.CV32E40PAddiAdderResult.
Import ExtendedSV ExtendedSVRootProjection ExtendedSVBlocking CV32E40PExtendedAST
  CV32E40PAddiOperands CV32E40PAddiAdderResult
  CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PAddiAdderInputs.
  Lemma assign_value s proc w root e : process_body proc = SAssign false e (LVar w root) ->
    norm w (read_signal (run_process cv32e40p_program s proc) root) = norm w (eval_expr s e).
  Proof.
    intros H. rewrite blocking_run_process by (rewrite H; reflexivity).
    change (statement_fuel cv32e40p_program) with 512%nat. rewrite H.
    cbv beta iota zeta delta [exec_stmt blocking_state apply_update resolve_update resolve_lvalue
      update_signal update_offset update_width update_value].
    rewrite read_signal_write_same, norm_write_low, norm_twice. reflexivity.
  Qed.
  Definition rhs proc := match process_body proc with SAssign _ e _ => e | _ => EConst 1 0 end.
  Lemma actual_negate s : norm 7 (read_signal s 1303%nat) = 24 ->
    norm 1 (read_signal s 1312%nat) = 0 ->
    norm 1 (read_signal (run_process cv32e40p_program s process_621) 1327%nat) = 0.
  Proof.
    intros Hop Hsub. rewrite (assign_value s process_621 1 1327%nat (rhs process_621) eq_refl).
    unfold rhs. cbn [process_621 process_body eval_expr]. rewrite Hop, Hsub. reflexivity.
  Qed.
  Lemma actual_operand_a s : norm 7 (read_signal s 1303%nat) = 24 ->
    norm 1 (read_signal s 1312%nat) = 0 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_622) 1328%nat) =
      norm 32 (read_signal s 1304%nat).
  Proof.
    intros Hop Hsub. rewrite (assign_value s process_622 32 1328%nat (rhs process_622) eq_refl).
    unfold rhs. cbn [process_622 process_body eval_expr]. rewrite Hop, Hsub.
    change (norm 32 (norm 32 (norm 32 (norm 32 (read_signal s 1304%nat)))) =
      norm 32 (read_signal s 1304%nat)). now rewrite !norm_twice.
  Qed.
  Lemma actual_operand_b s : norm 1 (read_signal s 1327%nat) = 0 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_623) 1329%nat) =
      norm 32 (read_signal s 1305%nat).
  Proof.
    intros Hneg. rewrite (assign_value s process_623 32 1329%nat (rhs process_623) eq_refl).
    unfold rhs. cbn [process_623 process_body eval_expr]. rewrite Hneg.
    change (norm 32 (norm 32 (norm 32 (read_signal s 1305%nat))) = norm 32 (read_signal s 1305%nat)).
    now rewrite !norm_twice.
  Qed.
End CV32E40PAddiAdderInputs.
