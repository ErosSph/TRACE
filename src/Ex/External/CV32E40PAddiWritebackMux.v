(** Actual EX ALU-port mux. CSR and multiply override ALU in the RTL;
    their disabled guards are explicit, not silently dropped. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVBlocking
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiOperands
  Ex.External.CV32E40PAddiForwardControl.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVBlocking
  CV32E40PExtendedAST CV32E40PAddiOperands CV32E40PAddiForwardControl
  CV32E40PAddiDecoder.CV32E40PAddiDecoder.
Local Open Scope Z_scope.
Module CV32E40PAddiWritebackMux.
  Definition outer_items := match process_body process_1789 with
    | SSeq [SSeq xs] => xs | _ => [] end.
  Definition body_items := match nth 5 outer_items SSkip with
    | SSeq xs => xs | _ => [] end.
  Definition prefix := SSeq (firstn 5 outer_items).
  Definition controls := SSeq (firstn 3 body_items).
  Definition alu := nth 3 body_items SSkip.
  Definition mult := nth 4 body_items SSkip.
  Definition csr := nth 5 body_items SSkip.
  Lemma shape : process_body process_1789 = SSeq [SSeq
    (firstn 5 outer_items ++ [SSeq (firstn 3 body_items ++ [alu;mult;csr])])].
  Proof. reflexivity. Qed.

  Lemma no_override fuel es en src : norm 1 (read_signal (blocking_state es) en) = 0 ->
    exec_stmt (S fuel) (SIf (EVar 1 en) (SAssign false (EVar 32 src) (LVar 32 1269%nat)) SSkip) es = es.
  Proof. intros H. rewrite exec_if. cbn [eval_expr]. rewrite H. destruct fuel; reflexivity. Qed.
  Lemma selects_alu fuel es : norm 1 (read_signal (blocking_state es) 1198%nat) = 1 ->
    norm 32 (read_signal (blocking_state (exec_stmt (S (S fuel)) alu es)) 1269%nat) =
    norm 32 (read_signal (blocking_state es) 1278%nat).
  Proof.
    intros H. change alu with (SIf (EVar 1 1198%nat)
      (SAssign false (EVar 32 1278%nat) (LVar 32 1269%nat)) SSkip).
    rewrite exec_if. cbn [eval_expr]. rewrite H. cbn [Z.eqb].
    cbv beta iota zeta delta [exec_stmt blocking_state apply_update resolve_update resolve_lvalue
      update_signal update_offset update_width update_value eval_expr].
    rewrite read_signal_write_same, norm_write_low.
    now rewrite !CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice.
  Qed.
  Lemma preserves_inputs fuel st es root :
    existsb (Nat.eqb root) (stmt_writers st) = false ->
    read_signal (blocking_state (exec_stmt fuel st es)) root = read_signal (blocking_state es) root.
  Proof. intros H. exact (proj1 (exec_stmt_preserves_unwritten_root fuel st root es (unwritten_checked root st H))). Qed.
  #[local] Opaque exec_stmt.
  Theorem actual_ex_alu_value s :
    norm 1 (read_signal s 1198%nat) = 1 ->
    norm 1 (read_signal s 1210%nat) = 0 ->
    norm 1 (read_signal s 1260%nat) = 0 ->
    norm 32 (read_signal (run_process cv32e40p_program s process_1789) 1269%nat) =
    norm 32 (read_signal s 1278%nat).
  Proof.
    intros Ha Hm Hc. rewrite blocking_run_process by reflexivity.
    change (statement_fuel cv32e40p_program) with 512%nat.
    rewrite shape, exec_sequence, fold_one, exec_sequence, fold_left_app, fold_one,
      exec_sequence, fold_left_app, fold_cons, fold_two.
    set (es0 := {| blocking_state := s; pending_nba := []; emitted_updates := [] |}).
    rewrite <- (exec_sequence 510 (firstn 5 outer_items) es0). fold prefix.
    rewrite <- (exec_sequence 509 (firstn 3 body_items) (exec_stmt 511 prefix es0)). fold controls.
    assert (Pres : forall root, In root [1198%nat;1210%nat;1260%nat;1278%nat] ->
      read_signal (blocking_state (exec_stmt 510 controls (exec_stmt 511 prefix es0))) root = read_signal s root).
    { intros root Hroot. repeat destruct Hroot as [Hroot|Hroot]; try contradiction; subst root;
        rewrite !preserves_inputs by reflexivity; reflexivity. }
    change csr with (SIf (EVar 1 1260%nat) (SAssign false (EVar 32 1261%nat) (LVar 32 1269%nat)) SSkip).
    rewrite no_override.
    2: { rewrite !preserves_inputs by reflexivity. exact Hc. }
    change mult with (SIf (EVar 1 1210%nat) (SAssign false (EVar 32 1279%nat) (LVar 32 1269%nat)) SSkip).
    rewrite no_override.
    2: { rewrite !preserves_inputs by reflexivity. exact Hm. }
    rewrite selects_alu.
    - rewrite Pres by (cbn; auto). reflexivity.
    - rewrite Pres by (cbn; auto). exact Ha.
  Qed.
End CV32E40PAddiWritebackMux.
