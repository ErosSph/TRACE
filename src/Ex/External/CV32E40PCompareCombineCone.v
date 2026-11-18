(** Scalar lexicographic combination, as executed by the original process
    591. The expressions below are extracted from that AST, not replacements. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking Lang.ExtendedSVCombCut
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiDecoder
  Ex.External.CV32E40PAddiWritebackMux Ex.External.CV32E40PAddiOperands
  Ex.External.CV32E40PAddiIDEXAccept Ex.External.CV32E40PAddiForwardControl
  Ex.External.CV32E40PAddiFullCoreALU Ex.External.CV32E40PAddiOperandCone.
Import ListNotations ExtendedSV ExtendedSVBlocking ExtendedSVCombCut CV32E40PExtendedAST
  CV32E40PAddiDecoder CV32E40PAddiWritebackMux CV32E40PAddiOperands
  CV32E40PAddiIDEXAccept CV32E40PAddiForwardControl CV32E40PAddiOperandCone.
Local Open Scope Z_scope.
Module CV32E40PCompareCombineCone.

Definition equal_expression := match process_body process_591 with
  | SSeq [SSeq (SAssign _ e _ :: _)] => e | _ => EConst 4 0 end.
Definition greater_expression := match process_body process_591 with
  | SSeq [SSeq (_ :: SAssign _ e _ :: _)] => e | _ => EConst 4 0 end.
Definition vector_case := match process_body process_591 with
  | SSeq [SSeq [_; _; c]] => c | _ => SSkip end.

Theorem actual_scalar_combine s : norm 2 (read_signal s 1307%nat) = 0 ->
  norm 4 (read_signal (run_process cv32e40p_program s process_591) 1350%nat) =
    norm 4 (eval_expr s equal_expression) /\
  norm 4 (read_signal (run_process cv32e40p_program s process_591) 1351%nat) =
    norm 4 (eval_expr s greater_expression).
Proof.
  intros HV. rewrite blocking_run_process by reflexivity.
  change (statement_fuel cv32e40p_program) with 512%nat.
  change (norm 4 (read_signal (blocking_state (exec_stmt 512
    (SSeq [SSeq [SAssign false equal_expression (LVar 4 1350%nat);
      SAssign false greater_expression (LVar 4 1351%nat); vector_case]])
      {| blocking_state := s; pending_nba := []; emitted_updates := [] |})) 1350%nat) =
      norm 4 (eval_expr s equal_expression) /\
    norm 4 (read_signal (blocking_state (exec_stmt 512
    (SSeq [SSeq [SAssign false equal_expression (LVar 4 1350%nat);
      SAssign false greater_expression (LVar 4 1351%nat); vector_case]])
      {| blocking_state := s; pending_nba := []; emitted_updates := [] |})) 1351%nat) =
      norm 4 (eval_expr s greater_expression)).
  rewrite !exec_sequence, !fold_one.
  rewrite !exec_sequence. cbn [fold_left].
  unfold vector_case. cbn [process_591 process_body].
  rewrite !exec_case. cbn [eval_expr].
  rewrite (preserves_inputs 510 (SAssign false greater_expression (LVar 4 1351%nat))
    _ 1307%nat eq_refl).
  rewrite (preserves_inputs 510 (SAssign false equal_expression (LVar 4 1350%nat))
    _ 1307%nat eq_refl).
  cbn [blocking_state]. rewrite HV.
  cbn [select_case_stmt eval_expr]. change (norm 2 2) with 2.
  change (norm 2 3) with 3. cbn [Z.eqb].
  cbv beta iota zeta delta [exec_stmt blocking_state apply_update resolve_update
    resolve_lvalue update_signal update_offset update_width update_value].
  rewrite read_signal_write_other by discriminate.
  rewrite !read_signal_write_same, !norm_write_low, !norm_twice.
  split; [reflexivity|]. unfold greater_expression.
  cbn [process_591 process_body eval_expr].
  repeat rewrite read_signal_write_other by discriminate. reflexivity.
Qed.

Local Opaque before_process comb_round run_process.
Theorem fullcore_scalar_combine s : norm 2 (read_signal (round s) 1307%nat) = 0 ->
  norm 4 (read_signal (round s) 1350%nat) = norm 4 (eval_expr (round s) equal_expression) /\
  norm 4 (read_signal (round s) 1351%nat) = norm 4 (eval_expr (round s) greater_expression).
Proof.
  intros HV. split.
  - CV32E40PAddiFullCoreALU.project 591 process_591 1350%nat.
    rewrite (proj1 (actual_scalar_combine (before_process cv32e40p_program 591 s)
      ltac:(CV32E40PAddiFullCoreALU.final_inputs; exact HV))).
    unfold equal_expression. cbn [process_591 process_body eval_expr].
    CV32E40PAddiFullCoreALU.final_inputs. reflexivity.
  - CV32E40PAddiFullCoreALU.project 591 process_591 1351%nat.
    rewrite (proj2 (actual_scalar_combine (before_process cv32e40p_program 591 s)
      ltac:(CV32E40PAddiFullCoreALU.final_inputs; exact HV))).
    unfold greater_expression. cbn [process_591 process_body eval_expr].
    CV32E40PAddiFullCoreALU.final_inputs. reflexivity.
Qed.
Print Assumptions actual_scalar_combine.
Print Assumptions fullcore_scalar_combine.
End CV32E40PCompareCombineCone.
