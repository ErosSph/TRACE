(** Memory-isolated structural proof for the unsigned-compare arm of process_1896. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking Lang.ExtendedSVCombCut
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiDecoder
  Ex.External.CV32E40PAddiWritebackMux Ex.External.CV32E40PAddiOperands
  Ex.External.CV32E40PScalarMuxSlt.
Import ListNotations ExtendedSV ExtendedSVBlocking ExtendedSVCombCut
  CV32E40PExtendedAST CV32E40PAddiOperands CV32E40PScalarMuxSlt.
Import CV32E40PAddiDecoder.CV32E40PAddiDecoder
  CV32E40PAddiWritebackMux.CV32E40PAddiWritebackMux
  CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PScalarMuxSltu.
Lemma actual_mux_sltu s : norm 7 (read_signal s 1303%nat) = 3 ->
  norm 32 (read_signal (run_process cv32e40p_program s process_1896) 1314%nat) =
  norm 32 (norm 1 (read_signal s 1315%nat)).
Proof.
  intros Hop. rewrite blocking_run_process by reflexivity.
  change (statement_fuel cv32e40p_program) with 512%nat.
  cbn [process_1896 process_body].
  rewrite exec_sequence, fold_one, exec_sequence, fold_two, exec_case.
  cbn [eval_expr].
  rewrite (preserves_inputs 510
    (SAssign false (EConst 32 0) (LVar 32 1314%nat)) _ 1303%nat eq_refl).
  cbn [blocking_state]. rewrite Hop. cbn [select_case_stmt eval_expr].
  normalize_preceding_opcodes. change (norm 7 3) with 3.
  cbn [Z.eqb Pos.eqb].
  cbv beta iota zeta delta
    [exec_stmt blocking_state apply_update resolve_update resolve_lvalue
     update_signal update_offset update_width update_value eval_expr].
  rewrite read_signal_write_same, norm_write_low, !norm_twice.
  repeat rewrite read_signal_write_other by discriminate. reflexivity.
Qed.
Print Assumptions actual_mux_sltu.
End CV32E40PScalarMuxSltu.
