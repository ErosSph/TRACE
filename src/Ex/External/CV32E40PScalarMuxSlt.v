(** Memory-isolated structural proof for the signed-compare arm of process_1896. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking Lang.ExtendedSVCombCut
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiDecoder
  Ex.External.CV32E40PAddiWritebackMux Ex.External.CV32E40PAddiOperands.
Import ListNotations ExtendedSV ExtendedSVBlocking ExtendedSVCombCut
  CV32E40PExtendedAST CV32E40PAddiOperands.
Import CV32E40PAddiDecoder.CV32E40PAddiDecoder
  CV32E40PAddiWritebackMux.CV32E40PAddiWritebackMux
  CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PScalarMuxSlt.
Ltac normalize_preceding_opcodes :=
  change (norm 7 21) with 21; change (norm 7 46) with 46;
  change (norm 7 47) with 47; change (norm 7 24) with 24;
  change (norm 7 28) with 28; change (norm 7 26) with 26;
  change (norm 7 30) with 30; change (norm 7 25) with 25;
  change (norm 7 29) with 29; change (norm 7 27) with 27;
  change (norm 7 31) with 31; change (norm 7 39) with 39;
  change (norm 7 37) with 37; change (norm 7 36) with 36;
  change (norm 7 38) with 38; change (norm 7 42) with 42;
  change (norm 7 40) with 40; change (norm 7 41) with 41;
  change (norm 7 43) with 43; change (norm 7 44) with 44;
  change (norm 7 73) with 73; change (norm 7 58) with 58;
  change (norm 7 59) with 59; change (norm 7 56) with 56;
  change (norm 7 57) with 57; change (norm 7 63) with 63;
  change (norm 7 62) with 62; change (norm 7 45) with 45;
  change (norm 7 16) with 16; change (norm 7 17) with 17;
  change (norm 7 18) with 18; change (norm 7 19) with 19;
  change (norm 7 20) with 20; change (norm 7 22) with 22;
  change (norm 7 23) with 23; change (norm 7 12) with 12;
  change (norm 7 13) with 13; change (norm 7 9) with 9;
  change (norm 7 11) with 11; change (norm 7 1) with 1;
  change (norm 7 5) with 5; change (norm 7 8) with 8;
  change (norm 7 10) with 10; change (norm 7 0) with 0;
  change (norm 7 4) with 4; change (norm 7 2) with 2.
Lemma actual_mux_slt s : norm 7 (read_signal s 1303%nat) = 2 ->
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
  normalize_preceding_opcodes. cbn [Z.eqb Pos.eqb].
  cbv beta iota zeta delta
    [exec_stmt blocking_state apply_update resolve_update resolve_lvalue
     update_signal update_offset update_width update_value eval_expr].
  rewrite read_signal_write_same, norm_write_low, !norm_twice.
  repeat rewrite read_signal_write_other by discriminate. reflexivity.
Qed.
Print Assumptions actual_mux_slt.
End CV32E40PScalarMuxSlt.
