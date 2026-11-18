(** The actual 624 -> 625 -> 626 scalar carry cone, with arbitrary operands.
    Does not assume the post-state contains the expected arithmetic result. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVBitSlice
  Lang.ExtendedSVBlocking Ex.Generated.CV32E40PExtendedAST
  Ex.External.CV32E40PAddiAdder Ex.External.CV32E40PAddiAdderBits
  Ex.External.CV32E40PAddiAdderAST Ex.External.CV32E40PAddiAdderResult
  Ex.External.CV32E40PAddiOperands Ex.External.CV32E40PAddiForwardControl.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVBitSlice
  ExtendedSVBlocking CV32E40PExtendedAST CV32E40PAddiAdder CV32E40PAddiAdderBits
  CV32E40PAddiAdderAST CV32E40PAddiAdderResult CV32E40PAddiOperands
  CV32E40PAddiForwardControl CV32E40PAddiDecoder.CV32E40PAddiDecoder.
Local Open Scope Z_scope.
Module CV32E40PAddiCarryCone.
  Lemma prepared_values s :
    norm 36 (read_signal (prepared s) 1330%nat) = pack (norm 32 (read_signal s 1328%nat)) + spacers /\
    norm 36 (read_signal (prepared s) 1331%nat) = pack (norm 32 (read_signal s 1329%nat)).
  Proof.
    destruct (prepared_fields s) as (A0&A1&A9&A10&A18&A19&A27&A28&B0&B1&B9&B10&B18&B19&B27&B28).
    split; rewrite reconstruct36;
      rewrite ?A0, ?A1, ?A9, ?A10, ?A18, ?A19, ?A27, ?A28,
        ?B0, ?B1, ?B9, ?B10, ?B18, ?B19, ?B27, ?B28;
      rewrite !slice_div by lia; unfold pack, spacers;
      change (2^0) with 1; change (2^8) with 256;
      change (2^16) with 65536; change (2^24) with 16777216;
      rewrite ?Z.div_1_r; ring.
  Qed.
  Lemma adjust_scalar_identity es :
    norm 1 (read_signal (blocking_state es) 1327%nat) = 0 ->
    norm 7 (read_signal (blocking_state es) 1303%nat) = 24 ->
    norm 2 (read_signal (blocking_state es) 1307%nat) = 0 ->
    exec_stmt 510 adjust es = es.
  Proof.
    intros Hneg Hop Hvec. unfold adjust, CV32E40PAddiAdderAST.items.
    cbv beta iota zeta delta [process_624 process_body nth].
    rewrite exec_if. cbn [eval_expr]. rewrite Hneg, Hop.
    change (norm 7 20) with 20. change (norm 7 22) with 22.
    cbn [Z.eqb boolz]. change (norm 1 (Z.lor 0 (norm 1 (Z.lor 0 0)))) with 0.
    cbn [Z.eqb]. rewrite exec_sequence, fold_one, exec_case.
    cbn [eval_expr]. rewrite Hvec.
    cbn [select_case_stmt eval_expr]. change (norm 2 2) with 2.
    change (norm 2 3) with 3. reflexivity.
  Qed.
  #[local] Opaque exec_stmt.
  Lemma prepared_fold s : prepared s = blocking_state
    (fold_left (fun es st => exec_stmt 510 st es) (firstn 16 CV32E40PAddiAdderAST.items)
      {| blocking_state := s; pending_nba := []; emitted_updates := [] |}).
  Proof. unfold prepared, setup. rewrite exec_sequence. reflexivity. Qed.
  #[local] Opaque prepared.
  Lemma actual_carry_setup s :
    norm 1 (read_signal s 1327%nat) = 0 ->
    norm 7 (read_signal s 1303%nat) = 24 ->
    norm 2 (read_signal s 1307%nat) = 0 ->
    run_process cv32e40p_program s process_624 = prepared s.
  Proof.
    intros Hneg Hop Hvec. rewrite blocking_run_process by reflexivity.
    change (statement_fuel cv32e40p_program) with 512%nat.
    assert (Shape : process_body process_624 = SSeq [SSeq (firstn 16 CV32E40PAddiAdderAST.items ++ [adjust])]) by reflexivity.
    rewrite Shape, exec_sequence, fold_one, exec_sequence, fold_left_app, fold_one.
    rewrite adjust_scalar_identity.
    - symmetry. apply prepared_fold.
    - rewrite <- prepared_fold.
      rewrite prepared_external by discriminate. exact Hneg.
    - rewrite <- prepared_fold.
      rewrite prepared_external by discriminate. exact Hop.
    - rewrite <- prepared_fold.
      rewrite prepared_external by discriminate. exact Hvec.
  Qed.
  Definition carry_cone s := run_process cv32e40p_program
    (run_process cv32e40p_program (run_process cv32e40p_program s process_624) process_625) process_626.
  Theorem actual_scalar_carry_cone s :
    norm 1 (read_signal s 1327%nat) = 0 ->
    norm 7 (read_signal s 1303%nat) = 24 ->
    norm 2 (read_signal s 1307%nat) = 0 ->
    norm 32 (read_signal (carry_cone s) 1332%nat) =
      norm 32 (read_signal s 1328%nat + read_signal s 1329%nat).
  Proof.
    intros Hneg Hop Hvec. unfold carry_cone.
    rewrite actual_add_and_extract, actual_carry_setup by assumption.
    destruct (prepared_values s) as [Ha Hb].
    rewrite <- (unpack_norm _ 36 ltac:(lia)).
    assert (Hsum : norm 36 (read_signal (prepared s) 1330%nat + read_signal (prepared s) 1331%nat) =
      norm 36 (norm 36 (read_signal (prepared s) 1330%nat) + norm 36 (read_signal (prepared s) 1331%nat))).
    { rewrite !norm_mod. apply Z.add_mod. apply Z.pow_nonzero; lia. }
    rewrite Hsum, Ha, Hb, unpack_norm by lia. rewrite scalar_carry_network.
    rewrite !norm_mod. change (2^Z.of_nat 32) with 4294967296.
    symmetry. apply Z.add_mod; lia.
  Qed.
  Print Assumptions actual_scalar_carry_cone.
End CV32E40PAddiCarryCone.
