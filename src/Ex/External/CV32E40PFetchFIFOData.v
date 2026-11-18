(** Symbolic data projections of the unchanged two-entry fetch FIFO.
    The contents are arbitrary words, not a fixed instruction trace. *)
From Coq Require Import ZArith List Bool Lia btauto.Btauto.
Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking Lang.ExtendedSVRootProjection
  Lang.ExtendedSVBitSlice Ex.Generated.CV32E40PExtendedAST
  Ex.External.CV32E40PFetchFIFOCount Ex.External.CV32E40PAddiOperands
  Ex.External.CV32E40PAddiAdderBits Ex.External.CV32E40PAddiIDEXAccept
  Ex.External.CV32E40PAddiForwardControl Ex.External.CV32E40PAddiDecoder.
Import ListNotations ExtendedSV ExtendedSVBlocking ExtendedSVRootProjection
  ExtendedSVBitSlice CV32E40PExtendedAST
  CV32E40PAddiOperands CV32E40PAddiAdderBits CV32E40PAddiIDEXAccept
  CV32E40PAddiForwardControl CV32E40PAddiDecoder CV32E40PFetchFIFOCount.
Local Open Scope Z_scope.
Module CV32E40PFetchFIFOData.
  Definition word_at memory pointer := read_slice memory (32 * norm 1 pointer) 32.
  Definition index_offset pointer := norm 6 (Z.shiftr
    (norm 32 (Z.shiftl (norm 32 (norm 1 pointer)) 5)) 0).
  Lemma index_offset_exact pointer : index_offset pointer = 32 * norm 1 pointer.
  Proof. unfold index_offset. destruct (bit_cases pointer) as [H|H]; rewrite H; reflexivity. Qed.
  Lemma word_at_norm memory pointer : word_at (norm 64 memory) pointer = word_at memory pointer.
  Proof.
    pose proof (norm_range 1 pointer). change (0 <= norm 1 pointer < 2) in H.
    unfold word_at. apply slice_norm; lia.
  Qed.
  Lemma keep fuel st es root :
    existsb (Nat.eqb root) (stmt_writers st) = false ->
    read_signal (blocking_state (exec_stmt fuel st es)) root = read_signal (blocking_state es) root.
  Proof. intros H. exact (proj1 (exec_stmt_preserves_unwritten_root fuel st root es (unwritten_checked root st H))). Qed.
  Lemma norm_write_old w old offset width value :
    norm w (write_slice (norm w old) offset width value) =
    norm w (write_slice old offset width value).
  Proof.
    unfold norm, write_slice. apply Z.bits_inj. intros i.
    rewrite !Z.land_spec, !Z.lor_spec, !Z.land_spec. btauto.
  Qed.
  #[local] Opaque read_signal write_signal norm write_slice.
  Lemma initial_head es :
    norm 32 (read_signal (blocking_state (exec_stmt 511 initial es)) 470%nat) =
    word_at (read_signal (blocking_state es) 481%nat) (read_signal (blocking_state es) 475%nat).
  Proof.
    unfold initial, items. cbn [process_1570 process_body firstn]. straight.
    change (norm 32 5) with 5. change (norm 32 0) with 0.
    change (norm 32 (Z.shiftr (norm 64 (read_signal (blocking_state es) 481%nat))
      (index_offset (read_signal (blocking_state es) 475%nat))) =
      word_at (read_signal (blocking_state es) 481%nat) (read_signal (blocking_state es) 475%nat)).
    rewrite index_offset_exact.
    change (word_at (norm 64 (read_signal (blocking_state es) 481%nat))
      (read_signal (blocking_state es) 475%nat) =
      word_at (read_signal (blocking_state es) 481%nat) (read_signal (blocking_state es) 475%nat)).
    apply word_at_norm.
  Qed.
  Lemma initial_memory es :
    norm 64 (read_signal (blocking_state (exec_stmt 511 initial es)) 480%nat) =
    norm 64 (read_signal (blocking_state es) 481%nat).
  Proof. unfold initial, items. cbn [process_1570 process_body firstn]. straight. reflexivity. Qed.
  Lemma initial_read_pointer es :
    norm 1 (read_signal (blocking_state (exec_stmt 511 initial es)) 474%nat) =
    norm 1 (read_signal (blocking_state es) 475%nat).
  Proof. unfold initial, items. cbn [process_1570 process_body firstn]. straight. reflexivity. Qed.
  Lemma initial_write_pointer es :
    norm 1 (read_signal (blocking_state (exec_stmt 511 initial es)) 476%nat) =
    norm 1 (read_signal (blocking_state es) 477%nat).
  Proof. unfold initial, items. cbn [process_1570 process_body firstn]. straight. reflexivity. Qed.
  Lemma push_memory es :
    norm 64 (read_signal (blocking_state (exec_stmt 510 push es)) 480%nat) =
    if eval_expr (blocking_state es) (guard push) =? 0 then
      norm 64 (read_signal (blocking_state es) 480%nat)
    else norm 64 (write_slice (read_signal (blocking_state es) 480%nat)
      (32 * norm 1 (read_signal (blocking_state es) 477%nat)) 32
      (norm 32 (read_signal (blocking_state es) 468%nat))).
  Proof.
    change push with (SIf (guard push) (SSeq (match push with SIf _ (SSeq xs) _ => xs | _ => [] end)) SSkip) at 1.
    rewrite exec_if. destruct (eval_expr (blocking_state es) (guard push) =? 0); [reflexivity|].
    unfold push, items. cbn [process_1570 process_body nth]. straight.
    change (norm 32 5) with 5. change (norm 32 0) with 0.
    change (norm 64 (write_slice (read_signal (blocking_state es) 480%nat)
      (0 + index_offset (read_signal (blocking_state es) 477%nat)) 32
      (norm 32 (read_signal (blocking_state es) 468%nat))) =
      norm 64 (write_slice (read_signal (blocking_state es) 480%nat)
        (32 * norm 1 (read_signal (blocking_state es) 477%nat)) 32
        (norm 32 (read_signal (blocking_state es) 468%nat)))).
    rewrite index_offset_exact, Z.add_0_l. reflexivity.
  Qed.
  Lemma push_write_pointer es :
    norm 1 (read_signal (blocking_state (exec_stmt 510 push es)) 476%nat) =
    if eval_expr (blocking_state es) (guard push) =? 0 then
      norm 1 (read_signal (blocking_state es) 476%nat)
    else norm 1 (1 + norm 1 (read_signal (blocking_state es) 477%nat)).
  Proof.
    change push with (SIf (guard push) (SSeq (match push with SIf _ (SSeq xs) _ => xs | _ => [] end)) SSkip) at 1.
    rewrite exec_if. destruct (eval_expr (blocking_state es) (guard push) =? 0); [reflexivity|].
    unfold push, items. cbn [process_1570 process_body nth]. straight. change (norm 1 1) with 1. reflexivity.
  Qed.
  Lemma pop_read_pointer es :
    norm 1 (read_signal (blocking_state (exec_stmt 510 pop es)) 474%nat) =
    if eval_expr (blocking_state es) (guard pop) =? 0 then
      norm 1 (read_signal (blocking_state es) 474%nat)
    else norm 1 (1 + norm 1 (read_signal (blocking_state es) 475%nat)).
  Proof.
    change pop with (SIf (guard pop) (SSeq (match pop with SIf _ (SSeq xs) _ => xs | _ => [] end)) SSkip) at 1.
    rewrite exec_if. destruct (eval_expr (blocking_state es) (guard pop) =? 0); [reflexivity|].
    unfold pop, items. cbn [process_1570 process_body nth]. straight. change (norm 1 1) with 1. reflexivity.
  Qed.
  #[local] Opaque initial push pop both.
  Ltac split_process :=
    rewrite actual_shape, exec_sequence, fold_one, exec_sequence, fold_left_app;
    change (fold_left (fun es st => exec_stmt 510 st es) (firstn 6 items)) with
      (exec_stmt 511 initial);
    rewrite fold_cons, fold_two.
  Theorem actual_head es :
    norm 32 (read_signal (blocking_state (exec_stmt 512 (process_body process_1570) es)) 470%nat) =
    word_at (read_signal (blocking_state es) 481%nat) (read_signal (blocking_state es) 475%nat).
  Proof.
    split_process.
    rewrite (keep 510 both _ 470%nat eq_refl), (keep 510 pop _ 470%nat eq_refl),
      (keep 510 push _ 470%nat eq_refl), initial_head. reflexivity.
  Qed.
  Definition read_pointer_step s := if eval_expr s (guard pop) =? 0 then norm 1 (read_signal s 475%nat)
    else norm 1 (1 + norm 1 (read_signal s 475%nat)).
  Definition write_pointer_step s := if eval_expr s (guard push) =? 0 then norm 1 (read_signal s 477%nat)
    else norm 1 (1 + norm 1 (read_signal s 477%nat)).
  Definition memory_step s := if eval_expr s (guard push) =? 0 then norm 64 (read_signal s 481%nat)
    else norm 64 (write_slice (read_signal s 481%nat) (32 * norm 1 (read_signal s 477%nat)) 32
      (norm 32 (read_signal s 468%nat))).
  Theorem actual_read_pointer es :
    norm 1 (read_signal (blocking_state (exec_stmt 512 (process_body process_1570) es)) 474%nat) =
    read_pointer_step (blocking_state es).
  Proof.
    split_process. rewrite (keep 510 both _ 474%nat eq_refl), pop_read_pointer.
    rewrite (eval_guard_same _ _ pop ltac:(simpl; auto) (push_inputs _)),
      (eval_guard_same _ _ pop ltac:(simpl; auto) (initial_inputs _)).
    rewrite (keep 510 push _ 474%nat eq_refl), initial_read_pointer,
      (keep 510 push _ 475%nat eq_refl), (keep 511 initial _ 475%nat eq_refl). reflexivity.
  Qed.
  Theorem actual_write_pointer es :
    norm 1 (read_signal (blocking_state (exec_stmt 512 (process_body process_1570) es)) 476%nat) =
    write_pointer_step (blocking_state es).
  Proof.
    split_process. rewrite (keep 510 both _ 476%nat eq_refl), (keep 510 pop _ 476%nat eq_refl), push_write_pointer.
    rewrite (eval_guard_same _ _ push ltac:(simpl; auto) (initial_inputs _)),
      initial_write_pointer, (keep 511 initial _ 477%nat eq_refl). reflexivity.
  Qed.
  Theorem actual_memory es :
    norm 64 (read_signal (blocking_state (exec_stmt 512 (process_body process_1570) es)) 480%nat) =
    memory_step (blocking_state es).
  Proof.
    split_process. rewrite (keep 510 both _ 480%nat eq_refl), (keep 510 pop _ 480%nat eq_refl), push_memory.
    rewrite (eval_guard_same _ _ push ltac:(simpl; auto) (initial_inputs _)),
      (keep 511 initial _ 477%nat eq_refl), (keep 511 initial _ 468%nat eq_refl).
    unfold memory_step. destruct (eval_expr (blocking_state es) (guard push) =? 0).
    - apply initial_memory.
    - rewrite <- (norm_write_old 64 (read_signal (blocking_state (exec_stmt 511 initial es)) 480%nat)).
      rewrite initial_memory, norm_write_old. reflexivity.
  Qed.
  Print Assumptions actual_memory.
End CV32E40PFetchFIFOData.
