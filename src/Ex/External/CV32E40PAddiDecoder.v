(** Symbolic ADDI path through the actual blocking decoder AST. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVBitSlice Lang.ExtendedSVBlocking.
Require Import Ex.Generated.CV32E40PExtendedAST.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVBitSlice ExtendedSVBlocking CV32E40PExtendedAST.
Local Open Scope Z_scope.
Module CV32E40PAddiDecoder.
  Definition decoder_items := match process_body process_1376 with
    | SSeq [SSeq xs] => xs | _ => [] end.
  Definition defaults := firstn (length decoder_items - 2) decoder_items.
  Definition opcode_case := nth (length decoder_items - 2) decoder_items SSkip.
  Definition compressed_check := nth (length decoder_items - 1) decoder_items SSkip.
  Definition opcode_arms := match opcode_case with SCase _ xs => xs | _ => [] end.
  Definition opimm := snd (nth 8 opcode_arms (None, SSkip)).
  Definition opimm_items := match opimm with SSeq xs => xs | _ => [] end.
  Definition opimm_prefix := firstn 4 opimm_items.
  Definition funct_case := nth 4 opimm_items SSkip.
  Definition funct_arms := match funct_case with SCase _ xs => xs | _ => [] end.
  Definition opcode_expr := ESel 7 (EVar 32 945%nat) (EConst 5 0).
  Definition funct_expr := ESel 3 (EVar 32 945%nat) (EConst 5 12).

  Lemma decoder_shape : process_body process_1376 =
    SSeq [SSeq (defaults ++ [opcode_case; compressed_check])].
  Proof. reflexivity. Qed.
  Lemma opcode_shape : opcode_case = SCase opcode_expr opcode_arms.
  Proof. reflexivity. Qed.
  Lemma opimm_shape : opimm = SSeq (opimm_prefix ++ [funct_case]).
  Proof. reflexivity. Qed.
  Lemma funct_shape : funct_case = SCase funct_expr funct_arms.
  Proof. reflexivity. Qed.
  Lemma choose_opimm s : select_case_stmt s 19 opcode_arms SSkip = opimm.
  Proof. reflexivity. Qed.
  Lemma choose_add s : select_case_stmt s 0 funct_arms SSkip =
    SAssign false (EConst 7 24) (LVar 7 948%nat).
  Proof. reflexivity. Qed.
  Lemma unwritten_checked root st : existsb (Nat.eqb root) (stmt_writers st) = false ->
    ~ In root (stmt_writers st).
  Proof.
    intros H Hin. assert (existsb (Nat.eqb root) (stmt_writers st) = true).
    { apply existsb_exists. exists root. split; [exact Hin|apply Nat.eqb_refl]. }
    congruence.
  Qed.
  Lemma defaults_do_not_write_instruction : ~ In 945%nat (stmt_writers (SSeq defaults)).
  Proof. apply unwritten_checked. vm_compute. reflexivity. Qed.
  Lemma prefix_does_not_write_instruction : ~ In 945%nat (stmt_writers (SSeq opimm_prefix)).
  Proof. apply unwritten_checked. vm_compute. reflexivity. Qed.
  Lemma tail_does_not_write_operator : ~ In 948%nat (stmt_writers compressed_check).
  Proof. apply unwritten_checked. vm_compute. reflexivity. Qed.

  Lemma field_reads_same s s' : read_signal s 945%nat = read_signal s' 945%nat ->
    eval_expr s opcode_expr = eval_expr s' opcode_expr /\
    eval_expr s funct_expr = eval_expr s' funct_expr.
  Proof. intros H. unfold opcode_expr, funct_expr. cbn [eval_expr]. now rewrite H. Qed.

  Lemma write_operator_low old : norm 7 (write_slice old 0 7 24) = 24.
  Proof.
    pose proof (read_slice_write_same old 0 7 24 ltac:(lia) ltac:(lia)) as H.
    unfold read_slice in H. rewrite Z.shiftr_0_r in H. exact H.
  Qed.

  #[local] Opaque opimm_prefix funct_case defaults opcode_case compressed_check opcode_arms funct_arms.
  Lemma exec_sequence fuel xs es : exec_stmt (S fuel) (SSeq xs) es =
    fold_left (fun st cmd => exec_stmt fuel cmd st) xs es.
  Proof. reflexivity. Qed.
  Lemma exec_case fuel e arms es : exec_stmt (S fuel) (SCase e arms) es =
    exec_stmt fuel (select_case_stmt (blocking_state es)
      (eval_expr (blocking_state es) e) arms SSkip) es.
  Proof. reflexivity. Qed.
  Lemma opimm_add_operator es : eval_expr (blocking_state es) funct_expr = 0 ->
    norm 7 (read_signal (blocking_state (exec_stmt 509 opimm es)) 948%nat) = 24.
  Proof.
    intros Hfunct. rewrite opimm_shape.
    rewrite exec_sequence, fold_left_app.
    set (mid := fold_left (fun st cmd => exec_stmt 508 cmd st) opimm_prefix es).
    assert (Hread : read_signal (blocking_state mid) 945%nat = read_signal (blocking_state es) 945%nat).
    { pose proof (proj1 (exec_stmt_preserves_unwritten_root 509 (SSeq opimm_prefix)
        945%nat es prefix_does_not_write_instruction)) as Hr.
      rewrite exec_sequence in Hr. exact Hr. }
    clearbody mid.
    pose proof (proj2 (field_reads_same _ _ Hread)) as Hfunct'.
    rewrite Hfunct in Hfunct'.
    change (norm 7 (read_signal (blocking_state (exec_stmt 508 funct_case mid)) 948%nat) = 24).
    rewrite funct_shape, exec_case, Hfunct', choose_add.
    change (norm 7 (read_signal (write_signal (blocking_state mid) 948%nat
      (write_slice (read_signal (blocking_state mid) 948%nat) 0 7 24)) 948%nat) = 24).
    rewrite read_signal_write_same. apply write_operator_low.
  Qed.
  Lemma fold_one {A B} (f : A -> B -> A) a b : fold_left f [b] a = f a b.
  Proof. reflexivity. Qed.
  Lemma fold_two {A B} (f : A -> B -> A) a b c : fold_left f [b;c] a = f (f a b) c.
  Proof. reflexivity. Qed.
  Lemma fold_cons {A B} (f : A -> B -> A) a b xs :
    fold_left f (b :: xs) a = fold_left f xs (f a b).
  Proof. reflexivity. Qed.

  Theorem actual_decoder_addi_operator es :
    eval_expr (blocking_state es) opcode_expr = 19 ->
    eval_expr (blocking_state es) funct_expr = 0 ->
    norm 7 (read_signal
      (blocking_state (exec_stmt 512 (process_body process_1376) es)) 948%nat) = 24.
  Proof.
    intros Hop Hfunct.
    rewrite decoder_shape, exec_sequence, fold_one, exec_sequence, fold_left_app.
    set (mid := fold_left (fun st cmd => exec_stmt 510 cmd st) defaults es).
    assert (Hr : read_signal (blocking_state mid) 945%nat = read_signal (blocking_state es) 945%nat).
    { pose proof (proj1 (exec_stmt_preserves_unwritten_root 511 (SSeq defaults)
        945%nat es defaults_do_not_write_instruction)) as H.
      rewrite exec_sequence in H. exact H. }
    clearbody mid.
    destruct (field_reads_same _ _ Hr) as [Hop' Hfunct'].
    rewrite Hop in Hop'. rewrite Hfunct in Hfunct'.
    rewrite fold_two.
    rewrite (proj1 (exec_stmt_preserves_unwritten_root 510 compressed_check
      948%nat (exec_stmt 510 opcode_case mid) tail_does_not_write_operator)).
    rewrite opcode_shape, exec_case, Hop', choose_opimm.
    now apply opimm_add_operator.
  Qed.
  Lemma decoder_is_blocking : blocking_onlyb (process_body process_1376) = true.
  Proof. vm_compute. reflexivity. Qed.
  Theorem actual_decoder_run_operator s :
    eval_expr s opcode_expr = 19 -> eval_expr s funct_expr = 0 ->
    norm 7 (read_signal (run_process cv32e40p_program s process_1376) 948%nat) = 24.
  Proof.
    intros Hop Hfunct. rewrite blocking_run_process by exact decoder_is_blocking.
    apply actual_decoder_addi_operator; assumption.
  Qed.

  Definition comb_prefix := filter is_comb (firstn 1376 (processes cv32e40p_program)).
  Definition comb_middle := filter is_comb (firstn 39 (skipn 1377 (processes cv32e40p_program))).
  Definition comb_tail := filter is_comb (skipn 1417 (processes cv32e40p_program)).
  Lemma split_at {A} (xs : list A) n x : nth_error xs n = Some x ->
    xs = firstn n xs ++ x :: skipn (S n) xs.
  Proof.
    induction n as [|n IH] in xs |- *; destruct xs; cbn; intros H; try discriminate.
    - inversion H. reflexivity.
    - f_equal. now apply IH.
  Qed.
  Lemma filter_yes {A} (f : A -> bool) x xs : f x = true ->
    filter f (x :: xs) = x :: filter f xs.
  Proof. intros H. cbn. now rewrite H. Qed.
  Lemma real_comb_decomposition : filter is_comb (processes cv32e40p_program) =
    comb_prefix ++ process_1376 :: (comb_middle ++ process_1416 :: comb_tail).
  Proof.
    pose proof (split_at (processes cv32e40p_program) 1376 process_1376 eq_refl) as H0.
    pose proof (split_at (skipn 1377 (processes cv32e40p_program)) 39 process_1416 eq_refl) as H1.
    rewrite skipn_skipn in H1.
    unfold comb_prefix, comb_middle, comb_tail.
    rewrite H0 at 1. rewrite filter_app.
    rewrite filter_yes by reflexivity.
    rewrite H1 at 1. rewrite filter_app, filter_yes by reflexivity. reflexivity.
  Qed.
  Lemma order_unwritten_checked root ps :
    forallb (fun p => negb (existsb (Nat.eqb root) (process_writers p))) ps = true ->
    forall p, In p ps -> ~ In root (process_writers p).
  Proof.
    intros H p Hin. apply forallb_forall with (x := p) in H; [|exact Hin].
    apply negb_true_iff in H. apply unwritten_checked. exact H.
  Qed.
  Lemma middle_keeps_operator : forall p, In p comb_middle -> ~ In 948%nat (process_writers p).
  Proof. apply order_unwritten_checked. vm_compute. reflexivity. Qed.
  Lemma tail_keeps_id_operator : forall p, In p comb_tail -> ~ In 780%nat (process_writers p).
  Proof. apply order_unwritten_checked. vm_compute. reflexivity. Qed.
  Definition decoder_input_state s := fold_left (run_process cv32e40p_program) comb_prefix s.
  #[local] Opaque comb_prefix comb_middle comb_tail decoder_input_state.

  Lemma wire_operator s : norm 7 (read_signal s 948%nat) = 24 ->
    norm 7 (read_signal (run_process cv32e40p_program s process_1416) 780%nat) = 24.
  Proof.
    intros Hop. change (norm 7 (read_signal
      (write_signal s 780%nat (write_slice (read_signal s 780%nat) 0 7
        (norm 7 (norm 7 (read_signal s 948%nat))))) 780%nat) = 24).
    rewrite read_signal_write_same, Hop. apply write_operator_low.
  Qed.
  Theorem fullcore_comb_addi_id_operator s :
    eval_expr (decoder_input_state s) opcode_expr = 19 ->
    eval_expr (decoder_input_state s) funct_expr = 0 ->
    norm 7 (read_signal (comb_round cv32e40p_program s) 780%nat) = 24.
  Proof.
    intros Hop Hfunct. unfold comb_round. rewrite real_comb_decomposition, fold_left_app.
    Transparent decoder_input_state. unfold decoder_input_state in Hop, Hfunct.
    set (before := fold_left (run_process cv32e40p_program) comb_prefix s) in *.
    clearbody before.
    rewrite fold_cons, fold_left_app.
    set (middle := fold_left (run_process cv32e40p_program) comb_middle
      (run_process cv32e40p_program before process_1376)).
    assert (Hmid : norm 7 (read_signal middle 948%nat) = 24).
    { unfold middle. rewrite fold_run_process_preserves_root by exact middle_keeps_operator.
      apply actual_decoder_run_operator; assumption. }
    clearbody middle.
    rewrite fold_cons.
    rewrite fold_run_process_preserves_root by exact tail_keeps_id_operator.
    now apply wire_operator.
  Qed.
  Print Assumptions opimm_add_operator.
  Print Assumptions actual_decoder_addi_operator.
  Print Assumptions fullcore_comb_addi_id_operator.
End CV32E40PAddiDecoder.
