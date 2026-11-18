(** Connection of arithmetic to the actual generated ALU statements.
    Control preconditions are local; this is not a reachability theorem. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVBitSlice
  Lang.ExtendedSVBlocking Ex.Generated.CV32E40PExtendedAST
  Ex.External.CV32E40PAddiOperands Ex.External.CV32E40PAddiForwardControl
  Ex.External.CV32E40PAddiAdder.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVBitSlice
  ExtendedSVBlocking CV32E40PExtendedAST CV32E40PAddiOperands
  CV32E40PAddiForwardControl CV32E40PAddiAdder
  CV32E40PAddiDecoder.CV32E40PAddiDecoder.
Local Open Scope Z_scope.
Module CV32E40PAddiAdderAST.
  Definition items := match process_body process_624 with
    | SSeq [SSeq xs] => xs | _ => [] end.
  Definition setup := SSeq (firstn 16 items).
  Definition adjust := nth 16 items SSkip.
  Definition prepared (s : State) := blocking_state
    (exec_stmt 511 setup {| blocking_state := s; pending_nba := []; emitted_updates := [] |}).

  Lemma prepared_external s root : root <> 1330%nat -> root <> 1331%nat ->
    read_signal (prepared s) root = read_signal s root.
  Proof.
    intros H0 H1. unfold prepared.
    exact (proj1 (exec_stmt_preserves_unwritten_root 511 setup root
      {| blocking_state := s; pending_nba := []; emitted_updates := [] |}
      ltac:(cbn; intuition congruence))).
  Qed.

  Lemma assign_blocking fuel rhs lhs es :
    blocking_state (exec_stmt (S fuel) (SAssign false rhs lhs) es) =
    apply_update (blocking_state es) (resolve_update (blocking_state es) lhs
      (eval_expr (blocking_state es) rhs)).
  Proof. reflexivity. Qed.
  #[local] Opaque exec_stmt read_signal write_signal.
  Ltac reduce_setup :=
    unfold prepared, setup, items;
    cbv beta iota zeta delta [process_624 process_body firstn];
    rewrite exec_sequence;
    cbv beta iota zeta delta [fold_left];
    repeat first [rewrite read_slice_write_disjoint by (vm_compute; intuition congruence)
      | rewrite read_slice_write_same by (vm_compute; intuition congruence)
      | rewrite read_signal_write_other by discriminate
      | rewrite read_signal_write_same
      | match goal with
      | |- context [read_signal (blocking_state (exec_stmt ?f ?st ?es)) ?root] =>
        let H := constr:(unwritten_checked root st ltac:(reflexivity)) in
        rewrite (proj1 (exec_stmt_preserves_unwritten_root f st root es H))
      end
      | rewrite assign_blocking;
        cbv beta iota zeta delta [resolve_update resolve_lvalue apply_update
          update_signal update_offset update_width update_value eval_expr]];
    cbn [blocking_state].

  Lemma prepared_1330_0 s : read_slice (read_signal (prepared s) 1330%nat) 0 1 = 1.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.
  Lemma prepared_1330_1 s : read_slice (read_signal (prepared s) 1330%nat) 1 8 = read_slice (norm 32 (read_signal s 1328%nat)) 0 8.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.
  Lemma prepared_1330_9 s : read_slice (read_signal (prepared s) 1330%nat) 9 1 = 1.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.
  Lemma prepared_1330_10 s : read_slice (read_signal (prepared s) 1330%nat) 10 8 = read_slice (norm 32 (read_signal s 1328%nat)) 8 8.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.
  Lemma prepared_1330_18 s : read_slice (read_signal (prepared s) 1330%nat) 18 1 = 1.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.
  Lemma prepared_1330_19 s : read_slice (read_signal (prepared s) 1330%nat) 19 8 = read_slice (norm 32 (read_signal s 1328%nat)) 16 8.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.
  Lemma prepared_1330_27 s : read_slice (read_signal (prepared s) 1330%nat) 27 1 = 1.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.
  Lemma prepared_1330_28 s : read_slice (read_signal (prepared s) 1330%nat) 28 8 = read_slice (norm 32 (read_signal s 1328%nat)) 24 8.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.
  Lemma prepared_1331_0 s : read_slice (read_signal (prepared s) 1331%nat) 0 1 = 0.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.
  Lemma prepared_1331_1 s : read_slice (read_signal (prepared s) 1331%nat) 1 8 = read_slice (norm 32 (read_signal s 1329%nat)) 0 8.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.
  Lemma prepared_1331_9 s : read_slice (read_signal (prepared s) 1331%nat) 9 1 = 0.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.
  Lemma prepared_1331_10 s : read_slice (read_signal (prepared s) 1331%nat) 10 8 = read_slice (norm 32 (read_signal s 1329%nat)) 8 8.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.
  Lemma prepared_1331_18 s : read_slice (read_signal (prepared s) 1331%nat) 18 1 = 0.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.
  Lemma prepared_1331_19 s : read_slice (read_signal (prepared s) 1331%nat) 19 8 = read_slice (norm 32 (read_signal s 1329%nat)) 16 8.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.
  Lemma prepared_1331_27 s : read_slice (read_signal (prepared s) 1331%nat) 27 1 = 0.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.
  Lemma prepared_1331_28 s : read_slice (read_signal (prepared s) 1331%nat) 28 8 = read_slice (norm 32 (read_signal s 1329%nat)) 24 8.
  Proof.
    reduce_setup. unfold read_slice; rewrite ?Z.shiftr_0_r;
      change (2^8-1) with (mask 8); change (2^1-1) with (mask 1);
      fold norm; rewrite ?CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.norm_twice;
      unfold norm; rewrite <- ?Z.land_assoc; rewrite ?Z.land_diag; reflexivity.
  Qed.

  Lemma prepared_fields s :
    read_slice (read_signal (prepared s) 1330%nat) 0 1 = 1 /\
    read_slice (read_signal (prepared s) 1330%nat) 1 8 = read_slice (norm 32 (read_signal s 1328%nat)) 0 8 /\
    read_slice (read_signal (prepared s) 1330%nat) 9 1 = 1 /\
    read_slice (read_signal (prepared s) 1330%nat) 10 8 = read_slice (norm 32 (read_signal s 1328%nat)) 8 8 /\
    read_slice (read_signal (prepared s) 1330%nat) 18 1 = 1 /\
    read_slice (read_signal (prepared s) 1330%nat) 19 8 = read_slice (norm 32 (read_signal s 1328%nat)) 16 8 /\
    read_slice (read_signal (prepared s) 1330%nat) 27 1 = 1 /\
    read_slice (read_signal (prepared s) 1330%nat) 28 8 = read_slice (norm 32 (read_signal s 1328%nat)) 24 8 /\
    read_slice (read_signal (prepared s) 1331%nat) 0 1 = 0 /\
    read_slice (read_signal (prepared s) 1331%nat) 1 8 = read_slice (norm 32 (read_signal s 1329%nat)) 0 8 /\
    read_slice (read_signal (prepared s) 1331%nat) 9 1 = 0 /\
    read_slice (read_signal (prepared s) 1331%nat) 10 8 = read_slice (norm 32 (read_signal s 1329%nat)) 8 8 /\
    read_slice (read_signal (prepared s) 1331%nat) 18 1 = 0 /\
    read_slice (read_signal (prepared s) 1331%nat) 19 8 = read_slice (norm 32 (read_signal s 1329%nat)) 16 8 /\
    read_slice (read_signal (prepared s) 1331%nat) 27 1 = 0 /\
    read_slice (read_signal (prepared s) 1331%nat) 28 8 = read_slice (norm 32 (read_signal s 1329%nat)) 24 8.
  Proof.
    repeat match goal with |- _ /\ _ => split end.
    - exact (prepared_1330_0 s).
    - exact (prepared_1330_1 s).
    - exact (prepared_1330_9 s).
    - exact (prepared_1330_10 s).
    - exact (prepared_1330_18 s).
    - exact (prepared_1330_19 s).
    - exact (prepared_1330_27 s).
    - exact (prepared_1330_28 s).
    - exact (prepared_1331_0 s).
    - exact (prepared_1331_1 s).
    - exact (prepared_1331_9 s).
    - exact (prepared_1331_10 s).
    - exact (prepared_1331_18 s).
    - exact (prepared_1331_19 s).
    - exact (prepared_1331_27 s).
    - exact (prepared_1331_28 s).
  Qed.
End CV32E40PAddiAdderAST.
