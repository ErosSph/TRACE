(** Exact signed-add and byte-concatenation processes of the generated ALU. *)
From Coq Require Import ZArith Lia List.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVBitSlice
  Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiOperands
  Ex.External.CV32E40PAddiAdder Ex.External.CV32E40PAddiAdderBits.
Import ExtendedSV ExtendedSVRootProjection ExtendedSVBitSlice
  CV32E40PExtendedAST CV32E40PAddiOperands CV32E40PAddiAdder CV32E40PAddiAdderBits
  CV32E40PAddiIDEXAccept.CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PAddiAdderResult.
  Lemma norm_down w total x : (w <= total)%nat -> norm w (norm total x) = norm w x.
  Proof.
    intros H. change (read_slice (norm total x) 0 (Z.of_nat w) = read_slice x 0 (Z.of_nat w)).
    apply slice_norm; lia.
  Qed.
  Lemma norm_low_write w total old value : (w <= total)%nat ->
    norm w (write_slice old 0 (Z.of_nat total) value) = norm w value.
  Proof.
    intros H. rewrite <- (norm_down w total (write_slice old 0 (Z.of_nat total) value) H).
    rewrite norm_write_low. apply norm_down; exact H.
  Qed.
  Lemma signed_norm w x : signed_value w (norm w x) = signed_value w x.
  Proof. unfold signed_value. now rewrite norm_twice. Qed.
  Lemma concat_value high low hi lo : (high = hi+lo)%nat ->
    0 <= low < 2^Z.of_nat lo ->
    forall top, 0 <= top < 2^Z.of_nat hi ->
    norm high (Z.lor (Z.shiftl top (Z.of_nat lo)) low) = 2^Z.of_nat lo*top+low.
  Proof.
    intros -> Hl top Ht. rewrite concat_arith by lia.
    apply norm_small. rewrite Nat2Z.inj_add, Z.pow_add_r by lia.
    pose proof (Z.pow_pos_nonneg 2 (Z.of_nat hi) ltac:(lia) ltac:(lia)).
    pose proof (Z.pow_pos_nonneg 2 (Z.of_nat lo) ltac:(lia) ltac:(lia)). nia.
  Qed.
  Lemma actual_add_low36 s :
    norm 36 (read_signal (run_process cv32e40p_program s process_625) 1333%nat) =
    norm 36 (read_signal s 1330%nat + read_signal s 1331%nat).
  Proof.
    change (norm 36 (read_signal (write_signal s 1333%nat
      (write_slice (read_signal s 1333%nat) 0 37
        (norm 37 (norm 37
          (norm 37 (signed_value 36 (norm 36 (read_signal s 1330%nat))) +
           norm 37 (signed_value 36 (norm 36 (read_signal s 1331%nat)))))))) 1333%nat) =
      norm 36 (read_signal s 1330%nat + read_signal s 1331%nat)).
    rewrite read_signal_write_same.
    rewrite (norm_low_write 36 37) by lia.
    rewrite !norm_twice, !signed_norm. apply signed_mod36.
  Qed.
  Definition extract_expr := match process_body process_626 with
    | SAssign _ rhs _ => rhs | _ => EConst 32 0 end.
  Lemma extract_expr_correct s : eval_expr s extract_expr = unpack (read_signal s 1333%nat).
  Proof.
    unfold extract_expr. cbn [process_626 process_body eval_expr expr_width].
    change (norm 6 28) with 28. change (norm 6 19) with 19.
    change (norm 6 10) with 10. change (norm 6 1) with 1.
    rewrite (concat_value 32 _ 8 24) by (try reflexivity; apply norm_range).
    rewrite (concat_value 24 _ 8 16) by (try reflexivity; apply norm_range).
    rewrite (concat_value 16 _ 8 8) by (try reflexivity; apply norm_range).
    change (2^Z.of_nat 24) with 16777216. change (2^Z.of_nat 16) with 65536.
    change (2^Z.of_nat 8) with 256.
    change (16777216 * read_slice (norm 37 (read_signal s 1333%nat)) 28 8 +
      (65536 * read_slice (norm 37 (read_signal s 1333%nat)) 19 8 +
       (256 * read_slice (norm 37 (read_signal s 1333%nat)) 10 8 +
        read_slice (norm 37 (read_signal s 1333%nat)) 1 8)) = unpack (read_signal s 1333%nat)).
    rewrite !slice_norm by lia. rewrite unpack_slices. ring.
  Qed.
  Lemma actual_extract s :
    norm 32 (read_signal (run_process cv32e40p_program s process_626) 1332%nat) =
      unpack (read_signal s 1333%nat).
  Proof.
    change (norm 32 (read_signal (write_signal s 1332%nat
      (write_slice (read_signal s 1332%nat) 0 32 (norm 32 (eval_expr s extract_expr)))) 1332%nat) =
      unpack (read_signal s 1333%nat)).
    rewrite read_signal_write_same, norm_write_low, extract_expr_correct, norm_twice.
    unfold unpack. apply norm_small.
    change (2^Z.of_nat 32) with 4294967296. div_lia.
  Qed.
  Theorem actual_add_and_extract s :
    norm 32 (read_signal (run_process cv32e40p_program
      (run_process cv32e40p_program s process_625) process_626) 1332%nat) =
    unpack (read_signal s 1330%nat + read_signal s 1331%nat).
  Proof.
    rewrite actual_extract.
    rewrite <- (unpack_norm _ 36 ltac:(lia)), actual_add_low36.
    apply unpack_norm; lia.
  Qed.
  Print Assumptions actual_add_and_extract.
End CV32E40PAddiAdderResult.
