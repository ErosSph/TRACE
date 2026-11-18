(** Design-independent rules for a process containing one assignment.
    Exact run_process/process_updates semantics; no CPU, expected output,
    fixed input trace or termination axiom occurs in these rules. *)
From Coq Require Import List ZArith Lia Bool btauto.Btauto.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice.
Import ExtendedSV ExtendedSVBitSlice ListNotations.
Module ExtendedSVAssignment.
Local Opaque eval_expr resolve_update apply_update.

Theorem assignment_process_updates p proc s nba rhs lhs :
 process_body proc = SAssign nba rhs lhs ->
 (0 < statement_fuel p)%nat ->
 process_updates p s proc = [resolve_update s lhs (eval_expr s rhs)].
Proof.
 intros Hbody Hfuel. unfold process_updates. rewrite Hbody.
 destruct (statement_fuel p); [lia|]. destruct nba; reflexivity.
Qed.

Theorem assignment_run_process p proc s nba rhs lhs :
 process_body proc = SAssign nba rhs lhs ->
 (0 < statement_fuel p)%nat ->
 run_process p s proc = apply_update s (resolve_update s lhs (eval_expr s rhs)).
Proof.
 intros Hbody Hfuel. unfold run_process. rewrite Hbody.
 destruct (statement_fuel p); [lia|]. destruct nba; reflexivity.
Qed.
Print Assumptions assignment_process_updates.
Print Assumptions assignment_run_process.

Theorem norm_full_low_write width old value :
 norm width (write_slice old 0 (Z.of_nat width) value) = norm width value.
Proof.
 pose proof (read_slice_write_same old 0 (Z.of_nat width) value
   (Z.le_refl 0) (Nat2Z.is_nonneg width)) as H.
 unfold read_slice in H. rewrite !Z.shiftr_0_r in H. exact H.
Qed.
Theorem norm_one_boolz b : norm 1 (boolz b) = boolz b.
Proof. destruct b; reflexivity. Qed.
Print Assumptions norm_full_low_write.

Theorem write_slice_overwrite old offset width first second :
 write_slice (write_slice old offset width first) offset width second =
 write_slice old offset width second.
Proof.
 unfold write_slice. apply Z.bits_inj. intros bit.
 destruct (Z_lt_ge_dec bit 0).
 - rewrite !Z.testbit_neg_r by lia. reflexivity.
 - repeat first [rewrite Z.lor_spec | rewrite Z.land_spec | rewrite Z.lnot_spec by lia].
   btauto.
Qed.
Print Assumptions write_slice_overwrite.
Theorem two_writes_idempotent s x y vx vy : x <> y ->
 write_signal (write_signal (write_signal (write_signal s x vx) y vy) x vx) y vy =
 write_signal (write_signal s x vx) y vy.
Proof.
 intros Hxy.
 rewrite (write_signal_commute (write_signal s x vx) y x vy vx) by congruence.
 rewrite !write_signal_write_same. reflexivity.
Qed.
End ExtendedSVAssignment.
