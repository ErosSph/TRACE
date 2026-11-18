(** Ordered combinational cuts.  These are identities of the existing fold,
    not an alternative scheduler and not an assumption of convergence. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection.
Import ListNotations ExtendedSV ExtendedSVRootProjection.
Module ExtendedSVCombCut.
  Definition before_process p n s :=
    fold_left (run_process p) (filter is_comb (firstn n (processes p))) s.
  Definition avoids_root root ps :=
    forallb (fun proc => negb (existsb (Nat.eqb root) (process_writers proc))) ps.

  Lemma avoids_root_sound root ps : avoids_root root ps = true ->
    forall proc, In proc ps -> ~ In root (process_writers proc).
  Proof.
    intros H proc Hin Hwrite. unfold avoids_root in H.
    apply forallb_forall with (x := proc) in H; [|exact Hin].
    apply negb_true_iff in H.
    assert (existsb (Nat.eqb root) (process_writers proc) = true) as E.
    { apply existsb_exists. exists root. split; [exact Hwrite|apply Nat.eqb_refl]. }
    congruence.
  Qed.
  Lemma split_at {A} (xs : list A) n x : nth_error xs n = Some x ->
    xs = firstn n xs ++ x :: skipn (S n) xs.
  Proof.
    induction n as [|n IH] in xs |- *; destruct xs; cbn; intros H; try discriminate.
    - inversion H. reflexivity.
    - f_equal. now apply IH.
  Qed.
  Theorem comb_cut_root p n proc s root :
    nth_error (processes p) n = Some proc -> is_comb proc = true ->
    avoids_root root (filter is_comb (skipn (S n) (processes p))) = true ->
    read_signal (comb_round p s) root =
    read_signal (run_process p (before_process p n s) proc) root.
  Proof.
    intros Hnth Hcomb Havoid. unfold comb_round, before_process.
    rewrite (split_at _ _ _ Hnth) at 1.
    rewrite filter_app, fold_left_app. cbn [filter]. rewrite Hcomb.
    cbn [fold_left]. apply fold_run_process_preserves_root.
    now apply avoids_root_sound.
  Qed.
  Theorem before_process_keeps_root p n s root :
    avoids_root root (filter is_comb (firstn n (processes p))) = true ->
    read_signal (before_process p n s) root = read_signal s root.
  Proof.
    intros H. unfold before_process. apply fold_run_process_preserves_root.
    now apply avoids_root_sound.
  Qed.
  Lemma firstn_successor {A} (xs : list A) n x : nth_error xs n = Some x ->
    firstn (S n) xs = firstn n xs ++ [x].
  Proof.
    induction n as [|n IH] in xs |- *; destruct xs; cbn; intros H; try discriminate.
    - inversion H. reflexivity.
    - f_equal. now apply IH.
  Qed.
  Theorem before_process_next p n proc s :
    nth_error (processes p) n = Some proc -> is_comb proc = true ->
    before_process p (S n) s = run_process p (before_process p n s) proc.
  Proof.
    intros Hnth Hcomb. unfold before_process.
    rewrite (firstn_successor _ _ _ Hnth), filter_app, fold_left_app.
    cbn [filter]. rewrite Hcomb. reflexivity.
  Qed.
  Theorem cut_final_root p n s root :
    avoids_root root (filter is_comb (skipn n (processes p))) = true ->
    read_signal (comb_round p s) root = read_signal (before_process p n s) root.
  Proof.
    intros H. unfold comb_round, before_process.
    rewrite <- (firstn_skipn n (processes p)) at 1.
    rewrite filter_app, fold_left_app. apply fold_run_process_preserves_root.
    now apply avoids_root_sound.
  Qed.

End ExtendedSVCombCut.
