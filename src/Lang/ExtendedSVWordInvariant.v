(** Raw fixed-width signal preservation.

    [eval_expr] always normalizes values, but [write_slice] deliberately keeps
    bits outside the selected field.  Consequently an equality about
    [norm width (read_signal ...)] is not, by itself, an equality about the
    raw signal stored in [State].  This reusable invariant says that a root
    starts normalized and is only written through a full-width [LVar]. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection.
Import ListNotations ExtendedSV ExtendedSVRootProjection.
Local Open Scope Z_scope.

Module ExtendedSVWordInvariant.

Definition Word (width : nat) (value : Z) : Prop :=
  value = norm width value.

Definition WordRoot width root s := Word width (read_signal s root).

Definition WordUpdate width root update :=
  update_signal update <> root \/
  (update_offset update = 0 /\ update_width update = width).

Fixpoint word_writesb width root statement : bool :=
  match statement with
  | SSkip => true
  | SAssign _ _ lvalue =>
      if Nat.eqb (lvalue_root lvalue) root then
        match lvalue with
        | LVar written_width _ => Nat.eqb written_width width
        | _ => false
        end
      else true
  | SSeq statements => forallb (word_writesb width root) statements
  | SIf _ yes no => word_writesb width root yes && word_writesb width root no
  | SCase _ arms => forallb (fun arm => word_writesb width root (snd arm)) arms
  end.

Lemma norm_idempotent width value : norm width (norm width value) = norm width value.
Proof. unfold norm. rewrite <- Z.land_assoc, Z.land_diag. reflexivity. Qed.

Lemma norm_is_word width value : Word width (norm width value).
Proof. unfold Word. symmetry. apply norm_idempotent. Qed.

Lemma full_slice_is_word width old value :
  Word width old -> Word width (write_slice old 0 (Z.of_nat width) value).
Proof.
  intros Hold.
  assert (Hexact : write_slice old 0 (Z.of_nat width) value = norm width value).
  { unfold Word in Hold. rewrite Hold at 1.
    unfold write_slice, norm, mask. rewrite Z.shiftl_0_r.
    rewrite <- Z.land_assoc, Z.land_lnot_diag, Z.land_0_r, Z.lor_0_l.
    reflexivity. }
  rewrite Hexact. apply norm_is_word.
Qed.

Lemma resolved_word width root s lvalue value :
  (if Nat.eqb (lvalue_root lvalue) root then
      match lvalue with
      | LVar written_width _ => Nat.eqb written_width width
      | _ => false
      end
   else true) = true ->
  WordUpdate width root (resolve_update s lvalue value).
Proof.
  destruct (Nat.eqb (lvalue_root lvalue) root) eqn:E; intros H.
  - apply Nat.eqb_eq in E. destruct lvalue as [written_width id|]; [|discriminate].
    apply Nat.eqb_eq in H. subst written_width. right. split; reflexivity.
  - left. rewrite resolve_update_root. now apply Nat.eqb_neq.
Qed.

Lemma update_word width root s update :
  WordRoot width root s -> WordUpdate width root update ->
  WordRoot width root (apply_update s update).
Proof.
  intros Hroot [Hother|[Hoffset Hwidth]].
  - unfold WordRoot. rewrite read_signal_apply_update_other by exact Hother.
    exact Hroot.
  - destruct (Nat.eq_dec (update_signal update) root) as [E|E].
    + unfold WordRoot, apply_update. rewrite E, read_signal_write_same.
      rewrite Hoffset, Hwidth. apply full_slice_is_word. exact Hroot.
    + unfold WordRoot. rewrite read_signal_apply_update_other by exact E.
      exact Hroot.
Qed.

Lemma apply_updates_word width root updates s :
  Forall (WordUpdate width root) updates -> WordRoot width root s ->
  WordRoot width root (apply_updates s updates).
Proof.
  intros Hupdates. induction Hupdates in s |- *; cbn; auto.
  intros Hs. apply IHHupdates. now apply update_word.
Qed.

Lemma apply_nba_word width root updates s :
  Forall (WordUpdate width root) updates -> WordRoot width root s ->
  WordRoot width root (apply_nba s updates).
Proof.
  intros Hupdates. induction Hupdates in s |- *; cbn [apply_nba fold_left]; auto.
  intros Hs. apply IHHupdates. now apply update_word.
Qed.

Definition ExecWord width root es :=
  WordRoot width root (blocking_state es) /\
  Forall (WordUpdate width root) (pending_nba es) /\
  Forall (WordUpdate width root) (emitted_updates es).

Lemma selected_word width root s value arms default :
  forallb (fun arm => word_writesb width root (snd arm)) arms = true ->
  word_writesb width root default = true ->
  word_writesb width root (select_case_stmt s value arms default) = true.
Proof.
  induction arms as [|[key body] rest IH] in default |- *; cbn; auto.
  intros H Hd. apply andb_true_iff in H as [Hb Hr].
  destruct key as [key|]; [destruct (value =? eval_expr s key)|]; auto.
Qed.

Theorem exec_word fuel statement width root es :
  word_writesb width root statement = true -> ExecWord width root es ->
  ExecWord width root (exec_stmt fuel statement es).
Proof.
  induction fuel as [|fuel IH] in statement, es |- *; [auto|].
  destruct statement as [|nba expression lvalue|statements|guard yes no|expression arms];
    cbn [word_writesb]; intros H Hword.
  - exact Hword.
  - pose proof (resolved_word width root (blocking_state es) lvalue
      (eval_expr (blocking_state es) expression) H) as Hupdate.
    destruct Hword as [Hs [Hp He]]. destruct nba;
      unfold ExecWord; cbn [exec_stmt blocking_state pending_nba emitted_updates].
    + split; [exact Hs|]. split; apply Forall_app; split; auto; constructor; auto.
    + split; [now apply update_word|]. split; [exact Hp|].
      apply Forall_app. split; auto.
  - cbn [exec_stmt]. induction statements as [|statement statements IHrest]
      in es, H, Hword |- *; cbn [fold_left]; [exact Hword|].
    apply andb_true_iff in H as [Hstatement Hstatements].
    apply IHrest; [exact Hstatements|]. now apply IH.
  - apply andb_true_iff in H as [Hy Hn]. cbn [exec_stmt].
    destruct (eval_expr (blocking_state es) guard =? 0); apply IH; assumption.
  - cbn [exec_stmt]. apply IH.
    + apply selected_word; [exact H|reflexivity].
    + exact Hword.
Qed.

Definition program_wordb program width root :=
  forallb (fun process => word_writesb width root (process_body process))
    (processes program).

Lemma process_word program width root process s :
  word_writesb width root (process_body process) = true ->
  WordRoot width root s ->
  WordRoot width root (run_process program s process) /\
  Forall (WordUpdate width root) (process_updates program s process).
Proof.
  intros H Hs.
  pose proof (exec_word (statement_fuel program) (process_body process) width root
    {| blocking_state := s; pending_nba := []; emitted_updates := [] |} H
    ltac:(repeat split; auto; constructor)) as [Hb [Hp He]].
  split; [unfold run_process; now apply apply_nba_word|exact He].
Qed.

Lemma process_word_checked program width root process :
  program_wordb program width root = true -> In process (processes program) ->
  word_writesb width root (process_body process) = true.
Proof.
  intros H Hin. unfold program_wordb in H.
  now apply forallb_forall with (x := process) in H.
Qed.

Lemma fold_word program width root process_list s :
  program_wordb program width root = true ->
  (forall process, In process process_list -> In process (processes program)) ->
  WordRoot width root s ->
  WordRoot width root (fold_left (run_process program) process_list s).
Proof.
  intros H. induction process_list as [|process rest IH] in s |- *; cbn; auto.
  intros Hin Hs. apply IH.
  - intros next Hnext. apply Hin. now right.
  - exact (proj1 (process_word program width root process s
      (process_word_checked program width root process H
        (Hin process (or_introl eq_refl))) Hs)).
Qed.

Lemma round_word program width root s :
  program_wordb program width root = true -> WordRoot width root s ->
  WordRoot width root (comb_round program s).
Proof.
  intros H Hs. unfold comb_round. apply fold_word; auto.
  intros process Hin. apply filter_In in Hin. tauto.
Qed.

Lemma iter_word program width root fuel s :
  program_wordb program width root = true -> WordRoot width root s ->
  WordRoot width root (comb_iter program fuel s).
Proof. intros H. induction fuel in s |- *; cbn; auto. intros Hs. apply IHfuel. now apply round_word. Qed.

Lemma lfp_word program width root s :
  program_wordb program width root = true -> WordRoot width root s ->
  WordRoot width root (lfp_candidate program s).
Proof. apply iter_word. Qed.

Lemma initialize_word program width root s :
  program_wordb program width root = true -> WordRoot width root s ->
  WordRoot width root (initialize program s).
Proof.
  intros Hp Hs. unfold initialize. apply fold_word; auto.
  intros process Hin. apply filter_In in Hin. tauto.
Qed.

Lemma zero_state_word signal_count width root :
  WordRoot width root (repeat 0 signal_count).
Proof.
  unfold WordRoot, Word. induction signal_count in root |- *;
    destruct root; cbn; auto; reflexivity.
Qed.

Lemma phase_word program width root event s :
  program_wordb program width root = true -> changed_signal event <> root ->
  WordRoot width root s -> WordRoot width root (PhaseSemantics program event s).
Proof.
  intros Hp He Hs.
  assert (Hd : WordRoot width root (phase_driven_state program event s)).
  { unfold phase_driven_state. apply lfp_word; [exact Hp|].
    unfold WordRoot. rewrite read_signal_write_other by exact He. exact Hs. }
  unfold PhaseSemantics, phase_execute_order, execute_process_order.
  apply lfp_word; [exact Hp|]. apply apply_updates_word; [|exact Hd].
  apply Forall_forall. intros update Hu. apply in_flat_map in Hu as [process [Hprocess Hu]].
  unfold selected_on_transition in Hprocess. apply filter_In in Hprocess as [Hin _].
  pose proof (proj2 (process_word program width root process
    (phase_driven_state program event s)
    (process_word_checked program width root process Hp Hin) Hd)) as Hupdates.
  now apply Forall_forall with (x := update) in Hupdates.
Qed.

Print Assumptions phase_word.
End ExtendedSVWordInvariant.
