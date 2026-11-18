(** Exact state-independent process slicing by a signal's static writer set. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection.
Import ListNotations ExtendedSV ExtendedSVRootProjection.

Module ExtendedSVProcessSlice.
  Lemma exec_emitted_writers : forall fuel st es u,
      In u (emitted_updates (exec_stmt fuel st es)) ->
      In u (emitted_updates es) \/ In (update_signal u) (stmt_writers st).
  Proof.
    induction fuel as [|fuel IH]; intros st es u Hin; cbn in Hin; [auto|].
    destruct st as [|nba rhs lhs|stmts|guard yes no|scrutinee arms].
    - auto.
    - destruct nba; cbn in Hin; apply in_app_or in Hin;
        destruct Hin as [H|[<-|[]]]; auto;
        right; cbn; rewrite resolve_update_root; auto.
    - cbn in Hin. induction stmts as [|st rest IHr] in es, Hin |- *.
      + cbn in *. auto.
      + cbn in Hin. apply IHr in Hin. destruct Hin as [H|H].
        * apply IH in H. destruct H as [H|H]; auto.
          right. cbn. apply in_or_app. auto.
        * right. cbn. apply in_or_app. auto.
    - destruct (Z.eqb (eval_expr (blocking_state es) guard) 0).
      + apply IH in Hin. destruct Hin as [H|H]; auto.
        right. cbn. apply in_or_app. auto.
      + apply IH in Hin. destruct Hin as [H|H]; auto.
        right. cbn. apply in_or_app. auto.
    - apply IH in Hin. destruct Hin as [H|H]; auto. right.
      pose proof (select_case_writers (blocking_state es)
        (eval_expr (blocking_state es) scrutinee) arms SSkip
        (update_signal u) H) as Hwriter.
      exact Hwriter.
  Qed.

  Lemma process_emitted_writers : forall p s proc u,
      In u (process_updates p s proc) ->
      In (update_signal u) (process_writers proc).
  Proof.
    intros p s proc u H. unfold process_updates in H.
    apply exec_emitted_writers in H. destruct H as [H|H]; [contradiction|exact H].
  Qed.

  Lemma apply_root_app : forall root updates rest value,
      apply_updates_root_value root value (updates ++ rest) =
      apply_updates_root_value root (apply_updates_root_value root value updates) rest.
  Proof. intros root updates. induction updates; intros; cbn; auto. Qed.

  Lemma apply_root_avoids : forall root updates value,
      updates_avoid root updates -> apply_updates_root_value root value updates = value.
  Proof.
    intros root updates. induction updates as [|u us IH]; intros value H; cbn; auto.
    rewrite IH.
    - unfold apply_update_root_value.
      assert (Hu : Nat.eqb (update_signal u) root = false).
      { apply Nat.eqb_neq. apply H. now left. }
      now rewrite Hu.
    - intros u' Hin. apply H. now right.
  Qed.

  Definition writes_rootb (root : signal) (proc : Process) : bool :=
    existsb (Nat.eqb root) (process_writers proc).

  Theorem process_slice_sound : forall p s order root value,
      apply_updates_root_value root value
        (flat_map (process_updates p s) order) =
      apply_updates_root_value root value
        (flat_map (process_updates p s) (filter (writes_rootb root) order)).
  Proof.
    intros p s order. induction order as [|proc rest IH]; intros root value; cbn; auto.
    destruct (writes_rootb root proc) eqn:E; cbn.
    - rewrite !apply_root_app. apply IH.
    - rewrite apply_root_app.
      rewrite (apply_root_avoids root (process_updates p s proc) value); [apply IH|].
      intros u Hin Heq.
      pose proof (process_emitted_writers p s proc u Hin) as Hwriter.
      unfold writes_rootb in E.
      assert (Hex : existsb (Nat.eqb root) (process_writers proc) = true).
      { apply existsb_exists. exists (update_signal u). split; auto.
        subst root. apply Nat.eqb_refl. }
      congruence.
  Qed.

  Lemma filter_swap : forall A (f g : A -> bool) xs,
      filter f (filter g xs) = filter g (filter f xs).
  Proof.
    intros A f g xs. induction xs as [|x xs IH]; cbn; auto.
    destruct (f x) eqn:F; destruct (g x) eqn:G;
      cbn; rewrite ?F, ?G, ?IH; reflexivity.
  Qed.
End ExtendedSVProcessSlice.
