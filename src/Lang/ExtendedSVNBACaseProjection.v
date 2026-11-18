(** Exact single-root interpreter for nonblocking-only statement trees.
    Blocking assignments rejected; cases use original priority selection. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice.
Module ExtendedSVNBACaseProjection.
  Fixpoint nba_onlyb (st : Stmt) : bool :=
    match st with
    | SSkip => true
    | SAssign nba _ _ => nba
    | SSeq xs => forallb nba_onlyb xs
    | SIf _ yes no => nba_onlyb yes && nba_onlyb no
    | SCase _ arms => forallb (fun arm => nba_onlyb (snd arm)) arms
    end.

  Lemma selected_nba s value arms default:
      forallb (fun arm => nba_onlyb (snd arm)) arms = true ->
      nba_onlyb default = true ->
      nba_onlyb (select_case_stmt s value arms default) = true.
  Proof.
    induction arms as [|[key body] rest IH] in default |- *; cbn; auto.
    intros H HD. apply andb_true_iff in H as [HB HR].
    destruct key as [e|]; [destruct (Z.eqb value (eval_expr s e))|]; auto.
  Qed.

  Fixpoint nba_root (fuel : nat) (st : Stmt) (s : State)
      (root : signal) (value : Z) : Z :=
    match fuel with
    | O => value
    | S f => match st with
      | SSkip => value
      | SAssign _ rhs lhs =>
          apply_update_root_value root value (resolve_update s lhs (eval_expr s rhs))
      | SSeq xs => fold_left (fun v st => nba_root f st s root v) xs value
      | SIf guard yes no => if Z.eqb (eval_expr s guard) 0
          then nba_root f no s root value else nba_root f yes s root value
      | SCase scr arms => nba_root f (select_case_stmt s (eval_expr s scr) arms SSkip) s root value
      end
    end.

  Theorem nba_root_sound : forall fuel st es root value,
      nba_onlyb st = true ->
      blocking_state (exec_stmt fuel st es) = blocking_state es /\
      apply_updates_root_value root value (emitted_updates (exec_stmt fuel st es)) =
        nba_root fuel st (blocking_state es) root
          (apply_updates_root_value root value (emitted_updates es)).
  Proof.
    induction fuel as [|fuel IH]; intros st es root value Hnba; cbn; [auto|].
    destruct st as [|nba rhs lhs|xs|guard yes no|scrutinee arms]; cbn in Hnba |- *.
    - auto.
    - subst nba. cbn. split; [reflexivity|]. rewrite apply_root_app. reflexivity.
    - induction xs as [|st xs IHr] in es, Hnba |- *; cbn in *; [auto|].
      apply andb_true_iff in Hnba as [Hst Hxs].
      destruct (IH st es root value Hst) as [Hstate Hvalue].
      destruct (IHr (exec_stmt fuel st es) Hxs) as [Hrest Hresult].
      split; [congruence|]. rewrite Hresult, Hstate, Hvalue. reflexivity.
    - apply andb_true_iff in Hnba as [Hy Hn].
      destruct (Z.eqb (eval_expr (blocking_state es) guard) 0); apply IH; assumption.
    - apply IH. apply selected_nba; [exact Hnba|reflexivity].
  Qed.

  Corollary process_nba_projection : forall p proc s root value,
      nba_onlyb (process_body proc) = true ->
      apply_updates_root_value root value (process_updates p s proc) =
        nba_root (statement_fuel p) (process_body proc) s root value.
  Proof.
    intros. exact (proj2 (nba_root_sound (statement_fuel p) (process_body proc)
      {| blocking_state := s; pending_nba := []; emitted_updates := [] |}
      root value H)).
  Qed.

  Fixpoint nba_root_pruned (fuel : nat) (st : Stmt) (s : State)
      (root : signal) (value : Z) : Z :=
    if existsb (Nat.eqb root) (stmt_writers st) then
      match fuel with
      | O => value
      | S f => match st with
        | SAssign _ rhs lhs => apply_update_root_value root value
            (resolve_update s lhs (eval_expr s rhs))
        | SSeq xs => fold_left (fun v st => nba_root_pruned f st s root v) xs value
        | SIf guard yes no => if Z.eqb (eval_expr s guard) 0
            then nba_root_pruned f no s root value else nba_root_pruned f yes s root value
        | SCase scr arms => nba_root_pruned f (select_case_stmt s (eval_expr s scr) arms SSkip) s root value
        | _ => value
        end
      end
    else value.

  Lemma nba_root_no_writer : forall fuel st s root value,
      ~ In root (stmt_writers st) -> nba_root fuel st s root value = value.
  Proof.
    induction fuel as [|fuel IH]; intros st s root value Hnone; [reflexivity|].
    destruct st as [|nba rhs lhs|xs|guard yes no|scrutinee arms]; cbn in *.
    - reflexivity.
    - unfold apply_update_root_value. rewrite resolve_update_root.
      destruct (Nat.eqb (lvalue_root lhs) root) eqn:E; [|reflexivity].
      apply Nat.eqb_eq in E. exfalso. apply Hnone. now left.
    - induction xs as [|st xs IHr] in value, Hnone |- *; cbn in *; [reflexivity|].
      rewrite IH.
      + apply IHr. intro H. apply Hnone. apply in_or_app. auto.
      + intro H. apply Hnone. apply in_or_app. auto.
    - destruct (Z.eqb (eval_expr s guard) 0); apply IH;
        intro H; apply Hnone; apply in_or_app; auto.
    - apply IH. intro H. apply Hnone.
      exact (select_case_writers s (eval_expr s scrutinee) arms SSkip root H).
  Qed.

  Theorem nba_root_pruned_sound : forall fuel st es root value,
      nba_onlyb st = true ->
      blocking_state (exec_stmt fuel st es) = blocking_state es /\
      apply_updates_root_value root value (emitted_updates (exec_stmt fuel st es)) =
        nba_root_pruned fuel st (blocking_state es) root
          (apply_updates_root_value root value (emitted_updates es)).
  Proof.
    induction fuel as [|fuel IH]; intros st es root value Hnba.
    - cbn. destruct (existsb (Nat.eqb root) (stmt_writers st)); auto.
    - cbn [nba_root_pruned].
      destruct (existsb (Nat.eqb root) (stmt_writers st)) eqn:Hw.
      2: {
        split; [exact (proj1 (nba_root_sound (S fuel) st es root value Hnba))|].
        assert (Hnone : ~ In root (stmt_writers st)).
        { intros Hin. assert (existsb (Nat.eqb root) (stmt_writers st) = true).
          { apply existsb_exists. exists root. split; [exact Hin|apply Nat.eqb_refl]. }
          congruence. }
        rewrite (proj2 (nba_root_sound (S fuel) st es root value Hnba)).
        now apply nba_root_no_writer.
      }
      destruct st as [|nba rhs lhs|xs|guard yes no|scrutinee arms]; cbn in Hnba |- *.
      + auto.
      + subst nba. cbn. split; [reflexivity|]. rewrite apply_root_app. reflexivity.
      + induction xs as [|st xs IHr] in es, Hnba |- *; cbn in *; [auto|].
        apply andb_true_iff in Hnba as [Hst Hxs].
        destruct (IH st es root value Hst) as [Hstate Hvalue].
        destruct (IHr (exec_stmt fuel st es) Hxs) as [Hrest Hresult].
        split; [congruence|]. rewrite Hresult, Hstate, Hvalue. reflexivity.
      + apply andb_true_iff in Hnba as [Hy Hn].
        destruct (Z.eqb (eval_expr (blocking_state es) guard) 0); apply IH; assumption.
      + apply IH. apply selected_nba; [exact Hnba|reflexivity].
  Qed.
  Corollary process_nba_pruned_projection : forall p proc s root value,
      nba_onlyb (process_body proc) = true ->
      apply_updates_root_value root value (process_updates p s proc) =
        nba_root_pruned (statement_fuel p) (process_body proc) s root value.
  Proof.
    intros. exact (proj2 (nba_root_pruned_sound (statement_fuel p) (process_body proc)
      {| blocking_state := s; pending_nba := []; emitted_updates := [] |}
      root value H)).
  Qed.
End ExtendedSVNBACaseProjection.

