(** Blocking-process certificates, including actual Case selection. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV.
Import ListNotations ExtendedSV.
Module ExtendedSVBlocking.
  Fixpoint blocking_onlyb st : bool :=
    match st with
    | SSkip => true | SAssign nba _ _ => negb nba
    | SSeq xs => forallb blocking_onlyb xs
    | SIf _ yes no => blocking_onlyb yes && blocking_onlyb no
    | SCase _ arms => forallb (fun arm => blocking_onlyb (snd arm)) arms
    end.
  Lemma selected_blocking s v arms default :
    forallb (fun arm => blocking_onlyb (snd arm)) arms = true ->
    blocking_onlyb default = true ->
    blocking_onlyb (select_case_stmt s v arms default) = true.
  Proof.
    induction arms as [|[key body] rest IH] in default |- *; cbn; auto.
    intros H Hd. apply andb_true_iff in H as [Hb Hr].
    destruct key as [key|]; [destruct (Z.eqb v (eval_expr s key))|]; auto.
  Qed.
  Theorem blocking_pending_unchanged fuel st es :
    blocking_onlyb st = true -> pending_nba (exec_stmt fuel st es) = pending_nba es.
  Proof.
    induction fuel as [|fuel IH] in st, es |- *; [reflexivity|].
    destruct st as [|nba rhs lhs|xs|guard yes no|scrutinee arms]; cbn; intros H.
    - reflexivity.
    - destruct nba; [discriminate|reflexivity].
    - induction xs as [|st xs IHr] in es, H |- *; cbn in *; [reflexivity|].
      apply andb_true_iff in H as [Hst Hxs]. rewrite IHr by exact Hxs.
      apply IH. exact Hst.
    - apply andb_true_iff in H as [Hy Hn].
      destruct (Z.eqb (eval_expr (blocking_state es) guard) 0); apply IH; assumption.
    - apply IH. apply selected_blocking; [exact H|reflexivity].
  Qed.
  Corollary blocking_run_process p proc s :
    blocking_onlyb (process_body proc) = true ->
    run_process p s proc = blocking_state (exec_stmt (statement_fuel p) (process_body proc)
      {| blocking_state := s; pending_nba := []; emitted_updates := [] |}).
  Proof.
    intros H. unfold run_process. rewrite blocking_pending_unchanged by exact H.
    reflexivity.
  Qed.
End ExtendedSVBlocking.
