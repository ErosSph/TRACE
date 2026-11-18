(** Structural certificate for the five-statement NBA shape of Dark's core
    process.  Fuel remains symbolic here: no CPU or value computation. *)
From Coq Require Import ZArith List.
Require Import Lang.ExtendedSV Lang.ExtendedSVNBAProjection.
Import ExtendedSV ExtendedSVNBAProjection ListNotations.
Module DarkRISCVResetSequence.
Lemma nba_sequence_unroll fuel xs s root old :
 nba_root (S fuel) (SSeq xs) s root old =
 fold_left (fun v st => nba_root fuel st s root v) xs old.
Proof. reflexivity. Qed.
Theorem five_statements_one_writer fuel s root old st0 st1 st2 st3 st4 :
 ~ In root (stmt_writers st0) -> ~ In root (stmt_writers st2) ->
 ~ In root (stmt_writers st3) -> ~ In root (stmt_writers st4) ->
 nba_root (S (S fuel)) (SSeq [SSeq [st0;st1;st2;st3;st4]]) s root old =
 nba_root fuel st1 s root old.
Proof.
 intros H0 H2 H3 H4.
 rewrite nba_sequence_unroll. cbn [fold_left].
 rewrite nba_sequence_unroll. cbn [fold_left].
 rewrite (nba_root_no_writer fuel st4 s root _ H4).
 rewrite (nba_root_no_writer fuel st3 s root _ H3).
 rewrite (nba_root_no_writer fuel st2 s root _ H2).
 rewrite (nba_root_no_writer fuel st0 s root old H0). reflexivity.
Qed.
Print Assumptions five_statements_one_writer.
Theorem five_statements_fourth_writer fuel s root old st0 st1 st2 st3 st4 :
 ~ In root (stmt_writers st0) -> ~ In root (stmt_writers st1) ->
 ~ In root (stmt_writers st2) -> ~ In root (stmt_writers st4) ->
 nba_root (S (S fuel)) (SSeq [SSeq [st0;st1;st2;st3;st4]]) s root old =
 nba_root fuel st3 s root old.
Proof.
 intros H0 H1 H2 H4.
 rewrite nba_sequence_unroll. cbn [fold_left].
 rewrite nba_sequence_unroll. cbn [fold_left].
 rewrite (nba_root_no_writer fuel st4 s root _ H4).
 rewrite (nba_root_no_writer fuel st2 s root _ H2).
 rewrite (nba_root_no_writer fuel st1 s root _ H1).
 rewrite (nba_root_no_writer fuel st0 s root old H0). reflexivity.
Qed.
Lemma nba_fold_unwritten fuel xs s root old :
 (forall st, In st xs -> ~ In root (stmt_writers st)) ->
 fold_left (fun v st => nba_root fuel st s root v) xs old = old.
Proof.
 intros Hall. induction xs as [|st xs IH] in old,Hall |- *; cbn [fold_left]; [reflexivity|].
 rewrite nba_root_no_writer by (apply Hall; now left).
 apply IH. intros st' Hin. apply Hall. now right.
Qed.
Theorem nba_sequence_focus fuel before st after s root old :
 (forall x, In x before -> ~ In root (stmt_writers x)) ->
 (forall x, In x after -> ~ In root (stmt_writers x)) ->
 nba_root (S fuel) (SSeq (before ++ st :: after)) s root old = nba_root fuel st s root old.
Proof.
 intros Hb Ha. rewrite nba_sequence_unroll,fold_left_app.
 rewrite (nba_fold_unwritten fuel before s root old Hb).
 cbn [fold_left]. apply nba_fold_unwritten. exact Ha.
Qed.
End DarkRISCVResetSequence.
