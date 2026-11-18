(** A checked, design-independent adapter compiler for nonblocking statement
    trees. Guards and RHS expressions are evaluated in the incoming state,
    as justified below, not assumed by the generated adapter. *)
From Coq Require Import List ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection.
Import ExtendedSV ExtendedSVRootProjection ListNotations.
Module ExtendedSVAutoAdapterSemantics.

Fixpoint nb_updates (fuel : nat) (s : State) (st : Stmt)
    : option (list Update) :=
 match fuel with
 | O => None
 | S fuel' =>
   match st with
   | SSkip => Some []
   | SAssign true rhs lhs => Some [resolve_update s lhs (eval_expr s rhs)]
   | SAssign false _ _ => None
   | SSeq sts =>
     let fix collect xs :=
       match xs with
       | [] => Some []
       | x :: rest =>
         match nb_updates fuel' s x, collect rest with
         | Some us, Some vs => Some (us ++ vs)
         | _, _ => None
         end
       end in collect sts
   | SIf g yes no => nb_updates fuel' s
       (if Z.eqb (eval_expr s g) 0 then no else yes)
   | SCase e arms => nb_updates fuel' s
       (select_case_stmt s (eval_expr s e) arms SSkip)
   end
 end.

Definition append_exec (es : ExecState) (us : list Update) : ExecState :=
 {| blocking_state := blocking_state es;
    pending_nba := pending_nba es ++ us;
    emitted_updates := emitted_updates es ++ us |}.

Lemma append_exec_nil es : append_exec es [] = es.
Proof. destruct es; unfold append_exec; cbn; now rewrite !app_nil_r. Qed.
Lemma append_exec_app es us vs :
 append_exec (append_exec es us) vs = append_exec es (us ++ vs).
Proof. unfold append_exec; cbn; now rewrite !app_assoc. Qed.

Theorem nb_updates_sound fuel : forall st es us,
 nb_updates fuel (blocking_state es) st = Some us ->
 exec_stmt fuel st es = append_exec es us.
Proof.
 induction fuel as [|fuel IH]; intros st es us H; [discriminate|].
 destruct st as [|nba rhs lhs|sts|g yes no|e arms]; cbn in H |- *.
 - inversion H; subst. symmetry; apply append_exec_nil.
 - destruct nba; [inversion H; reflexivity|discriminate].
 - induction sts as [|st rest IHr] in es,us,H |- *; cbn in H |- *.
   + inversion H; subst. symmetry; apply append_exec_nil.
   + destruct (nb_updates fuel (blocking_state es) st) as [xs|] eqn:HX;
       [|discriminate].
     destruct ((fix collect (xs : list Stmt) : option (list Update) :=
       match xs with
       | [] => Some []
       | x :: rest => match nb_updates fuel (blocking_state es) x, collect rest with
         | Some a, Some b => Some (a ++ b) | _, _ => None end
       end) rest) as [ys|] eqn:HY; [|discriminate].
     inversion H; subst us. rewrite (IH st es xs HX).
     rewrite (IHr (append_exec es xs) ys HY).
     apply append_exec_app.
 - apply IH; exact H.
 - apply IH; exact H.
Qed.

Theorem checked_process_updates p proc s us :
 nb_updates (statement_fuel p) s (process_body proc) = Some us ->
 process_updates p s proc = us.
Proof.
 intros H. unfold process_updates.
 rewrite (nb_updates_sound _ _
   {| blocking_state := s; pending_nba := []; emitted_updates := [] |} _ H).
 reflexivity.
Qed.

Theorem checked_run_process p proc s us :
 nb_updates (statement_fuel p) s (process_body proc) = Some us ->
 run_process p s proc = apply_nba s us.
Proof.
 intros H. unfold run_process.
 rewrite (nb_updates_sound _ _
   {| blocking_state := s; pending_nba := []; emitted_updates := [] |} _ H).
 reflexivity.
Qed.

Theorem checked_process_frame p proc s us root :
 nb_updates (statement_fuel p) s (process_body proc) = Some us ->
 updates_avoid root us ->
 read_signal (run_process p s proc) root = read_signal s root.
Proof. intros H HA; rewrite (checked_run_process _ _ _ _ H).
 now apply apply_nba_preserves_root. Qed.

Lemma read_signal_apply_nba us s root :
 read_signal (apply_nba s us) root =
 apply_updates_root_value root (read_signal s root) us.
Proof.
 induction us as [|u us IH] in s |- *; cbn; [reflexivity|].
 rewrite IH, read_signal_apply_update. reflexivity.
Qed.

Theorem checked_process_projection p proc s us root :
 nb_updates (statement_fuel p) s (process_body proc) = Some us ->
 read_signal (run_process p s proc) root =
 apply_updates_root_value root (read_signal s root) us.
Proof.
 intros H; rewrite (checked_run_process _ _ _ _ H).
 apply read_signal_apply_nba.
Qed.

(** A reusable hold/flush/load rule. All identifiers, widths, guards and
    expressions are parameters. The AST equation is the generated evidence;
    the theorem proves the update list, not merely a writer-set property. *)
Theorem checked_hold_flush_load p proc s flush enable value width root fuel :
 statement_fuel p = S (S (S fuel)) ->
 process_body proc =
   SIf flush (SAssign true (EConst width 0) (LVar width root))
     (SIf enable (SAssign true value (LVar width root)) SSkip) ->
 process_updates p s proc =
   if Z.eqb (eval_expr s flush) 0 then
     if Z.eqb (eval_expr s enable) 0 then []
     else [resolve_update s (LVar width root) (eval_expr s value)]
   else [resolve_update s (LVar width root) (eval_expr s (EConst width 0))].
Proof.
 intros HF HB. apply checked_process_updates.
 rewrite HF, HB. cbn [nb_updates].
 destruct (Z.eqb (eval_expr s flush) 0); [|reflexivity].
 destruct (Z.eqb (eval_expr s enable) 0); reflexivity.
Qed.

Print Assumptions nb_updates_sound.
Print Assumptions checked_process_updates.
Print Assumptions checked_run_process.
Print Assumptions checked_process_frame.
Print Assumptions checked_process_projection.
Print Assumptions checked_hold_flush_load.
End ExtendedSVAutoAdapterSemantics.
