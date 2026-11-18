From Coq Require Import List ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVAutoAdapterSemantics.
Import ExtendedSV ExtendedSVAutoAdapterSemantics ListNotations.
Module ExtendedSVAutoAdapterPlan.

Inductive NbPlan :=
| NEmpty
| NAssign (rhs : Expr) (lhs : LValue)
| NSeq (plans : list NbPlan)
| NIf (guard : Expr) (yes no : NbPlan)
| NCase (scrutinee : Expr) (arms : list (option Expr * NbPlan)).

Fixpoint traverse {A B} (f : A -> option B) (xs : list A) : option (list B) :=
 match xs with
 | [] => Some []
 | x :: rest => match f x, traverse f rest with
   | Some y, Some ys => Some (y :: ys) | _, _ => None end
 end.

Fixpoint compile_nb (fuel : nat) (st : Stmt) : option NbPlan :=
 match fuel with
 | O => None
 | S f => match st with
   | SSkip => Some NEmpty
   | SAssign true rhs lhs => Some (NAssign rhs lhs)
   | SAssign false _ _ => None
   | SSeq sts => option_map NSeq (traverse (compile_nb f) sts)
   | SIf g yes no => match compile_nb f yes, compile_nb f no with
     | Some y, Some n => Some (NIf g y n) | _, _ => None end
   | SCase e arms => match f with O => None | S _ => option_map (NCase e)
       (traverse (fun arm => option_map (fun p => (fst arm,p))
         (compile_nb f (snd arm))) arms) end
   end
 end.

Fixpoint eval_plan (s : State) (plan : NbPlan) : list Update :=
 match plan with
 | NEmpty => []
 | NAssign rhs lhs => [resolve_update s lhs (eval_expr s rhs)]
 | NSeq plans => flat_map (eval_plan s) plans
 | NIf g yes no => eval_plan s
     (if Z.eqb (eval_expr s g) 0 then no else yes)
 | NCase e arms =>
   let fix select xs default :=
     match xs with
     | [] => default
     | (None,p) :: rest => select rest (eval_plan s p)
     | (Some key,p) :: rest =>
       if Z.eqb (eval_expr s e) (eval_expr s key)
       then eval_plan s p else select rest default
     end in select arms []
 end.

Theorem compile_nb_sound fuel : forall st plan s,
 compile_nb fuel st = Some plan ->
 nb_updates fuel s st = Some (eval_plan s plan).
Proof.
 induction fuel as [|f IH]; intros st plan s H; [discriminate|].
 destruct st as [|nba rhs lhs|sts|g yes no|e arms]; cbn in H |- *.
 - inversion H; reflexivity.
 - destruct nba; [inversion H; reflexivity|discriminate].
 - destruct (traverse (compile_nb f) sts) as [plans|] eqn:HT;
     [|discriminate]. inversion H; subst plan; cbn.
   induction sts as [|st rest IHr] in plans,HT |- *; cbn in HT |- *.
   + inversion HT; reflexivity.
   + destruct (compile_nb f st) as [p|] eqn:HP; [|discriminate].
     destruct (traverse (compile_nb f) rest) as [ps|] eqn:HS;
       [|discriminate]. inversion HT; subst plans; cbn.
     rewrite (IH st p s HP), (IHr ps eq_refl). reflexivity.
 - destruct (compile_nb f yes) as [y|] eqn:HY; [|discriminate].
   destruct (compile_nb f no) as [n|] eqn:HN; [|discriminate].
   inversion H; subst plan; cbn.
   destruct (Z.eqb (eval_expr s g) 0); apply IH; assumption.
 - destruct f as [|f']; [discriminate|].
   destruct (traverse _ arms) as [ps|] eqn:HT; [|discriminate].
   inversion H; subst plan; cbn.
   assert (HC : forall default dp,
      nb_updates (S f') s default = Some dp ->
      nb_updates (S f') s (select_case_stmt s (eval_expr s e) arms default) =
      Some ((fix select xs d :=
        match xs with
        | [] => d
        | (None,p) :: rest => select rest (eval_plan s p)
        | (Some key,p) :: rest =>
          if Z.eqb (eval_expr s e) (eval_expr s key)
          then eval_plan s p else select rest d
        end) ps dp)).
   { induction arms as [|[key body] rest IHr] in ps,HT |- *;
       intros default dp HD; cbn [traverse fst snd] in HT;
       cbn [select_case_stmt].
     - inversion HT; exact HD.
     - destruct (compile_nb (S f') body) as [p|] eqn:HP; [|discriminate].
       cbn [option_map] in HT.
       destruct (traverse _ rest) as [qs|] eqn:HQ; [|discriminate].
       inversion HT; subst ps; cbn.
       destruct key as [key|]; cbn.
       + destruct (Z.eqb (eval_expr s e) (eval_expr s key)).
         * apply IH; exact HP.
         * apply IHr; [reflexivity|exact HD].
       + apply IHr; [reflexivity|]. apply IH; exact HP.
   }
   apply HC. reflexivity.
Qed.

Theorem checked_process_plan p proc plan :
 compile_nb (statement_fuel p) (process_body proc) = Some plan ->
 forall s, process_updates p s proc = eval_plan s plan.
Proof.
 intros H s. apply checked_process_updates.
 now apply compile_nb_sound.
Qed.

Theorem checked_run_plan p proc plan :
 compile_nb (statement_fuel p) (process_body proc) = Some plan ->
 forall s, run_process p s proc = apply_nba s (eval_plan s plan).
Proof.
 intros H s. apply checked_run_process. now apply compile_nb_sound.
Qed.

Theorem checked_plan_projection p proc plan :
 compile_nb (statement_fuel p) (process_body proc) = Some plan ->
 forall s root, read_signal (run_process p s proc) root =
 ExtendedSVRootProjection.ExtendedSVRootProjection.apply_updates_root_value
   root (read_signal s root) (eval_plan s plan).
Proof.
 intros H s root. apply checked_process_projection. now apply compile_nb_sound.
Qed.

Print Assumptions compile_nb_sound.
Print Assumptions checked_process_plan.
Print Assumptions checked_run_plan.
Print Assumptions checked_plan_projection.
End ExtendedSVAutoAdapterPlan.
