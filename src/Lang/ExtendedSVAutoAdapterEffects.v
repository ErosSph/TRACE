(** State-threaded effect plans, including blocking temporaries and NBA.
    Unlike NBA-only plans, guards and RHS expressions observe preceding
    blocking writes. Pending updates retain execution-time resolved values. *)
From Coq Require Import List ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVAutoAdapterPlan.
Import ExtendedSV ExtendedSVAutoAdapterPlan ListNotations.
Module ExtendedSVAutoAdapterEffects.

Inductive EffectPlan :=
| FEmpty
| FAssign (nba : bool) (rhs : Expr) (lhs : LValue)
| FSeq (plans : list EffectPlan)
| FIf (guard : Expr) (yes no : EffectPlan)
| FCase (scrutinee : Expr) (arms : list (option Expr * EffectPlan)).

Fixpoint compile_effect (fuel : nat) (st : Stmt) : option EffectPlan :=
 match fuel with
 | O => None
 | S f => match st with
   | SSkip => Some FEmpty
   | SAssign nba rhs lhs => Some (FAssign nba rhs lhs)
   | SSeq sts => option_map FSeq (traverse (compile_effect f) sts)
   | SIf g yes no => match compile_effect f yes, compile_effect f no with
     | Some y, Some n => Some (FIf g y n) | _, _ => None end
   | SCase e arms => option_map (FCase e)
       (traverse (fun arm => option_map (fun p => (fst arm,p))
         (compile_effect f (snd arm))) arms)
   end
 end.

Fixpoint eval_effect (plan : EffectPlan) (es : ExecState) : ExecState :=
 match plan with
 | FEmpty => es
 | FAssign nba rhs lhs =>
   let u := resolve_update (blocking_state es) lhs
     (eval_expr (blocking_state es) rhs) in
   if nba then
     {| blocking_state := blocking_state es;
        pending_nba := pending_nba es ++ [u];
        emitted_updates := emitted_updates es ++ [u] |}
   else
     {| blocking_state := apply_update (blocking_state es) u;
        pending_nba := pending_nba es;
        emitted_updates := emitted_updates es ++ [u] |}
 | FSeq plans => fold_left (fun state p => eval_effect p state) plans es
 | FIf g yes no => eval_effect
     (if Z.eqb (eval_expr (blocking_state es) g) 0 then no else yes) es
 | FCase e arms =>
   let fix select xs default :=
     match xs with
     | [] => default
     | (None,p) :: rest => select rest (eval_effect p es)
     | (Some key,p) :: rest =>
       if Z.eqb (eval_expr (blocking_state es) e)
           (eval_expr (blocking_state es) key)
       then eval_effect p es else select rest default
     end in select arms es
 end.

Theorem compile_effect_sound fuel : forall st plan es,
 compile_effect fuel st = Some plan ->
 exec_stmt fuel st es = eval_effect plan es.
Proof.
 induction fuel as [|f IH]; intros st plan es H; [discriminate|].
 destruct st as [|nba rhs lhs|sts|g yes no|e arms]; cbn in H |- *.
 - inversion H; reflexivity.
 - inversion H; reflexivity.
 - destruct (traverse (compile_effect f) sts) as [plans|] eqn:HT;
     [|discriminate]. inversion H; subst plan; cbn.
   induction sts as [|st rest IHr] in plans,HT,es |- *;
     cbn in HT |- *.
   + inversion HT; reflexivity.
   + destruct (compile_effect f st) as [p|] eqn:HP; [|discriminate].
     destruct (traverse (compile_effect f) rest) as [ps|] eqn:HS;
       [|discriminate]. inversion HT; subst plans; cbn.
     rewrite (IH st p es HP). apply IHr. reflexivity.
 - destruct (compile_effect f yes) as [y|] eqn:HY; [|discriminate].
   destruct (compile_effect f no) as [n|] eqn:HN; [|discriminate].
   inversion H; subst plan; cbn.
   destruct (Z.eqb (eval_expr (blocking_state es) g) 0); apply IH; assumption.
 - destruct (traverse _ arms) as [ps|] eqn:HT; [|discriminate].
   inversion H; subst plan; cbn.
   assert (HC : forall default result,
      exec_stmt f default es = result ->
      exec_stmt f (select_case_stmt (blocking_state es)
        (eval_expr (blocking_state es) e) arms default) es =
      (fix select xs d :=
        match xs with
        | [] => d
        | (None,p) :: rest => select rest (eval_effect p es)
        | (Some key,p) :: rest =>
          if Z.eqb (eval_expr (blocking_state es) e)
              (eval_expr (blocking_state es) key)
          then eval_effect p es else select rest d
        end) ps result).
   { induction arms as [|[key body] rest IHr] in ps,HT |- *;
       intros default result HD; cbn [traverse fst snd] in HT;
       cbn [select_case_stmt].
     - inversion HT; exact HD.
     - destruct (compile_effect f body) as [p|] eqn:HP; [|discriminate].
       cbn [option_map] in HT.
       destruct (traverse _ rest) as [qs|] eqn:HQ; [|discriminate].
       inversion HT; subst ps; cbn.
       destruct key as [key|]; cbn.
       + destruct (Z.eqb (eval_expr (blocking_state es) e)
           (eval_expr (blocking_state es) key)).
         * apply IH; exact HP.
         * apply IHr; [reflexivity|exact HD].
       + apply IHr; [reflexivity|]. apply IH; exact HP.
   }
   apply HC. destruct f; reflexivity.
Qed.

Definition initial_exec (s : State) : ExecState :=
 {| blocking_state := s; pending_nba := []; emitted_updates := [] |}.

Theorem checked_effect_updates p proc plan :
 compile_effect (statement_fuel p) (process_body proc) = Some plan ->
 forall s, process_updates p s proc =
 emitted_updates (eval_effect plan (initial_exec s)).
Proof.
 intros H s. unfold process_updates, initial_exec.
 now rewrite (compile_effect_sound _ _ _ _ H).
Qed.

Theorem checked_effect_run p proc plan :
 compile_effect (statement_fuel p) (process_body proc) = Some plan ->
 forall s, run_process p s proc =
 let result := eval_effect plan (initial_exec s) in
 apply_nba (blocking_state result) (pending_nba result).
Proof.
 intros H s. unfold run_process, initial_exec.
 now rewrite (compile_effect_sound _ _ _ _ H).
Qed.

Print Assumptions compile_effect_sound.
Print Assumptions checked_effect_updates.
Print Assumptions checked_effect_run.

(** Executable regression: a blocking temporary is visible to the following
    NBA, whose snapshot remains queued rather than updating blocking state. *)
Example mixed_assignment_snapshot :
 eval_effect
   (FSeq [FAssign false (EConst 8 5) (LVar 8 0);
          FAssign true (EVar 8 0) (LVar 8 1)])
   (initial_exec [3%Z; 0%Z]) =
 {| blocking_state := [5%Z; 0%Z];
    pending_nba := [{| update_signal := 1; update_offset := 0;
      update_width := 8; update_value := 5 |}];
    emitted_updates :=
      [{| update_signal := 0; update_offset := 0;
          update_width := 8; update_value := 5 |};
       {| update_signal := 1; update_offset := 0;
          update_width := 8; update_value := 5 |}] |}.
Proof. vm_compute. reflexivity. Qed.

Example mixed_assignment_static_compile :
 compile_effect 3
   (SSeq [SAssign false (EConst 8 5) (LVar 8 0);
          SAssign true (EVar 8 0) (LVar 8 1)]) =
 Some (FSeq [FAssign false (EConst 8 5) (LVar 8 0);
             FAssign true (EVar 8 0) (LVar 8 1)]).
Proof. reflexivity. Qed.

Example ordered_case_first_match :
 blocking_state (eval_effect
   (FCase (EConst 8 7)
     [(None, FAssign false (EConst 8 1) (LVar 8 0));
      (Some (EConst 8 7), FAssign false (EConst 8 2) (LVar 8 0));
      (None, FAssign false (EConst 8 3) (LVar 8 0))])
   (initial_exec [0%Z])) = [2%Z].
Proof. vm_compute. reflexivity. Qed.
End ExtendedSVAutoAdapterEffects.
