(** Compile whole-root NBA effects into a sampled expression. Seed denotes
    the previous projected value; it is NOT an updated blocking state. *)
From Coq Require Import List ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
 Lang.ExtendedSVAssignment Lang.ExtendedSVWordInvariant Lang.ExtendedSVAutoAdapterPlan
 Lang.ExtendedSVAutoAdapterPhase
 Lang.ExtendedSVPlanRootSlice Lang.ExtendedSVPlanEmpty.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice
 ExtendedSVAssignment ExtendedSVWordInvariant ExtendedSVAutoAdapterPlan ExtendedSVAutoAdapterPhase
 ExtendedSVPlanRootSlice ExtendedSVPlanEmpty.
Module ExtendedSVScalarExpression.

Fixpoint option_fold {A B} (f : A -> B -> option B) (xs : list A) (seed : B) : option B :=
 match xs with
 | [] => Some seed
 | x :: rest => match f x seed with Some next => option_fold f rest next | None => None end
 end.

Fixpoint case_expression width scrutinee (arms : list (option Expr * Expr)) seed : Expr :=
 match arms with
 | [] => seed
 | (None,body)::rest => case_expression width scrutinee rest body
 | (Some key,body)::rest => ECond width (EBinary 1 BEq scrutinee key)
     body (case_expression width scrutinee rest seed)
 end.

Fixpoint compile_scalar fuel root width plan seed : option Expr :=
 match fuel with
 | O => None
 | S f => if plan_emptyb (S f) plan then Some seed else
   match plan with
   | NEmpty => Some seed
   | NAssign rhs lhs => if Nat.eqb (lvalue_root lhs) root then
       match lhs with
       | LVar w _ => if Nat.eqb w width then Some rhs else None
       | _ => None
       end else Some seed
   | NSeq plans => option_fold (compile_scalar f root width) plans seed
   | NIf guard yes no => match compile_scalar f root width yes seed,
       compile_scalar f root width no seed with
       | Some y,Some n => Some (ECond width guard y n) | _,_ => None end
   | NCase scrutinee arms => option_map (fun es => case_expression width scrutinee es seed)
       (traverse (fun arm => option_map (fun body => (fst arm,body))
         (compile_scalar f root width (snd arm) seed)) arms)
   end
 end.

Theorem compile_scalar_sound fuel : forall root width plan seed result s old,
 compile_scalar fuel root width plan seed = Some result ->
 norm width old = norm width (eval_expr s seed) ->
 norm width (apply_updates_root_value root old (eval_plan s plan)) =
 norm width (eval_expr s result).
Proof.
 induction fuel as [|f IH]; intros root width plan seed result s old HC HV;
   [discriminate|].
 cbn [compile_scalar] in HC.
 destruct (plan_emptyb (S f) plan) eqn:HE.
 { inversion HC;subst result. rewrite (empty_plan_sound (S f) plan s HE). exact HV. }
 destruct plan as [|rhs lhs|plans|guard yes no|scrutinee arms].
 - inversion HC;subst;exact HV.
 - destruct (Nat.eqb (lvalue_root lhs) root) eqn:HR.
   + destruct lhs as [w id|]; [|discriminate].
     destruct (Nat.eqb w width) eqn:HW; [|discriminate].
     apply Nat.eqb_eq in HW. subst w.
     apply Nat.eqb_eq in HR. cbn [lvalue_root] in HR. subst id.
     inversion HC;subst result.
     cbn [eval_plan apply_updates_root_value].
     unfold apply_update_root_value,resolve_update.
     cbn [resolve_lvalue update_signal update_offset update_width update_value].
     rewrite Nat.eqb_refl,norm_full_low_write,norm_idempotent. reflexivity.
   + inversion HC;subst result.
     cbn [eval_plan apply_updates_root_value]. unfold apply_update_root_value.
     rewrite resolve_update_root,HR. exact HV.
 - cbn [eval_plan]. induction plans as [|plan rest IHr] in seed,old,HC,HV |- *.
   + inversion HC;subst result. exact HV.
   + cbn [option_fold] in HC.
     destruct (compile_scalar f root width plan seed) as [next|] eqn:HN;
       [|discriminate].
     cbn [flat_map]. rewrite apply_root_app.
     apply (IHr next (apply_updates_root_value root old (eval_plan s plan)) HC).
     exact (IH root width plan seed next s old HN HV).
 - destruct (compile_scalar f root width yes seed) as [y|] eqn:HY; [|discriminate].
   destruct (compile_scalar f root width no seed) as [n|] eqn:HN; [|discriminate].
   inversion HC;subst result. cbn [eval_plan eval_expr].
   rewrite norm_idempotent.
   destruct (Z.eqb (eval_expr s guard) 0); eapply IH; eassumption.
 - destruct (traverse _ arms) as [es|] eqn:HT; [|discriminate].
   inversion HC;subst result.
   change (norm width (apply_updates_root_value root old
     (case_updates s (eval_expr s scrutinee) arms [])) =
     norm width (eval_expr s (case_expression width scrutinee es seed))).
   assert (Hcases : forall default_updates default_expr,
     norm width (apply_updates_root_value root old default_updates) =
       norm width (eval_expr s default_expr) ->
     norm width (apply_updates_root_value root old
       (case_updates s (eval_expr s scrutinee) arms default_updates)) =
     norm width (eval_expr s (case_expression width scrutinee es default_expr))).
   { induction arms as [|[key body] rest IHr] in es,HT |- *;
       intros default_updates default_expr HD;
       cbn [traverse fst snd] in HT.
     - inversion HT;subst es;exact HD.
     - destruct (compile_scalar f root width body seed) as [b|] eqn:HB;
         [|discriminate]. cbn [option_map] in HT.
       destruct (traverse _ rest) as [bs|] eqn:HR; [|discriminate].
       inversion HT;subst es. cbn [case_updates case_expression].
       destruct key as [key|]; cbn [fst snd].
       + cbn [eval_expr]. rewrite norm_one_boolz,norm_idempotent.
         destruct (Z.eqb (eval_expr s scrutinee) (eval_expr s key)) eqn:HK;
           cbn [boolz Z.eqb].
         * exact (IH root width body seed b s old HB HV).
         * exact (IHr bs eq_refl default_updates default_expr HD).
       + apply (IHr bs eq_refl (eval_plan s body) b).
         exact (IH root width body seed b s old HB HV).
   }
   apply Hcases. exact HV.
Qed.

Print Assumptions compile_scalar_sound.

Corollary checked_scalar_process p proc plan root width fuel expression :
 compile_nb (statement_fuel p) (process_body proc) = Some plan ->
 compile_scalar fuel root width plan (EVar width root) = Some expression ->
 forall s, norm width (read_signal (run_process p s proc) root) =
 norm width (eval_expr s expression).
Proof.
 intros HC HE s. rewrite (checked_plan_projection p proc plan HC s root).
 eapply compile_scalar_sound; [exact HE|].
 cbn [eval_expr]. now rewrite norm_idempotent.
Qed.

Lemma sampled_root_preserved p ev pre root :
 comb_root_unwrittenb p root = true -> changed_signal ev <> root ->
 read_signal (phase_driven_state p ev pre) root = read_signal pre root.
Proof.
 intros HC HE. unfold phase_driven_state.
 rewrite lfp_candidate_preserves_unwritten_root by exact HC.
 now rewrite read_signal_write_other by exact HE.
Qed.

Theorem checked_scalar_phase p root proc plan width fuel expression :
 PlanRootCertificate p root [(proc,plan)] ->
 compile_scalar fuel root width plan (EVar width root) = Some expression ->
 forall ev pre, changed_signal ev <> root ->
 norm width (read_signal (PhaseSemantics p ev pre) root) =
 if process_matches_states pre (phase_driven_state p ev pre) proc
 then norm width (eval_expr (phase_driven_state p ev pre) expression)
 else norm width (read_signal pre root).
Proof.
 intros HC HE ev pre Hdriver.
 rewrite (planned_phase_root p root [(proc,plan)] HC ev pre Hdriver).
 cbn [plan_transition_updates flat_map fst snd].
 destruct (process_matches_states pre (phase_driven_state p ev pre) proc).
 - rewrite app_nil_r. eapply compile_scalar_sound; [exact HE|].
   cbn [eval_expr]. rewrite norm_idempotent.
   rewrite sampled_root_preserved by (exact (plan_root_comb_unwritten _ _ _ HC)||exact Hdriver).
   reflexivity.
 - reflexivity.
Qed.

Print Assumptions checked_scalar_process.
Print Assumptions sampled_root_preserved.
Print Assumptions checked_scalar_phase.

Corollary checked_sliced_scalar_process p proc plan root width slice_fuel expr_fuel expression :
 compile_nb (statement_fuel p) (process_body proc) = Some plan ->
 compile_scalar expr_fuel root width (slice_plan slice_fuel root plan)
   (EVar width root) = Some expression ->
 forall s, norm width (read_signal (run_process p s proc) root) =
 norm width (eval_expr s expression).
Proof.
 intros HC HE s. rewrite (checked_plan_projection p proc plan HC s root).
 rewrite <-(slice_plan_sound slice_fuel root plan s (read_signal s root)).
 eapply compile_scalar_sound; [exact HE|].
 cbn [eval_expr]. now rewrite norm_idempotent.
Qed.

Theorem checked_sliced_scalar_phase p root proc plan width slice_fuel expr_fuel expression :
 PlanRootCertificate p root [(proc,plan)] ->
 compile_scalar expr_fuel root width (slice_plan slice_fuel root plan)
   (EVar width root) = Some expression ->
 forall ev pre, changed_signal ev <> root ->
 norm width (read_signal (PhaseSemantics p ev pre) root) =
 if process_matches_states pre (phase_driven_state p ev pre) proc
 then norm width (eval_expr (phase_driven_state p ev pre) expression)
 else norm width (read_signal pre root).
Proof.
 intros HC HE ev pre Hdriver.
 rewrite (planned_phase_root p root [(proc,plan)] HC ev pre Hdriver).
 cbn [plan_transition_updates flat_map fst snd].
 destruct (process_matches_states pre (phase_driven_state p ev pre) proc).
 - rewrite app_nil_r.
   rewrite <-(slice_plan_sound slice_fuel root plan
     (phase_driven_state p ev pre) (read_signal pre root)).
   eapply compile_scalar_sound; [exact HE|].
   cbn [eval_expr]. rewrite norm_idempotent.
   rewrite sampled_root_preserved by (exact (plan_root_comb_unwritten _ _ _ HC)||exact Hdriver).
   reflexivity.
 - reflexivity.
Qed.
Print Assumptions checked_sliced_scalar_process.
Print Assumptions checked_sliced_scalar_phase.
End ExtendedSVScalarExpression.
