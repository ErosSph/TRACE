(** Cross-state substitution for blocking evaluation. No CPU invariant assumed. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVProjectionConnection
 Lang.ExtendedSVExprAgreement Lang.ExtendedSVAssignment Lang.ExtendedSVWordInvariant.
Import ExtendedSV ExtendedSVProjectionConnection ExtendedSVExprAgreement
 ExtendedSVAssignment ExtendedSVWordInvariant ListNotations.
Module ExtendedSVSequentialSubstitution.

Definition EnvironmentRelated (sigma:nat->signal->option Expr) seed live :=
 forall w x, norm w (read_signal live x) =
 match sigma w x with
 | Some rhs => norm w (eval_expr seed rhs)
 | None => norm w (read_signal seed x)
 end.

Theorem sequential_substitute_sound sigma e seed live :
 EnvironmentRelated sigma seed live ->
 eval_expr seed (substitute sigma e) = eval_expr live e.
Proof.
 intros HC; induction e; cbn [substitute eval_expr].
 - reflexivity.
 - specialize (HC width id). destruct (sigma width id);
   cbn [eval_expr]; symmetry; exact HC.
 - now rewrite IHe1,IHe2.
 - now rewrite substitute_width,IHe1,IHe2.
 - now rewrite substitute_width,IHe.
 - now rewrite substitute_width,IHe.
 - now rewrite IHe.
 - now rewrite !substitute_width,IHe1,IHe2.
 - now rewrite IHe1,IHe2,IHe3.
Qed.

Lemma empty_environment s : EnvironmentRelated (fun _ _=>None) s s.
Proof. intros w x; reflexivity. Qed.

Theorem sequential_substitute_inputs sigma e seed live :
 (forall w x, In (w,x) (expr_inputs e) ->
 norm w (read_signal live x) =
 match sigma w x with Some rhs=>norm w(eval_expr seed rhs)
 | None=>norm w(read_signal seed x) end) ->
 eval_expr seed(substitute sigma e)=eval_expr live e.
Proof.
 induction e; cbn [expr_inputs substitute eval_expr]; intro HC.
 - reflexivity.
 - specialize(HC width id (or_introl eq_refl)).
   destruct(sigma width id);cbn[eval_expr];symmetry;exact HC.
 - rewrite IHe1,IHe2;try reflexivity;intros w x HI;apply HC;
   apply in_or_app;auto.
 - rewrite substitute_width,IHe1,IHe2;try reflexivity;intros w x HI;
   apply HC;apply in_or_app;auto.
 - rewrite substitute_width,IHe;auto.
 - rewrite substitute_width,IHe;auto.
 - rewrite IHe;auto.
 - rewrite !substitute_width,IHe1,IHe2;try reflexivity;intros w x HI;
   apply HC;apply in_or_app;auto.
 - rewrite IHe1,IHe2,IHe3;try reflexivity;intros w x HI;apply HC;
   repeat (apply in_or_app; first [left;exact HI|right]);exact HI.
Qed.

Definition assign_substitution width root rhs : nat->signal->option Expr :=
 fun _ x=>if Nat.eqb x root then Some(EExtend width false rhs) else None.

Theorem read_after_blocking_assignment s width root rhs e :
 (forall w x, In(w,x)(expr_inputs e)->x=root->w=width) ->
 eval_expr s(substitute(assign_substitution width root rhs)e)=
 eval_expr (apply_update s(resolve_update s(LVar width root)(eval_expr s rhs))) e.
Proof.
 intro HW;apply sequential_substitute_inputs;intros w x HI.
 unfold assign_substitution,apply_update,resolve_update;cbn[resolve_lvalue].
 destruct(Nat.eqb x root)eqn:HX.
 - apply Nat.eqb_eq in HX;subst x;specialize(HW w root HI eq_refl);subst w.
   rewrite read_signal_write_same,norm_full_low_write.
   cbn[eval_expr update_width update_value]. now rewrite norm_idempotent.
 - apply Nat.eqb_neq in HX;cbn[update_signal];
   rewrite read_signal_write_other by congruence;reflexivity.
Qed.

End ExtendedSVSequentialSubstitution.
Print Assumptions ExtendedSVSequentialSubstitution.sequential_substitute_sound.
Print Assumptions ExtendedSVSequentialSubstitution.read_after_blocking_assignment.
