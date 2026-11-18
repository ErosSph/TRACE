(** Stronger constant evaluation of expression facts (template route, additive; 2026-11-03).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    [simp_f F e] rewrites every subexpression that [xeval2] decides into a constant and short-circuits [a & b] with a zero side at ALL
    depths (xeval2 only does it at the top of an [&] chain); [xeval3 F e := xeval2 F (simp_f F e)].  Used to check expression
    facts such as the controller stall conjunctions.  Sound for any state satisfying the facts. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVExpressionFold
 Lang.ExtendedSVCaseExpr Lang.ExtendedSVCaseBackO Lang.ExtendedSVSymExecOverlay Lang.ExtendedSVBackOverlay Lang.ExtendedSVBackward.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVExpressionFold ExtendedSVCaseExpr ExtendedSVCaseBackO
 ExtendedSVSymExecOverlay ExtendedSVBackOverlay ExtendedSVBackward.
Local Open Scope Z_scope.
Module ExtendedSVEval3.

Fixpoint simp_f (F:Facts) (e:Expr) : Expr :=
 match xeval2 F e with
 | Some z => EConst (expr_width e) z
 | None =>
   match e with
   | ESel w a b => ESel w (simp_f F a) (simp_f F b)
   | EConcat w a b => EConcat w (simp_f F a) (simp_f F b)
   | EReplicate w c a => EReplicate w c (simp_f F a)
   | EExtend w sg a => EExtend w sg (simp_f F a)
   | EUnary w op a => EUnary w op (simp_f F a)
   | EBinary w BAnd a b =>
       let a' := simp_f F a in let b' := simp_f F b in
       if zero_expressionb a' || zero_expressionb b' then EConst w 0 else EBinary w BAnd a' b'
   | EBinary w op a b => EBinary w op (simp_f F a) (simp_f F b)
   | ECond w g y n => ECond w (simp_f F g) (simp_f F y) (simp_f F n)
   | _ => e
   end
 end.

Lemma simp_width F : forall e, expr_width (simp_f F e) = expr_width e.
Proof.
 induction e; cbn [simp_f]; match goal with |- context [xeval2 F ?x] => destruct (xeval2 F x) as [z|] end; try reflexivity.
 destruct op; cbn [expr_width]; try reflexivity.
 destruct (zero_expressionb (simp_f F e1) || zero_expressionb (simp_f F e2)); reflexivity.
Qed.

Lemma const_case s e z : eval_expr s e = z -> eval_expr s (EConst (expr_width e) z) = eval_expr s e.
Proof. intro H. cbn [eval_expr]. rewrite <- H at 1. apply eval_normalized. Qed.

Lemma simp_sound F s (HF : FactsHold s F) : forall e, eval_expr s (simp_f F e) = eval_expr s e.
Proof.
 induction e; cbn [simp_f]; match goal with |- context [xeval2 F ?x] => let Hx := fresh "Hx" in destruct (xeval2 F x) as [z|] eqn:Hx end.
 all: try (exact (const_case s _ _ (xeval2_sound F s HF _ _ Hx))).
 - reflexivity.
 - reflexivity.
 - cbn [eval_expr]. rewrite IHe1, IHe2. reflexivity.
 - cbn [eval_expr]. rewrite IHe1, IHe2, simp_width. reflexivity.
 - cbn [eval_expr]. rewrite IHe, simp_width. reflexivity.
 - cbn [eval_expr]. rewrite IHe, simp_width. reflexivity.
 - cbn [eval_expr]. rewrite IHe. reflexivity.
 - destruct op; try (cbn [eval_expr]; rewrite IHe1, IHe2, ?simp_width; reflexivity).
   destruct (zero_expressionb (simp_f F e1) || zero_expressionb (simp_f F e2)) eqn:Hz.
   + apply orb_true_iff in Hz as [Hz|Hz].
     * rewrite (zero_expression_sound _ s Hz) in IHe1. cbn [eval_expr]. rewrite <- IHe1. rewrite Z.land_0_l. reflexivity.
     * rewrite (zero_expression_sound _ s Hz) in IHe2. cbn [eval_expr]. rewrite <- IHe2. rewrite Z.land_0_r. reflexivity.
   + cbn [eval_expr]. rewrite IHe1, IHe2. reflexivity.
 - cbn [eval_expr]. rewrite IHe1, IHe2, IHe3. reflexivity.
Qed.

Definition xeval3 (F:Facts) (e:Expr) : option Z := xeval2 F (simp_f F e).
Lemma xeval3_sound F s (HF : FactsHold s F) e z : xeval3 F e = Some z -> eval_expr s e = z.
Proof. unfold xeval3. intro H. rewrite <- (simp_sound F s HF e). exact (xeval2_sound F s HF _ _ H). Qed.

Definition expr_fact_ok3 (F:Facts) (ez : Expr * Z) : bool :=
  match xeval3 F (fst ez) with Some z => Z.eqb z (snd ez) | None => false end.
Lemma exprs_hold3 F s0 (L : Facts) : FactsHold s0 F -> forallb (expr_fact_ok3 F) L = true -> FactsHold s0 L.
Proof.
  intros HF H e z HI. rewrite forallb_forall in H. specialize (H _ HI). unfold expr_fact_ok3 in H. cbn [fst snd] in H.
  destruct (xeval3 F e) as [z'|] eqn:E; [|discriminate]. apply Z.eqb_eq in H. subst z'.
  exact (xeval3_sound F s0 HF e z E).
Qed.

(** cases over the overlay executor, expression facts checked with xeval3 *)
Definition check_casebo3 ps T fuel (c:CaseBO) : bool :=
  let F := cbo_derived ps T fuel c in outs_in_facts F (cbo_outs c) && forallb (expr_fact_ok3 F) (cbo_exprs c).
Definition check_casesbo3 ps T fuel (cs:list CaseBO) : bool := forallb (check_casebo3 ps T fuel) cs.

Theorem casesbo3_sound p ps T cases seed fixed c :
  filter is_comb (processes p) = ps -> tab_okb ps T = true -> CombLFP p seed fixed ->
  check_casesbo3 ps T (statement_fuel p) cases = true -> In c cases -> FactsHold fixed (cbo_facts c) ->
  FactsHold fixed (cbo_derived ps T (statement_fuel p) c) /\ DecOut fixed (cbo_outs c) /\ FactsHold fixed (cbo_exprs c).
Proof.
  intros HP HT HL Hc Hin HF. unfold check_casesbo3 in Hc. rewrite forallb_forall in Hc. specialize (Hc c Hin).
  unfold check_casebo3 in Hc. apply andb_true_iff in Hc as [H1 H2].
  pose proof (orun_script_sound p ps T seed fixed HP (tab_okb_sound ps T HT) HL (cbo_script c) (cbo_facts c) HF) as HD.
  fold (cbo_derived ps T (statement_fuel p) c) in HD, H1, H2.
  refine (conj HD (conj _ _)).
  - intros t Ht. unfold outs_in_facts in H1. rewrite forallb_forall in H1. specialize (H1 t Ht).
    destruct (fact_find (cbo_derived ps T (statement_fuel p) c) (EVar (snd (fst t)) (fst (fst t)))) as [z|] eqn:Hf; [|discriminate].
    apply Z.eqb_eq in H1. subst z.
    pose proof (fact_find_sound _ _ _ fixed HD Hf) as Hv. cbn [eval_expr] in Hv. exact Hv.
  - exact (exprs_hold3 _ _ _ HD H2).
Qed.
End ExtendedSVEval3.
Print Assumptions ExtendedSVEval3.casesbo3_sound.
