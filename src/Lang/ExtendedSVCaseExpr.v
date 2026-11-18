(** Case reflection, expression facts (template route, additive; 2026-11-03).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    Extends ExtendedSVCaseReflect: besides the derived root constants and wire expressions, a case may state EXPRESSION facts
    (e.g. the controller stall-guard conjunctions `(1056 & 1104 | ...) = 0` of CvTmplCtl2.facts_C): each is checked by [xeval2] under the
    derived constants. One boolean, one soundness theorem. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVSymExecPhase Lang.ExtendedSVCaseReflect.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVSymExecPhase ExtendedSVCaseReflect.
Local Open Scope Z_scope.
Module ExtendedSVCaseExpr.

Definition expr_fact_ok (F:Facts) (ez : Expr * Z) : bool :=
  match xeval2 F (fst ez) with Some z => Z.eqb z (snd ez) | None => false end.

Lemma exprs_hold F s0 (L : Facts) : FactsHold s0 F -> forallb (expr_fact_ok F) L = true -> FactsHold s0 L.
Proof.
  intros HF H e z HI. rewrite forallb_forall in H. specialize (H _ HI). unfold expr_fact_ok in H. cbn [fst snd] in H.
  destruct (xeval2 F e) as [z'|] eqn:E; [|discriminate]. apply Z.eqb_eq in H. subst z'.
  exact (xeval2_sound F s0 HF e z E).
Qed.

(** a case with expression facts: the extra list is checked under the derived constants of the case *)
Definition CaseX := (CaseSpec * Facts)%type.
Definition check_case_x ps T fuel (c : CaseX) : bool :=
  check_case ps T fuel (fst c) && forallb (expr_fact_ok (derived ps T fuel (fst c))) (snd c).
Definition check_cases_x ps T fuel (cs : list CaseX) : bool := forallb (check_case_x ps T fuel) cs.

Theorem cases_x_sound p ps T cases seed fixed c :
  filter is_comb (processes p) = ps -> tab_okb ps T = true -> CombLFP p seed fixed ->
  check_cases_x ps T (statement_fuel p) cases = true -> In c cases -> FactsHold fixed (cs_facts (fst c)) ->
  FactsHold fixed (derived ps T (statement_fuel p) (fst c)) /\ DecOut fixed (cs_outs (fst c)) /\
  (forall x, In x (cs_wires (fst c)) -> norm (snd (fst x)) (read_signal fixed (snd (fst (fst x)))) = norm (snd (fst x)) (eval_expr fixed (snd x))) /\
  FactsHold fixed (snd c).
Proof.
  intros HP HT HL Hc Hin HF. unfold check_cases_x in Hc. rewrite forallb_forall in Hc. specialize (Hc c Hin).
  unfold check_case_x in Hc. apply andb_true_iff in Hc as [H1 H2].
  pose proof (case_sound p ps T (fst c) seed fixed HP (tab_okb_sound ps T HT) HL HF H1) as [HD [Ho Hw]].
  refine (conj HD (conj Ho (conj Hw _))).
  exact (exprs_hold _ _ _ HD H2).
Qed.
End ExtendedSVCaseExpr.
Print Assumptions ExtendedSVCaseExpr.cases_x_sound.
