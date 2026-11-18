(** Scripted cases (forward + backward steps) with expression facts; one checker, one soundness theorem (template route, additive).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVSymExecPhase
 Lang.ExtendedSVCaseReflect Lang.ExtendedSVCaseExpr Lang.ExtendedSVBackward Lang.ExtendedSVSymExecOverlay Lang.ExtendedSVBackOverlay.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVSymExecPhase ExtendedSVCaseExpr ExtendedSVBackward ExtendedSVSymExecOverlay ExtendedSVBackOverlay.
Local Open Scope Z_scope.
Module ExtendedSVCaseBackO.
Record CaseBO := mkCaseBOO {
  cbo_facts : Facts;                      (* literal facts about the driven state (registers, hypotheses such as 586 = 1) *)
  cbo_script : Script;                    (* forward / backward steps *)
  cbo_outs : list ((signal*nat)*Z);       (* derived root constants *)
  cbo_exprs : Facts }.                    (* derived expression facts *)
Definition cbo_derived ps T fuel (c:CaseBO) : Facts := orun_script ps T fuel (cbo_facts c) (cbo_script c).
Definition check_casebo ps T fuel (c:CaseBO) : bool :=
  let F := cbo_derived ps T fuel c in outs_in_facts F (cbo_outs c) && forallb (expr_fact_ok F) (cbo_exprs c).
Definition check_casesbo ps T fuel (cs:list CaseBO) : bool := forallb (check_casebo ps T fuel) cs.

Theorem casesbo_sound p ps T cases seed fixed c :
  filter is_comb (processes p) = ps -> tab_okb ps T = true -> CombLFP p seed fixed ->
  check_casesbo ps T (statement_fuel p) cases = true -> In c cases -> FactsHold fixed (cbo_facts c) ->
  FactsHold fixed (cbo_derived ps T (statement_fuel p) c) /\ DecOut fixed (cbo_outs c) /\ FactsHold fixed (cbo_exprs c).
Proof.
  intros HP HT HL Hc Hin HF. unfold check_casesbo in Hc. rewrite forallb_forall in Hc. specialize (Hc c Hin).
  unfold check_casebo in Hc. apply andb_true_iff in Hc as [H1 H2].
  pose proof (orun_script_sound p ps T seed fixed HP (tab_okb_sound ps T HT) HL (cbo_script c) (cbo_facts c) HF) as HD.
  fold (cbo_derived ps T (statement_fuel p) c) in HD, H1, H2.
  refine (conj HD (conj _ _)).
  - intros t Ht. unfold outs_in_facts in H1. rewrite forallb_forall in H1. specialize (H1 t Ht).
    destruct (fact_find (cbo_derived ps T (statement_fuel p) c) (EVar (snd (fst t)) (fst (fst t)))) as [z|] eqn:Hf; [|discriminate].
    apply Z.eqb_eq in H1. subst z.
    pose proof (fact_find_sound _ _ _ fixed HD Hf) as Hv. cbn [eval_expr] in Hv. exact Hv.
  - exact (exprs_hold _ _ _ HD H2).
Qed.
End ExtendedSVCaseBackO.
Print Assumptions ExtendedSVCaseBackO.casesbo_sound.
