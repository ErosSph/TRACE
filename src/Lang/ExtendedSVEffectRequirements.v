(** Predicate transformers for complete blocking/NBA effects. Conditions see
    the live blocking state; queued and emitted writes are never erased. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVAutoAdapterEffects
 Lang.ExtendedSVStaticRootCertificate Lang.ExtendedSVRootProjection.
Import ExtendedSV ExtendedSVAutoAdapterEffects ExtendedSVStaticRootCertificate
 ExtendedSVRootProjection ListNotations.
Module ExtendedSVEffectRequirements.
Definition Transformer := (ExecState->Prop)->ExecState->Prop.
Definition Correct (effect:EffectPlan)(wp:Transformer):Prop :=
 forall post es,wp post es <->post(eval_effect effect es).
Definition identity_wp:Transformer:=fun post es=>post es.
Definition assignment_wp nba rhs lhs:Transformer:=
 fun post es=>post(eval_effect(FAssign nba rhs lhs)es).
Definition conditional_wp guard (yes no:Transformer):Transformer:=fun post es=>
 (eval_expr(blocking_state es)guard=0%Z ->no post es) /\
 (eval_expr(blocking_state es)guard<>0%Z ->yes post es).
Fixpoint sequence_wp(wps:list Transformer):Transformer:=match wps with
 |[]=>identity_wp|w::rest=>fun post es=>w(sequence_wp rest post)es end.
Definition ListCorrect effects wps:=forall post es,
 sequence_wp wps post es <->post(fold_left(fun s e=>eval_effect e s)effects es).

Lemma empty_correct:Correct FEmpty identity_wp.
Proof. intros post es;reflexivity. Qed.
Lemma assignment_correct nba rhs lhs:Correct(FAssign nba rhs lhs)(assignment_wp nba rhs lhs).
Proof. intros post es;reflexivity. Qed.
Lemma conditional_correct g y n wy wn:
 Correct y wy ->Correct n wn ->Correct(FIf g y n)(conditional_wp g wy wn).
Proof.
 intros HY HN post es;unfold conditional_wp.
 specialize(HY post es);specialize(HN post es).
 cbn[eval_effect];destruct(Z.eqb(eval_expr(blocking_state es)g)0)eqn:HG.
 - apply Z.eqb_eq in HG;tauto.
 - apply Z.eqb_neq in HG;tauto.
Qed.
Lemma list_nil_correct:ListCorrect [] [].
Proof. intros post es;reflexivity. Qed.
Lemma list_cons_correct e rest w ws:
 Correct e w ->ListCorrect rest ws ->ListCorrect(e::rest)(w::ws).
Proof.
 intros HE HT post es;cbn[sequence_wp fold_left].
 transitivity(sequence_wp ws post(eval_effect e es));[apply HE|apply HT].
Qed.
Lemma sequence_correct effects wps:ListCorrect effects wps ->Correct(FSeq effects)(sequence_wp wps).
Proof. intros H post es;exact(H post es). Qed.

Fixpoint eval_arms scr (arms:list(option Expr*EffectPlan)) es default:=
 match arms with
 |[]=>default
 |(None,e)::rest=>eval_arms scr rest es(eval_effect e es)
 |(Some key,e)::rest=>if Z.eqb(eval_expr(blocking_state es)scr)(eval_expr(blocking_state es)key)
   then eval_effect e es else eval_arms scr rest es default
 end.
Definition CaseTransformer:=Transformer->Transformer.
Definition case_nil:CaseTransformer:=fun default=>default.
Definition case_default(branch:Transformer)(rest:CaseTransformer):CaseTransformer:=
 fun _=>rest branch.
Definition case_key scr key(branch:Transformer)(rest:CaseTransformer):CaseTransformer:=
 fun default post es=>
 (eval_expr(blocking_state es)scr=eval_expr(blocking_state es)key ->branch post es) /\
 (eval_expr(blocking_state es)scr<>eval_expr(blocking_state es)key ->rest default post es).
Definition CaseCorrect scr arms (wp:CaseTransformer):Prop:=
 forall post es default value,(default post es <->post value) ->
 wp default post es <->post(eval_arms scr arms es value).
Lemma case_nil_correct scr:CaseCorrect scr [] case_nil.
Proof. intros post es default value H;exact H. Qed.
Lemma case_default_correct scr e rest w ws:
 Correct e w ->CaseCorrect scr rest ws ->CaseCorrect scr((None,e)::rest)(case_default w ws).
Proof.
 intros HE HT post es default value H;unfold case_default;cbn[eval_arms].
 apply HT;apply HE.
Qed.
Lemma case_key_correct scr key e rest w ws:
 Correct e w ->CaseCorrect scr rest ws ->CaseCorrect scr((Some key,e)::rest)(case_key scr key w ws).
Proof.
 intros HE HT post es default value H;unfold case_key.
 specialize(HE post es);specialize(HT post es default value H).
 cbn[eval_arms];destruct(Z.eqb(eval_expr(blocking_state es)scr)(eval_expr(blocking_state es)key))eqn:HG.
 - apply Z.eqb_eq in HG;tauto.
 - apply Z.eqb_neq in HG;tauto.
Qed.
Lemma case_correct scr arms wp:CaseCorrect scr arms wp ->Correct(FCase scr arms)(wp identity_wp).
Proof.
 intros H post es.
 assert(HA:forall remaining default,
   (fix select xs d:=match xs with
    |[]=>d
    |(None,e)::rest=>select rest(eval_effect e es)
    |(Some key,e)::rest=>if Z.eqb(eval_expr(blocking_state es)scr)(eval_expr(blocking_state es)key)
      then eval_effect e es else select rest d end)remaining default=
   eval_arms scr remaining es default).
 { induction remaining as[|[key e]rest IH];intro default;[reflexivity|].
   destruct key as[key|];cbn[eval_arms];[|apply IH].
   destruct(Z.eqb(eval_expr(blocking_state es)scr)(eval_expr(blocking_state es)key));
   [reflexivity|apply IH]. }
 pose proof(H post es identity_wp es (iff_refl _))as HC.
 assert(HE:eval_effect(FCase scr arms)es=eval_arms scr arms es es)by exact(HA arms es).
 rewrite HE;exact HC.
Qed.
Definition phase_wp p proc width root (wp:Transformer) ev pre expected:Prop:=
 (process_matches_states pre(phase_driven_state p ev pre)proc=true ->
  wp(fun es=>norm width(apply_updates_root_value root(read_signal pre root)(emitted_updates es))=expected)
    (initial_exec(phase_driven_state p ev pre))) /\
 (process_matches_states pre(phase_driven_state p ev pre)proc=false ->
  norm width(read_signal pre root)=expected).

Theorem phase_wp_exact p proc width root effect wp ev pre expected:
 RootCertificate p root [proc] ->
 compile_effect(statement_fuel p)(process_body proc)=Some effect ->
 Correct effect wp ->changed_signal ev<>root ->
 (phase_wp p proc width root wp ev pre expected <->
  norm width(read_signal(PhaseSemantics p ev pre)root)=expected).
Proof.
 intros HC HE HW Hroot.
 pose proof(certified_phase_root p root [proc] HC ev pre Hroot)as HP.
 unfold phase_wp.
 specialize(HW (fun es=>norm width(apply_updates_root_value root(read_signal pre root)(emitted_updates es))=expected)
   (initial_exec(phase_driven_state p ev pre))).
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc)eqn:HS;
 cbn[filter flat_map app]in HP;try rewrite HS in HP;cbn[flat_map app]in HP.
 - rewrite(checked_effect_updates p proc effect HE)in HP.
   rewrite app_nil_r in HP.
   rewrite HP;intuition discriminate.
 - cbn[apply_updates_root_value]in HP;rewrite HP;intuition discriminate.
Qed.
End ExtendedSVEffectRequirements.
Print Assumptions ExtendedSVEffectRequirements.conditional_correct.
Print Assumptions ExtendedSVEffectRequirements.sequence_correct.
Print Assumptions ExtendedSVEffectRequirements.case_correct.
Print Assumptions ExtendedSVEffectRequirements.phase_wp_exact.
