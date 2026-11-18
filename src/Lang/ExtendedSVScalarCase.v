(** A linear structural proof for scalar blocking cases. Default arms retain
    their original position and last-default behavior; no branch is assumed. *)
From Coq Require Import List ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVAutoAdapterEffects
 Lang.ExtendedSVWordInvariant Lang.ExtendedSVAssignment.
Import ListNotations ExtendedSV ExtendedSVAutoAdapterEffects
 ExtendedSVWordInvariant ExtendedSVAssignment.
Module ExtendedSVScalarCase.
Fixpoint scalar_case_expression width scrutinee (arms:list(option Expr*Expr)) default :=
 match arms with
 |[]=>default
 |(None,rhs)::rest=>scalar_case_expression width scrutinee rest rhs
 |(Some key,rhs)::rest=>ECond width (EBinary 1 BEq scrutinee key) rhs
   (scalar_case_expression width scrutinee rest default)
 end.
Definition scalar_case_arms width root (arms:list(option Expr*Expr)) :=
 map(fun arm=>(fst arm,FAssign false(snd arm)(LVar width root)))arms.
Fixpoint select_effect scrutinee (arms:list(option Expr*EffectPlan)) es default :=
 match arms with
 |[]=>default
 |(None,p)::rest=>select_effect scrutinee rest es(eval_effect p es)
 |(Some key,p)::rest=>if Z.eqb(eval_expr(blocking_state es)scrutinee)
     (eval_expr(blocking_state es)key)
   then eval_effect p es else select_effect scrutinee rest es default
 end.
Definition output width root es :=
 norm width(read_signal(apply_nba(blocking_state es)(pending_nba es))root).

Lemma assign_output width root rhs s:
 output width root(eval_effect(FAssign false rhs(LVar width root))(initial_exec s))=
 norm width(eval_expr s rhs).
Proof.
 unfold output;cbn[eval_effect initial_exec blocking_state pending_nba apply_nba].
 unfold apply_update,resolve_update.
 cbn[resolve_lvalue update_signal update_offset update_width update_value].
 rewrite read_signal_write_same,norm_full_low_write,norm_idempotent;reflexivity.
Qed.
Lemma conditional_output width scrutinee key yes no s:
 norm width(eval_expr s(ECond width(EBinary 1 BEq scrutinee key)yes no))=
 if Z.eqb(eval_expr s scrutinee)(eval_expr s key)
 then norm width(eval_expr s yes)else norm width(eval_expr s no).
Proof.
 cbn[eval_expr];rewrite norm_one_boolz.
 destruct(Z.eqb(eval_expr s scrutinee)(eval_expr s key));
 cbn[boolz Z.eqb];apply norm_idempotent.
Qed.
Lemma select_output width root scrutinee arms s default expression:
 output width root default=norm width(eval_expr s expression)->
 output width root(select_effect scrutinee(scalar_case_arms width root arms)
   (initial_exec s)default)=
 norm width(eval_expr s(scalar_case_expression width scrutinee arms expression)).
Proof.
 revert default expression;induction arms as[|[key rhs]rest IH];intros default expression H.
 - exact H.
 - destruct key as[key|];cbn[scalar_case_arms map fst snd select_effect
     initial_exec blocking_state scalar_case_expression].
   + rewrite conditional_output.
     destruct(Z.eqb(eval_expr s scrutinee)(eval_expr s key)).
     * apply assign_output.
     * apply IH;exact H.
   + apply IH;apply assign_output.
Qed.
Lemma select_matches scrutinee arms es default:
 (fix select (xs:list(option Expr*EffectPlan)) (d:ExecState):ExecState :=
  match xs with
  |[]=>d
  |(None,p)::rest=>select rest(eval_effect p es)
  |(Some key,p)::rest=>if Z.eqb(eval_expr(blocking_state es)scrutinee)
      (eval_expr(blocking_state es)key)
    then eval_effect p es else select rest d
  end) arms default=select_effect scrutinee arms es default.
Proof.
 revert default;induction arms as[|[key p]rest IH];intro default;[reflexivity|].
 destruct key as[key|];cbn[select_effect].
 - destruct(Z.eqb(eval_expr(blocking_state es)scrutinee)(eval_expr(blocking_state es)key));
   [reflexivity|apply IH].
 - apply IH.
Qed.
Theorem scalar_case_output width root scrutinee arms s:
 output width root(eval_effect(FCase scrutinee(scalar_case_arms width root arms))(initial_exec s))=
 norm width(eval_expr s(scalar_case_expression width scrutinee arms(EVar width root))).
Proof.
 pose proof(select_matches scrutinee(scalar_case_arms width root arms)
   (initial_exec s)(initial_exec s))as H.
 change(eval_effect(FCase scrutinee(scalar_case_arms width root arms))(initial_exec s)=
   select_effect scrutinee(scalar_case_arms width root arms)(initial_exec s)(initial_exec s))in H.
 rewrite H.
 apply select_output. unfold output;cbn[initial_exec blocking_state pending_nba apply_nba eval_expr].
 symmetry;apply norm_idempotent.
Qed.
End ExtendedSVScalarCase.
Print Assumptions ExtendedSVScalarCase.scalar_case_output.
