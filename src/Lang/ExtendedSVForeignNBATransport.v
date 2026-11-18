(** Foreign-root transport for both blocking and captured NBA scalar writes. *)
From Coq Require Import List Bool PeanoNat ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVProducerAssignment
 Lang.ExtendedSVSingleRootInputs Lang.ExtendedSVRootProjection
 Lang.ExtendedSVForeignUpdateTransport.
Import ExtendedSV ExtendedSVProducerAssignment ExtendedSVSingleRootInputs
 ExtendedSVRootProjection ExtendedSVForeignUpdateTransport ListNotations.
Module ExtendedSVForeignNBATransport.
Fixpoint foreign_nbab root st:=match st with
 |SSkip=>true
 |SAssign _ rhs(LVar _ r)=>negb(Nat.eqb r root)&&no_input_rootb root rhs
 |SAssign _ _ _=>false
 |SSeq xs=>forallb(foreign_nbab root)xs
 |SIf guard yes no=>no_input_rootb root guard&&foreign_nbab root yes&&foreign_nbab root no
 |SCase scr arms=>no_input_rootb root scr&&forallb(fun arm=>key_freeb root(fst arm)&&foreign_nbab root(snd arm))arms
 end.
Lemma selected_foreign_nba root s value arms default:
 forallb(fun arm=>key_freeb root(fst arm)&&foreign_nbab root(snd arm))arms=true ->
 foreign_nbab root default=true ->foreign_nbab root(select_case_stmt s value arms default)=true.
Proof.
 induction arms as[|[key body]rest IH]in default|-*;cbn;intros HC HD;[exact HD|].
 apply andb_true_iff in HC as[HB HR]. apply andb_true_iff in HB as[HK HF].
 destruct key as[e|];[destruct(Z.eqb value(eval_expr s e))|];auto.
Qed.
Definition ExecForeignNBA u es et:=
 blocking_state et=apply_update(blocking_state es)u /\pending_nba et=pending_nba es /\
 Forall(fun v=>update_signal v<>update_signal u)(pending_nba es).
Theorem exec_foreign_nba u fuel st es et:
 foreign_nbab(update_signal u)st=true ->ExecForeignNBA u es et ->
 ExecForeignNBA u(exec_stmt fuel st es)(exec_stmt fuel st et).
Proof.
 induction fuel as[|fuel IH]in st,es,et|-*;[auto|].
 destruct st as[|nba rhs lhs|xs|guard yes no|scr arms];cbn;intros HC HE.
 - exact HE.
 - destruct lhs as[w r|];[|discriminate]. apply andb_true_iff in HC as[HR HX].
   apply negb_true_iff in HR. apply Nat.eqb_neq in HR.
   destruct HE as[HB[HP HF]]. rewrite HB,invisible_update_keeps_expression by now apply no_input_rootb_sound.
   destruct nba;unfold ExecForeignNBA;cbn.
   + split;[reflexivity|]. split;[now rewrite HP|]. apply Forall_app. split;[exact HF|]. constructor;[exact HR|constructor].
   + split;[|now split].
     change(apply_update(apply_update(blocking_state es)u)(resolve_update(blocking_state es)(LVar w r)(eval_expr(blocking_state es)rhs))=
      apply_update(apply_update(blocking_state es)(resolve_update(blocking_state es)(LVar w r)(eval_expr(blocking_state es)rhs)))u).
     apply apply_update_commute. cbn[resolve_update resolve_lvalue update_signal]. congruence.
 - induction xs as[|st rest IHr]in es,et,HC,HE|-*;cbn in *;[exact HE|].
   apply andb_true_iff in HC as[HS HR]. apply IHr;[exact HR|now apply IH].
 - apply andb_true_iff in HC as[HG HN]. apply andb_true_iff in HG as[HG HY].
   destruct HE as[HB[HP HF]]. rewrite HB,invisible_update_keeps_expression by now apply no_input_rootb_sound.
   destruct(Z.eqb(eval_expr(blocking_state es)guard)0);apply IH;
   [exact HN|repeat split;assumption|exact HY|repeat split;assumption].
 - apply andb_true_iff in HC as[HS HA]. destruct HE as[HB[HP HF]].
   rewrite HB,invisible_update_keeps_expression by now apply no_input_rootb_sound.
   assert(Hkeys:forallb(fun arm=>key_freeb(update_signal u)(fst arm))arms=true).
   { apply forallb_forall. intros arm Hin. apply forallb_forall with(x:=arm)in HA;[|exact Hin].
     now apply andb_true_iff in HA as[HK Hbody]. }
   rewrite(select_case_outside_equal(update_signal u)(apply_update(blocking_state es)u)(blocking_state es)
    (eval_expr(blocking_state es)scr)arms SSkip Hkeys(update_outside u(blocking_state es))).
   apply IH;[apply selected_foreign_nba;[exact HA|reflexivity]|repeat split;assumption].
Qed.
Lemma foreign_nba_apply u us s : Forall(fun v=>update_signal v<>update_signal u)us ->
 apply_nba(apply_update s u)us=apply_update(apply_nba s us)u.
Proof.
 induction us as[|v vs IH]in s|-*;cbn;intro H;[reflexivity|].
 inversion H;subst. rewrite <-IH by assumption.
 f_equal. apply apply_update_commute. congruence.
Qed.
Theorem actual_process_foreign_nba_commutes p proc u s :
 foreign_nbab(update_signal u)(process_body proc)=true ->
 run_process p(apply_update s u)proc=apply_update(run_process p s proc)u.
Proof.
 intro H. unfold run_process.
 pose proof(exec_foreign_nba u(statement_fuel p)(process_body proc)
 {|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|}
 {|blocking_state:=apply_update s u;pending_nba:=[];emitted_updates:=[]|}H
 ltac:(split;[reflexivity|split;[reflexivity|constructor]]))as[HB[HP HF]].
 rewrite HB,HP. now apply foreign_nba_apply.
Qed.
Print Assumptions actual_process_foreign_nba_commutes.
End ExtendedSVForeignNBATransport.
