(** Actual single-output statement execution ignores the old output payload
    when all guards, case keys and RHS inputs are proved independent of it. *)
From Coq Require Import List Bool ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVProducerAssignment
 Lang.ExtendedSVExprAgreement Lang.ExtendedSVRootProjection.
Import ExtendedSV ExtendedSVProducerAssignment ExtendedSVExprAgreement
 ExtendedSVRootProjection ListNotations.
Module ExtendedSVSingleRootInputs.
Definition OutsideEqual root s t:=forall r,r<>root->read_signal s r=read_signal t r.
Lemma outside_eval root expr s t:
 no_input_rootb root expr=true->OutsideEqual root s t->eval_expr s expr=eval_expr t expr.
Proof.
 intros HE HS. apply eval_expr_agree. intros w r HR.
 rewrite HS;[reflexivity|]. apply (no_input_rootb_sound root expr HE(w,r)HR).
Qed.
Definition key_freeb root key:=match key with None=>true|Some e=>no_input_rootb root e end.
Fixpoint single_root_freeb root width st:=match st with
 |SSkip=>true
 |SAssign nba rhs(LVar w r)=>negb nba&&Nat.eqb w width&&Nat.eqb r root&&no_input_rootb root rhs
 |SAssign _ _ _=>false
 |SSeq xs=>forallb(single_root_freeb root width)xs
 |SIf guard yes no=>no_input_rootb root guard&&single_root_freeb root width yes&&single_root_freeb root width no
 |SCase scr arms=>no_input_rootb root scr&&forallb(fun arm=>key_freeb root(fst arm)&&single_root_freeb root width(snd arm))arms
 end.
Lemma select_case_outside_equal root s t value arms default:
 forallb(fun arm=>key_freeb root(fst arm))arms=true->OutsideEqual root s t->
 select_case_stmt s value arms default=select_case_stmt t value arms default.
Proof.
 induction arms as[|[key body]rest IH]in default|-*;cbn;[auto|].
 intros HC HS. apply andb_true_iff in HC as[HK HR].
 destruct key as[e|];cbn in *.
 - rewrite(outside_eval root e s t HK HS).
   destruct(Z.eqb value(eval_expr t e));[reflexivity|now apply IH].
 - now apply IH.
Qed.
Lemma selected_single_root_free root width s value arms default:
 forallb(fun arm=>key_freeb root(fst arm)&&single_root_freeb root width(snd arm))arms=true->
 single_root_freeb root width default=true->
 single_root_freeb root width(select_case_stmt s value arms default)=true.
Proof.
 induction arms as[|[key body]rest IH]in default|-*;cbn;[auto|].
 intros HC HD. apply andb_true_iff in HC as[HB HR]. apply andb_true_iff in HB as[HK HF].
 destruct key as[e|];[destruct(Z.eqb value(eval_expr s e))|];auto.
Qed.
Definition ExecOutsideEqual root es et:=
 OutsideEqual root(blocking_state es)(blocking_state et)/\
 pending_nba es=pending_nba et/\emitted_updates es=emitted_updates et.
Theorem actual_single_root_execution_congruence root width fuel st es et:
 single_root_freeb root width st=true->ExecOutsideEqual root es et->
 ExecOutsideEqual root(exec_stmt fuel st es)(exec_stmt fuel st et).
Proof.
 induction fuel as[|fuel IH]in st,es,et|-*;[auto|].
 destruct st as[|nba rhs lhs|xs|guard yes no|scr arms];cbn;intros HC HE.
 - exact HE.
 - destruct lhs as[w r|];[|discriminate].
   destruct nba;[discriminate|].
   apply andb_true_iff in HC as[HC HX].
   apply andb_true_iff in HC as[HC HR].
   apply andb_true_iff in HC as[HN HW].
   apply Nat.eqb_eq in HW,HR. subst w r.
   destruct HE as[HB[HP HU]].
   rewrite(outside_eval root rhs(blocking_state es)(blocking_state et)HX HB).
   unfold ExecOutsideEqual;cbn. split.
   + intros r Hneq. rewrite !read_signal_write_other by congruence. now apply HB.
   + split;[exact HP|now rewrite HU].
 - induction xs as[|st xs IHr]in es,et,HC,HE|-*;cbn in *;[exact HE|].
   apply andb_true_iff in HC as[Hst Hxs]. apply IHr;[exact Hxs|now apply IH].
 - apply andb_true_iff in HC as[HG HN]. apply andb_true_iff in HG as[HG HY].
   destruct HE as[HB[HP HU]].
   rewrite(outside_eval root guard(blocking_state es)(blocking_state et)HG HB).
   destruct(Z.eqb(eval_expr(blocking_state et)guard)0);apply IH;
   [exact HN|repeat split;assumption|exact HY|repeat split;assumption].
 - apply andb_true_iff in HC as[HS HA].
   destruct HE as[HB[HP HU]].
   rewrite(outside_eval root scr(blocking_state es)(blocking_state et)HS HB).
   assert(Hkeys:forallb(fun arm=>key_freeb root(fst arm))arms=true).
   { apply forallb_forall. intros arm Hin.
     apply forallb_forall with(x:=arm)in HA;[|exact Hin].
     now apply andb_true_iff in HA as[HA _]. }
   rewrite(select_case_outside_equal root(blocking_state es)(blocking_state et)
    (eval_expr(blocking_state et)scr)arms SSkip Hkeys HB).
   apply IH;[apply selected_single_root_free;[exact HA|reflexivity]|].
   repeat split;assumption.
Qed.
Theorem actual_single_root_captured_updates_ignore_old_output p proc root width s t:
 single_root_freeb root width(process_body proc)=true->OutsideEqual root s t->
 process_updates p s proc=process_updates p t proc.
Proof.
 intros HC HS. unfold process_updates.
 pose proof(actual_single_root_execution_congruence root width(statement_fuel p)
  (process_body proc){|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|}
  {|blocking_state:=t;pending_nba:=[];emitted_updates:=[]|}HC)as H.
 assert(Hinitial:ExecOutsideEqual root
  {|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|}
  {|blocking_state:=t;pending_nba:=[];emitted_updates:=[]|}).
 { repeat split;auto. }
 exact(proj2(proj2(H Hinitial))).
Qed.
End ExtendedSVSingleRootInputs.
Print Assumptions ExtendedSVSingleRootInputs.actual_single_root_captured_updates_ignore_old_output.
