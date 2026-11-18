(** Typed multi-output, input-free execution certificate. Captured updates
    remain identical when only OLD output payloads differ; original branch
    selection and intra-process update order are retained. *)
From Coq Require Import List Bool PeanoNat ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVExprAgreement Lang.ExtendedSVRootProjection.
Import ExtendedSV ExtendedSVExprAgreement ExtendedSVRootProjection ListNotations.
Module ExtendedSVOutputsFree.
Definition OutputSpec:=list(nat*signal).
Definition owns_rootb (spec:OutputSpec)root:=existsb(fun wr=>Nat.eqb(snd wr)root)spec.
Definition supports_outputb (spec:OutputSpec)width root:=
 existsb(fun wr=>Nat.eqb(fst wr)width&&Nat.eqb(snd wr)root)spec.
Definition output_free_exprb spec expr:=
 forallb(fun wr=>negb(owns_rootb spec(snd wr)))(expr_inputs expr).
Definition OutsideOutputs spec s t:=forall r,owns_rootb spec r=false->read_signal s r=read_signal t r.
Definition SupportedUpdate spec u:=update_offset u=0%Z/\In(update_width u,update_signal u)spec.
Lemma support_sound spec w r:supports_outputb spec w r=true->In(w,r)spec.
Proof.
 intro H. apply existsb_exists in H as[[w' r'][HI HE]]. cbn in HE.
 apply andb_true_iff in HE as[HW HR]. apply Nat.eqb_eq in HW,HR. now subst.
Qed.
Lemma support_owns spec w r:In(w,r)spec->owns_rootb spec r=true.
Proof. intro H. apply existsb_exists. exists(w,r). split;[exact H|cbn;apply Nat.eqb_refl]. Qed.
Lemma outside_outputs_eval spec expr s t:
 output_free_exprb spec expr=true->OutsideOutputs spec s t->eval_expr s expr=eval_expr t expr.
Proof.
 intros HE HS. apply eval_expr_agree. intros w r HR.
 unfold output_free_exprb in HE. apply forallb_forall with(x:=(w,r))in HE;[|exact HR].
 cbn in HE. apply Bool.negb_true_iff in HE. now rewrite HS by exact HE.
Qed.
Definition output_free_keyb spec key:=match key with None=>true|Some e=>output_free_exprb spec e end.
Fixpoint output_free_stmtb spec st:=match st with
 |SSkip=>true
 |SAssign nba rhs(LVar w r)=>negb nba&&supports_outputb spec w r&&output_free_exprb spec rhs
 |SAssign _ _ _=>false
 |SSeq xs=>forallb(output_free_stmtb spec)xs
 |SIf guard yes no=>output_free_exprb spec guard&&output_free_stmtb spec yes&&output_free_stmtb spec no
 |SCase scr arms=>output_free_exprb spec scr&&forallb(fun arm=>output_free_keyb spec(fst arm)&&output_free_stmtb spec(snd arm))arms
 end.
Lemma outputs_select_agree spec s t value arms default:
 forallb(fun arm=>output_free_keyb spec(fst arm))arms=true->OutsideOutputs spec s t->
 select_case_stmt s value arms default=select_case_stmt t value arms default.
Proof.
 induction arms as[|[key body]rest IH]in default|-*;cbn;[auto|].
 intros HC HS. apply andb_true_iff in HC as[HK HR]. destruct key as[e|];cbn in *.
 - rewrite(outside_outputs_eval spec e s t HK HS).
   destruct(Z.eqb value(eval_expr t e));[reflexivity|now apply IH].
 - now apply IH.
Qed.
Lemma outputs_selected_free spec s value arms default:
 forallb(fun arm=>output_free_keyb spec(fst arm)&&output_free_stmtb spec(snd arm))arms=true->
 output_free_stmtb spec default=true->output_free_stmtb spec(select_case_stmt s value arms default)=true.
Proof.
 induction arms as[|[key body]rest IH]in default|-*;cbn;[auto|].
 intros HC HD. apply andb_true_iff in HC as[HB HR]. apply andb_true_iff in HB as[HK HF].
 destruct key as[e|];[destruct(Z.eqb value(eval_expr s e))|];auto.
Qed.
Definition ExecOutputs spec es et:=OutsideOutputs spec(blocking_state es)(blocking_state et)/\
 pending_nba es=[]/\pending_nba et=[]/\emitted_updates es=emitted_updates et/\
 Forall(SupportedUpdate spec)(emitted_updates es).
Theorem actual_outputs_free_execution spec fuel st es et:
 output_free_stmtb spec st=true->ExecOutputs spec es et->
 ExecOutputs spec(exec_stmt fuel st es)(exec_stmt fuel st et).
Proof.
 induction fuel as[|fuel IH]in st,es,et|-*;[auto|].
 destruct st as[|nba rhs lhs|xs|guard yes no|scr arms];cbn;intros HC HE.
 - exact HE.
 - destruct lhs as[w r|];[|discriminate]. destruct nba;[discriminate|].
   apply andb_true_iff in HC as[HC HX]. apply andb_true_iff in HC as[HN HS].
   apply support_sound in HS.
   destruct HE as[HB[HP[HT[HU Htyped]]]].
   rewrite(outside_outputs_eval spec rhs(blocking_state es)(blocking_state et)HX HB).
   unfold ExecOutputs;cbn. split.
   + intros r' HR'. assert(Hneq:r<>r').
     { intro E. subst r'. pose proof(support_owns spec w r HS). congruence. }
     rewrite !read_signal_write_other by congruence. now apply HB.
   + split;[exact HP|]. split;[exact HT|]. split;[now rewrite HU|].
     apply Forall_app. split;[exact Htyped|]. constructor;[split;[reflexivity|exact HS]|constructor].
 - induction xs as[|st xs IHr]in es,et,HC,HE|-*;cbn in *;[exact HE|].
   apply andb_true_iff in HC as[Hst Hxs]. apply IHr;[exact Hxs|now apply IH].
 - apply andb_true_iff in HC as[HG HN]. apply andb_true_iff in HG as[HG HY].
   destruct HE as[HB[HP[HT[HU Htyped]]]].
   rewrite(outside_outputs_eval spec guard(blocking_state es)(blocking_state et)HG HB).
   destruct(Z.eqb(eval_expr(blocking_state et)guard)0);apply IH;
   [exact HN|repeat split;assumption|exact HY|repeat split;assumption].
 - apply andb_true_iff in HC as[HS HA]. destruct HE as[HB[HP[HT[HU Htyped]]]].
   rewrite(outside_outputs_eval spec scr(blocking_state es)(blocking_state et)HS HB).
   assert(Hkeys:forallb(fun arm=>output_free_keyb spec(fst arm))arms=true).
   { apply forallb_forall. intros arm Hin. apply forallb_forall with(x:=arm)in HA;[|exact Hin].
     now apply andb_true_iff in HA as[HA _]. }
   rewrite(outputs_select_agree spec(blocking_state es)(blocking_state et)
    (eval_expr(blocking_state et)scr)arms SSkip Hkeys HB).
   apply IH;[apply outputs_selected_free;[exact HA|reflexivity]|repeat split;assumption].
Qed.
Theorem actual_outputs_free_captured_updates spec p proc s t:
 output_free_stmtb spec(process_body proc)=true->OutsideOutputs spec s t->
 process_updates p s proc=process_updates p t proc/\Forall(SupportedUpdate spec)(process_updates p s proc).
Proof.
 intros HC HS. unfold process_updates.
 pose proof(actual_outputs_free_execution spec(statement_fuel p)(process_body proc)
  {|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|}
  {|blocking_state:=t;pending_nba:=[];emitted_updates:=[]|}HC)as H.
 assert(HI:ExecOutputs spec {|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|}
  {|blocking_state:=t;pending_nba:=[];emitted_updates:=[]|}).
 { repeat split;auto;constructor. }
 destruct(H HI)as[HB[HP[HT HU]]]. exact HU.
Qed.
End ExtendedSVOutputsFree.
Print Assumptions ExtendedSVOutputsFree.actual_outputs_free_captured_updates.
