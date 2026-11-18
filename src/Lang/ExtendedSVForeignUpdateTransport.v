(** Foreign updates commute with ACTUAL blocking statement execution when
    all guards/keys/RHS avoid that root and no assignment writes it. *)
From Coq Require Import List Bool PeanoNat ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVProducerAssignment
 Lang.ExtendedSVSingleRootInputs Lang.ExtendedSVRootProjection
 Lang.ExtendedSVBlocking Lang.ExtendedSVBlockingReplay Lang.ExtendedSVCombIdempotence
 Lang.ExtendedSVProcessSlice.
Import ExtendedSV ExtendedSVProducerAssignment ExtendedSVSingleRootInputs
 ExtendedSVRootProjection ExtendedSVBlocking ExtendedSVBlockingReplay
 ExtendedSVCombIdempotence ExtendedSVProcessSlice ListNotations.
Module ExtendedSVForeignUpdateTransport.
Fixpoint foreign_freeb root st:=match st with
 |SSkip=>true
 |SAssign nba rhs(LVar _ r)=>negb nba&&negb(Nat.eqb r root)&&no_input_rootb root rhs
 |SAssign _ _ _=>false
 |SSeq xs=>forallb(foreign_freeb root)xs
 |SIf guard yes no=>no_input_rootb root guard&&foreign_freeb root yes&&foreign_freeb root no
 |SCase scr arms=>no_input_rootb root scr&&forallb(fun arm=>key_freeb root(fst arm)&&foreign_freeb root(snd arm))arms
 end.
Lemma foreign_selected root s value arms default:
 forallb(fun arm=>key_freeb root(fst arm)&&foreign_freeb root(snd arm))arms=true->
 foreign_freeb root default=true->foreign_freeb root(select_case_stmt s value arms default)=true.
Proof.
 induction arms as[|[key body]rest IH]in default|-*;cbn;[auto|].
 intros HC HD. apply andb_true_iff in HC as[HB HR]. apply andb_true_iff in HB as[HK HF].
 destruct key as[e|];[destruct(Z.eqb value(eval_expr s e))|];auto.
Qed.
Definition ExecShift update es et:=
 blocking_state et=apply_update(blocking_state es)update/\pending_nba es=[]/\pending_nba et=[].
Lemma update_outside update state:OutsideEqual(update_signal update)(apply_update state update)state.
Proof. intros r HR. rewrite read_signal_apply_update_other;[reflexivity|congruence]. Qed.
Theorem actual_statement_foreign_update_commutes update fuel st es et:
 foreign_freeb(update_signal update)st=true->ExecShift update es et->
 ExecShift update(exec_stmt fuel st es)(exec_stmt fuel st et).
Proof.
 induction fuel as[|fuel IH]in st,es,et|-*;[auto|].
 destruct st as[|nba rhs lhs|xs|guard yes no|scr arms];cbn;intros HC HE.
 - exact HE.
 - destruct lhs as[w r|];[|discriminate]. destruct nba;[discriminate|].
   apply andb_true_iff in HC as[HC HX]. apply andb_true_iff in HC as[HN HR].
   apply Bool.negb_true_iff in HR. apply Nat.eqb_neq in HR.
   destruct HE as[HB[HP HT]]. unfold ExecShift;cbn. split;[|now split].
   rewrite HB. rewrite invisible_update_keeps_expression by now apply no_input_rootb_sound.
   change(apply_update(apply_update(blocking_state es)update)
    (resolve_update(blocking_state es)(LVar w r)(eval_expr(blocking_state es)rhs))=
    apply_update(apply_update(blocking_state es)
    (resolve_update(blocking_state es)(LVar w r)(eval_expr(blocking_state es)rhs)))update).
   apply apply_update_commute. cbn[resolve_update resolve_lvalue update_signal]. congruence.
 - induction xs as[|st xs IHr]in es,et,HC,HE|-*;cbn in *;[exact HE|].
   apply andb_true_iff in HC as[Hst Hxs]. apply IHr;[exact Hxs|now apply IH].
 - apply andb_true_iff in HC as[HG HN]. apply andb_true_iff in HG as[HG HY].
   destruct HE as[HB[HP HT]].
   rewrite HB,invisible_update_keeps_expression by now apply no_input_rootb_sound.
   destruct(Z.eqb(eval_expr(blocking_state es)guard)0);apply IH;
   [exact HN|repeat split;assumption|exact HY|repeat split;assumption].
 - apply andb_true_iff in HC as[HS HA]. destruct HE as[HB[HP HT]].
   rewrite HB,invisible_update_keeps_expression by now apply no_input_rootb_sound.
   assert(Hkeys:forallb(fun arm=>key_freeb(update_signal update)(fst arm))arms=true).
   { apply forallb_forall. intros arm Hin. apply forallb_forall with(x:=arm)in HA;[|exact Hin].
     now apply andb_true_iff in HA as[HA _]. }
   rewrite(select_case_outside_equal(update_signal update)(apply_update(blocking_state es)update)
    (blocking_state es)(eval_expr(blocking_state es)scr)arms SSkip Hkeys(update_outside update(blocking_state es))).
   apply IH;[apply foreign_selected;[exact HA|reflexivity]|repeat split;assumption].
Qed.
Theorem actual_process_foreign_update_commutes p proc update state:
 foreign_freeb(update_signal update)(process_body proc)=true->
 run_process p(apply_update state update)proc=apply_update(run_process p state proc)update.
Proof.
 intro HC. unfold run_process.
 pose proof(actual_statement_foreign_update_commutes update(statement_fuel p)(process_body proc)
  {|blocking_state:=state;pending_nba:=[];emitted_updates:=[]|}
  {|blocking_state:=apply_update state update;pending_nba:=[];emitted_updates:=[]|}HC)as HE.
 assert(HI:ExecShift update {|blocking_state:=state;pending_nba:=[];emitted_updates:=[]|}
  {|blocking_state:=apply_update state update;pending_nba:=[];emitted_updates:=[]|})by(repeat split;reflexivity).
 destruct(HE HI)as[HB[HP HT]]. rewrite HP,HT. exact HB.
Qed.
Lemma actual_process_foreign_updates_commute p proc updates:
 (forall u,In u updates->foreign_freeb(update_signal u)(process_body proc)=true)->
 forall state,run_process p(apply_updates state updates)proc=
 apply_updates(run_process p state proc)updates.
Proof.
 intro H. induction updates as[|u us IH];intro state;cbn;[reflexivity|].
 rewrite IH;[|intros v HV;apply H;now right].
 rewrite actual_process_foreign_update_commutes;[reflexivity|apply H;now left].
Qed.
Definition later_preservesb first later:=blocking_onlyb(process_body later)&&
 forallb(fun root=>foreign_freeb root(process_body first))(process_writers later).
Theorem checked_original_later_preserves_fixed p first later:
 later_preservesb first later=true->LaterPreservesFixed p first later.
Proof.
 unfold later_preservesb. intro H. apply andb_true_iff in H as[HB HW].
 intros state HS. unfold ProducerFixed in *.
 rewrite(actual_blocking_process_replays p later state HB).
 rewrite actual_process_foreign_updates_commute.
 - now rewrite HS.
 - intros u HU. apply process_emitted_writers in HU.
   now apply forallb_forall with(x:=update_signal u)in HW.
Qed.
Fixpoint OrderedPreservation p order:Prop:=match order with
 |[]=>True|first::rest=>Forall(LaterPreservesFixed p first)rest/\OrderedPreservation p rest end.
Fixpoint ordered_preservationb order:=match order with
 |[]=>true|first::rest=>forallb(later_preservesb first)rest&&ordered_preservationb rest end.
Theorem ordered_preservationb_sound p order:
 ordered_preservationb order=true->OrderedPreservation p order.
Proof.
 induction order as[|first rest IH];cbn;intro H;[exact I|].
 apply andb_true_iff in H as[HH HT]. split;[|now apply IH].
 apply Forall_forall. intros later Hin. apply checked_original_later_preserves_fixed.
 now apply forallb_forall with(x:=later)in HH.
Qed.
Theorem idempotent_producers_with_preservation_complete p order:
 Forall(ProducerIdempotent p)order->OrderedPreservation p order->OrderedProducerCertificate p order.
Proof.
 intro H. induction H;cbn;intro HP;[exact I|].
 destruct HP as[HL HT]. split;[exact H|]. split;[exact HL|now apply IHForall].
Qed.
End ExtendedSVForeignUpdateTransport.
Print Assumptions ExtendedSVForeignUpdateTransport.actual_process_foreign_update_commutes.
