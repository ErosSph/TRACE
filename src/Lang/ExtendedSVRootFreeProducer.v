(** Root-independent captures for arbitrary lvalues, including overlapping
    partial writes. Reject reads of any old output root, including offsets.
    Pure blocking or pure NBA only: mixed scheduling is not chronological replay. *)
From Coq Require Import List Bool PeanoNat ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVOutputsFree Lang.ExtendedSVRootProjection
 Lang.ExtendedSVBlocking Lang.ExtendedSVBlockingReplay Lang.ExtendedSVNBACaseProjection
 Lang.ExtendedSVNBAOutputsFreeProducer Lang.ExtendedSVArbitraryMaskedReplay
 Lang.ExtendedSVCombIdempotence.
Import ListNotations ExtendedSV ExtendedSVOutputsFree ExtendedSVRootProjection
 ExtendedSVBlocking ExtendedSVBlockingReplay ExtendedSVNBACaseProjection
 ExtendedSVNBAOutputsFreeProducer ExtendedSVArbitraryMaskedReplay ExtendedSVCombIdempotence.
Module ExtendedSVRootFreeProducer.

Fixpoint root_free_lvalueb spec lv := match lv with
 | LVar _ root=>owns_rootb spec root
 | LSel _ base offset=>root_free_lvalueb spec base && output_free_exprb spec offset
 end.
Lemma root_free_owns spec lv : root_free_lvalueb spec lv=true->owns_rootb spec(lvalue_root lv)=true.
Proof.
 induction lv;cbn;[auto|]. intro H. apply andb_true_iff in H as [H _]. now apply IHlv.
Qed.
Lemma root_free_resolve spec lv s t : root_free_lvalueb spec lv=true->
 OutsideOutputs spec s t->resolve_lvalue s lv=resolve_lvalue t lv.
Proof.
 induction lv;cbn;intros HC HS;[reflexivity|].
 apply andb_true_iff in HC as [HB HE].
 rewrite (IHlv HB HS),(outside_outputs_eval spec _ s t HE HS). reflexivity.
Qed.
Fixpoint root_free_stmtb spec st := match st with
 | SSkip=>true
 | SAssign _ rhs lhs=>root_free_lvalueb spec lhs && output_free_exprb spec rhs
 | SSeq xs=>forallb (root_free_stmtb spec) xs
 | SIf guard yes no=>output_free_exprb spec guard && root_free_stmtb spec yes && root_free_stmtb spec no
 | SCase scr arms=>output_free_exprb spec scr &&
   forallb(fun arm=>output_free_keyb spec(fst arm)&&root_free_stmtb spec(snd arm))arms
 end.
Lemma selected_root_free spec s value arms default :
 forallb(fun arm=>output_free_keyb spec(fst arm)&&root_free_stmtb spec(snd arm))arms=true->
 root_free_stmtb spec default=true->root_free_stmtb spec(select_case_stmt s value arms default)=true.
Proof.
 induction arms as [|[key body]rest IH] in default|-*;cbn;[auto|].
 intros HC HD. apply andb_true_iff in HC as [HC HR]. apply andb_true_iff in HC as [HK HB].
 destruct key as [e|];[destruct(Z.eqb value(eval_expr s e))|];auto.
Qed.
Definition RootOwned spec u:=owns_rootb spec(update_signal u)=true.
Lemma matched_write_preserves_outside spec s t u : RootOwned spec u->OutsideOutputs spec s t->
 OutsideOutputs spec(apply_update s u)(apply_update t u).
Proof.
 intros HU HS r HR. assert(Hneq:update_signal u<>r)by(unfold RootOwned in HU;congruence).
 rewrite !read_signal_apply_update_other by exact Hneq. now apply HS.
Qed.
Definition RootCaptureAgreement spec es et :=
 OutsideOutputs spec(blocking_state es)(blocking_state et)/\
 pending_nba es=pending_nba et/\emitted_updates es=emitted_updates et/\
 Forall(RootOwned spec)(emitted_updates es).

Theorem root_free_execution spec fuel st es et :
 root_free_stmtb spec st=true->RootCaptureAgreement spec es et->
 RootCaptureAgreement spec(exec_stmt fuel st es)(exec_stmt fuel st et).
Proof.
 induction fuel as [|fuel IH] in st,es,et|-*;[auto|].
 destruct st as [|nba rhs lhs|xs|guard yes no|scr arms];cbn;intros HC HE.
 - exact HE.
 - apply andb_true_iff in HC as [HL HX]. destruct HE as [HB[HP[HU HT]]].
   assert(Hupdate:resolve_update(blocking_state es)lhs(eval_expr(blocking_state es)rhs)=
     resolve_update(blocking_state et)lhs(eval_expr(blocking_state et)rhs)).
   { unfold resolve_update. rewrite(root_free_resolve spec lhs _ _ HL HB),
      (outside_outputs_eval spec rhs _ _ HX HB). reflexivity. }
   assert(Howned:RootOwned spec(resolve_update(blocking_state es)lhs(eval_expr(blocking_state es)rhs))).
   { unfold RootOwned. rewrite resolve_update_root. now apply root_free_owns. }
   destruct nba;unfold RootCaptureAgreement;cbn.
   + split;[exact HB|]. split;[now rewrite Hupdate,HP|]. split;[now rewrite Hupdate,HU|].
     apply Forall_app. split;[exact HT|]. constructor;[exact Howned|constructor].
   + split.
     * rewrite <-Hupdate. now apply matched_write_preserves_outside.
     * split;[exact HP|]. split;[now rewrite Hupdate,HU|].
       apply Forall_app. split;[exact HT|]. constructor;[exact Howned|constructor].
 - induction xs as [|st xs IHr] in es,et,HC,HE|-*;cbn in *;[exact HE|].
   apply andb_true_iff in HC as [HS HR]. apply IHr;[exact HR|now apply IH].
 - apply andb_true_iff in HC as [HC HN]. apply andb_true_iff in HC as [HG HY].
   destruct HE as [HB[HP[HU HT]]].
   rewrite(outside_outputs_eval spec guard _ _ HG HB).
   destruct(Z.eqb(eval_expr(blocking_state et)guard)0);apply IH;
     [exact HN|repeat split;assumption|exact HY|repeat split;assumption].
 - apply andb_true_iff in HC as [HS HA]. destruct HE as [HB[HP[HU HT]]].
   rewrite(outside_outputs_eval spec scr _ _ HS HB).
   assert(HK:forallb(fun arm=>output_free_keyb spec(fst arm))arms=true).
   { apply forallb_forall. intros arm HI. apply forallb_forall with(x:=arm)in HA;[|exact HI].
     now apply andb_true_iff in HA as [HA _]. }
   rewrite(outputs_select_agree spec _ _ (eval_expr(blocking_state et)scr)arms SSkip HK HB).
   apply IH;[apply selected_root_free;[exact HA|reflexivity]|repeat split;assumption].
Qed.

Theorem root_free_captures spec p proc s t : root_free_stmtb spec(process_body proc)=true->
 OutsideOutputs spec s t->process_updates p s proc=process_updates p t proc/\
 Forall(RootOwned spec)(process_updates p s proc).
Proof.
 intros HC HS. unfold process_updates.
 assert(HI:RootCaptureAgreement spec
   {|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|}
   {|blocking_state:=t;pending_nba:=[];emitted_updates:=[]|}).
 { repeat split;auto;constructor. }
 destruct(root_free_execution spec(statement_fuel p)(process_body proc)_ _ HC HI)as[HB[HP HU]]. exact HU.
Qed.
Lemma root_owned_replay_preserves_outside spec updates : Forall(RootOwned spec)updates->
 forall s,OutsideOutputs spec(apply_updates s updates)s.
Proof.
 intro H. induction H;intros s r HR;cbn;[reflexivity|]. rewrite IHForall by exact HR.
 rewrite read_signal_apply_update_other;[reflexivity|]. unfold RootOwned in H. congruence.
Qed.
Theorem root_free_producer_sound spec p proc : root_free_stmtb spec(process_body proc)=true->
 blocking_onlyb(process_body proc)||nba_onlyb(process_body proc)=true->ProducerIdempotent p proc.
Proof.
 intros HC HK s.
 assert(Hreplay:forall state,run_process p state proc=apply_updates state(process_updates p state proc)).
 { intro state. apply orb_true_iff in HK as [HB|HN].
   - now apply actual_blocking_process_replays.
   - now apply actual_nba_process_replays. }
 destruct(root_free_captures spec p proc s s HC(fun r HR=>eq_refl))as[_ HT].
 rewrite !Hreplay.
 destruct(root_free_captures spec p proc (apply_updates s(process_updates p s proc))s HC
   (root_owned_replay_preserves_outside spec _ HT s))as[HE _].
 rewrite HE. apply arbitrary_captured_replay_is_idempotent.
Qed.
Definition root_free_producerb proc :=
 let body:=process_body proc in
 (blocking_onlyb body||nba_onlyb body)&&
 root_free_stmtb(map(fun root=>(0%nat,root))(stmt_writers body))body.
Theorem checked_root_free_producer p proc : root_free_producerb proc=true->ProducerIdempotent p proc.
Proof.
 unfold root_free_producerb. intro H. apply andb_true_iff in H as [HK HC].
 exact(root_free_producer_sound _ p proc HC HK).
Qed.
End ExtendedSVRootFreeProducer.
Print Assumptions ExtendedSVRootFreeProducer.root_free_captures.
Print Assumptions ExtendedSVRootFreeProducer.root_free_producer_sound.
Print Assumptions ExtendedSVRootFreeProducer.checked_root_free_producer.
