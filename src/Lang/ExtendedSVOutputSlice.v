(** Checked output-sensitive pruning of actual blocking statement execution.
    A discarded statement must leave every retained dependency unchanged. *)
From Coq Require Import List Bool PeanoNat ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVExprAgreement
 Lang.ExtendedSVBlocking.
Import ExtendedSV ExtendedSVRootProjection ExtendedSVExprAgreement ExtendedSVBlocking ListNotations.
Module ExtendedSVOutputSlice.
Definition RootAgree (roots:list signal)(s t:State):=forall r,In r roots->read_signal s r=read_signal t r.
Definition reads_withinb roots e:=forallb(fun wr=>existsb(Nat.eqb(snd wr))roots)(expr_inputs e).
Definition key_withinb roots key:=match key with None=>true|Some e=>reads_withinb roots e end.
Definition writes_targetb targets st:=existsb(fun r=>existsb(Nat.eqb r)targets)(stmt_writers st).
Definition erases_safelyb roots st:=forallb(fun r=>negb(existsb(Nat.eqb r)roots))(stmt_writers st).
Fixpoint output_slice fuel root st:=match fuel with
 |O=>SSkip|S n=>if writes_targetb root st then match st with
 |SSkip=>SSkip|SAssign nba e l=>SAssign nba e l
 |SSeq xs=>SSeq(map(output_slice n root)xs)
 |SIf g a b=>SIf g(output_slice n root a)(output_slice n root b)
 |SCase e arms=>SCase e(map(fun arm=>(fst arm,output_slice n root(snd arm)))arms)
 end else SSkip end.
Fixpoint output_slice_safeb fuel root roots st:=match fuel with
 |O=>true|S n=>if writes_targetb root st then match st with
 |SSkip=>true
 |SAssign nba e(LVar _ r)=>negb nba&&existsb(Nat.eqb r)root&&reads_withinb roots e
 |SAssign _ _ _=>false
 |SSeq xs=>forallb(output_slice_safeb n root roots)xs
 |SIf g a b=>reads_withinb roots g&&output_slice_safeb n root roots a&&output_slice_safeb n root roots b
 |SCase e arms=>reads_withinb roots e&&forallb(fun arm=>key_withinb roots(fst arm)&&output_slice_safeb n root roots(snd arm))arms
 end else erases_safelyb roots st end.
Lemma read_within_agree roots e s t : reads_withinb roots e=true->RootAgree roots s t->eval_expr s e=eval_expr t e.
Proof.
 intros HE HS. apply eval_expr_agree. intros w r HR.
 apply forallb_forall with(x:=(w,r))in HE;[|exact HR].
 apply existsb_exists in HE as[r'[HI HE]]. cbn in HE. apply Nat.eqb_eq in HE. subst r'.
 now rewrite HS by exact HI.
Qed.
Lemma erased_preserves roots st fuel es : erases_safelyb roots st=true->
 RootAgree roots(blocking_state(exec_stmt fuel st es))(blocking_state es).
Proof.
 intros H r HR. apply exec_stmt_preserves_unwritten_root. intro HW.
 apply forallb_forall with(x:=r)in H;[|exact HW].
 apply negb_true_iff in H. assert(existsb(Nat.eqb r)roots=true).
 { apply existsb_exists. exists r. split;[exact HR|apply Nat.eqb_refl]. } congruence.
Qed.
Lemma slice_case_selection fuel root roots s t value arms default :
 forallb(fun arm=>key_withinb roots(fst arm))arms=true->RootAgree roots s t->
 output_slice fuel root(select_case_stmt s value arms default)=
 select_case_stmt t value(map(fun arm=>(fst arm,output_slice fuel root(snd arm)))arms)(output_slice fuel root default).
Proof.
 induction arms as[|[key body]rest IH]in default|-*;cbn;[auto|].
 intros HC HS. apply andb_true_iff in HC as[HK HR].
 destruct key as[e|];cbn in *.
 - rewrite(read_within_agree roots e s t HK HS). destruct(Z.eqb value(eval_expr t e));[reflexivity|now apply IH].
 - now apply IH.
Qed.
Lemma selected_slice_safe fuel root roots s value arms default :
 forallb(fun arm=>key_withinb roots(fst arm)&&output_slice_safeb fuel root roots(snd arm))arms=true->
 output_slice_safeb fuel root roots default=true->
 output_slice_safeb fuel root roots(select_case_stmt s value arms default)=true.
Proof.
 induction arms as[|[key body]rest IH]in default|-*;cbn;intros HC HD;[exact HD|].
 apply andb_true_iff in HC as[HB HR]. apply andb_true_iff in HB as[HK HF].
 destruct key as[e|];[destruct(Z.eqb value(eval_expr s e))|];auto.
Qed.
Theorem actual_output_slice_execution fuel root roots st es et :
 output_slice_safeb fuel root roots st=true ->RootAgree roots(blocking_state es)(blocking_state et)->
 RootAgree roots(blocking_state(exec_stmt fuel st es))
 (blocking_state(exec_stmt fuel(output_slice fuel root st)et)).
Proof.
 induction fuel as[|fuel IH]in st,es,et|-*;[auto|].
 cbn[output_slice_safeb output_slice]. destruct(writes_targetb root st)eqn:HW.
 2:{ intros HC HE r HR.
     change(read_signal(blocking_state(exec_stmt(S fuel)st es))r=read_signal(blocking_state et)r).
     rewrite(erased_preserves roots st(S fuel)es HC r HR). now apply HE. }
 destruct st as[|nba e l|xs|g a b|scr arms];cbn;intros HC HE.
 - exact HE.
 - destruct l as[w r|];[|discriminate].
   apply andb_true_iff in HC as[HC HX]. apply andb_true_iff in HC as[HN HR].
   destruct nba;[discriminate|].
   rewrite(read_within_agree roots e(blocking_state es)(blocking_state et)HX HE).
   intros q HQ. unfold apply_update. cbn[resolve_update resolve_lvalue update_signal update_offset update_width update_value blocking_state].
   destruct(Nat.eq_dec r q)as[<-|Hneq].
   + rewrite !read_signal_write_same. now rewrite HE by exact HQ.
   + rewrite !read_signal_write_other by exact Hneq. now apply HE.
 - induction xs as[|x xs IHr]in es,et,HC,HE|-*;cbn in *;[exact HE|].
   apply andb_true_iff in HC as[HX HT]. apply IHr;[exact HT|now apply IH].
 - apply andb_true_iff in HC as[HC HB]. apply andb_true_iff in HC as[HG HA].
   rewrite(read_within_agree roots g(blocking_state es)(blocking_state et)HG HE).
   destruct(Z.eqb(eval_expr(blocking_state et)g)0);apply IH;assumption.
 - apply andb_true_iff in HC as[HG HA].
   rewrite(read_within_agree roots scr(blocking_state es)(blocking_state et)HG HE).
   assert(HK:forallb(fun arm=>key_withinb roots(fst arm))arms=true).
   { apply forallb_forall. intros arm HI. apply forallb_forall with(x:=arm)in HA;[|exact HI]. now apply andb_true_iff in HA as[HK _]. }
   pose proof(slice_case_selection fuel root roots(blocking_state es)(blocking_state et)
    (eval_expr(blocking_state et)scr)arms SSkip HK HE)as Hselect.
   assert(Hskip:output_slice fuel root SSkip=SSkip)by(destruct fuel;reflexivity).
   rewrite Hskip in Hselect. rewrite <-Hselect.
   apply IH;[apply selected_slice_safe;[exact HA|destruct fuel;reflexivity]|exact HE].
Qed.
Print Assumptions actual_output_slice_execution.
Definition sliced_process p root proc : Process:=
 {|process_kind:=process_kind proc;process_events:=process_events proc;
 process_body:=output_slice(statement_fuel p)root(process_body proc);
 process_source_line:=process_source_line proc|}.
Theorem actual_output_slice_process p root roots proc s :
 output_slice_safeb(statement_fuel p)root roots(process_body proc)=true ->
 blocking_onlyb(process_body proc)=true ->
 blocking_onlyb(process_body(sliced_process p root proc))=true ->
 RootAgree roots(run_process p s proc)(run_process p s(sliced_process p root proc)).
Proof.
 intros HC HB HS. rewrite !blocking_run_process by assumption.
 apply actual_output_slice_execution;[exact HC|intros r HR;reflexivity].
Qed.
Theorem actual_output_slice_dependency p targets roots proc s t :
 output_slice_safeb(statement_fuel p)targets roots(process_body proc)=true ->
 blocking_onlyb(process_body proc)=true ->
 blocking_onlyb(process_body(sliced_process p targets proc))=true ->
 RootAgree roots s t ->RootAgree roots(run_process p s proc)(run_process p t proc).
Proof.
 intros HC HB HS HE r HR.
 pose proof(actual_output_slice_process p targets roots proc t HC HB HS r HR)as HT.
 rewrite HT. rewrite !blocking_run_process by assumption.
 exact(actual_output_slice_execution(statement_fuel p)targets roots(process_body proc)
 {|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|}
 {|blocking_state:=t;pending_nba:=[];emitted_updates:=[]|}HC HE r HR).
Qed.
End ExtendedSVOutputSlice.
