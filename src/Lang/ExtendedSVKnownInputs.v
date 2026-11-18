(** Checked definite assignment for normalized scalar inputs. A successful
    analysis proves actual execution agreement, not guessed dependency edges. *)
From Coq Require Import List Bool PeanoNat ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVExprAgreement Lang.ExtendedSVAssignment
 Lang.ExtendedSVWordInvariant Lang.ExtendedSVBlocking.
Import ExtendedSV ExtendedSVExprAgreement ExtendedSVAssignment ExtendedSVWordInvariant ExtendedSVBlocking ListNotations.
Module ExtendedSVKnownInputs.
Definition Wire:= (nat*signal)%type.
Definition wire_eqb(a b:Wire):=Nat.eqb(fst a)(fst b)&&Nat.eqb(snd a)(snd b).
Definition containsb (known requested:list Wire):=forallb(fun wr=>existsb(wire_eqb wr)known)requested.
Lemma contains_sound known requested : containsb known requested=true->forall wr,In wr requested->In wr known.
Proof.
 intros H [w r] HI. apply forallb_forall with(x:=(w,r))in H;[|exact HI].
 apply existsb_exists in H as[[w' r'][Hin HE]]. cbn in HE.
 apply andb_true_iff in HE as[HW HR]. apply Nat.eqb_eq in HW,HR. cbn in HW,HR. subst. exact Hin.
Qed.
Lemma contains_agree known requested s t : containsb known requested=true->InputsAgree s t known->InputsAgree s t requested.
Proof. intros HC HA w r HI. apply HA. exact(contains_sound _ _ HC(w,r)HI). Qed.
Definition known_expr known e:=containsb known(expr_inputs e).
Definition known_key known key:=match key with None=>true|Some e=>known_expr known e end.
Definition assigned_known(known:list Wire)(w r:nat):=(w,r)::filter(fun wr=>negb(Nat.eqb(snd wr)r))known.
Fixpoint infer_known fuel known st : option(list Wire):=match fuel with
 |O=>Some known|S n=>match st with
 |SSkip=>Some known
 |SAssign false e(LVar w r)=>if known_expr known e then Some(assigned_known known w r)else None
 |SAssign _ _ _=>None
 |SSeq xs=>fold_left(fun acc st=>match acc with Some k=>infer_known n k st|None=>None end)xs(Some known)
 |SIf g a b=>if known_expr known g then
    match infer_known n known a,infer_known n known b with
    |Some ka,Some kb=>if containsb ka known&&containsb kb known then Some known else None
    |_,_=>None end else None
 |SCase e arms=>if known_expr known e&&forallb(fun arm=>known_key known(fst arm)&&
    match infer_known n known(snd arm)with Some k=>containsb k known|None=>false end)arms
    then Some known else None
 end end.
Lemma scalar_assignment_agree known w r e s t : known_expr known e=true->InputsAgree s t known->
 InputsAgree(apply_update s(resolve_update s(LVar w r)(eval_expr s e)))
 (apply_update t(resolve_update t(LVar w r)(eval_expr t e)))(assigned_known known w r).
Proof.
 intros HE HA ww rr HI. assert(HV:eval_expr s e=eval_expr t e).
 { apply eval_expr_agree. exact(contains_agree _ _ _ _ HE HA). }
 rewrite HV. destruct HI as[HI|HI].
 - inversion HI;subst ww rr. unfold apply_update,resolve_update;cbn[resolve_lvalue update_signal update_offset update_width update_value].
   rewrite !read_signal_write_same,!norm_full_low_write. reflexivity.
 - apply filter_In in HI as[HI HN]. apply negb_true_iff in HN. apply Nat.eqb_neq in HN. cbn in HN.
   unfold apply_update,resolve_update;cbn[resolve_lvalue update_signal update_offset update_width update_value].
   rewrite !read_signal_write_other by congruence. now apply HA.
Qed.
Lemma selected_known_case_same known s t value arms default :
 forallb(fun arm=>known_key known(fst arm))arms=true->InputsAgree s t known->
 select_case_stmt s value arms default=select_case_stmt t value arms default.
Proof.
 induction arms as[|[key body]rest IH]in default|-*;cbn;[auto|].
 intros HC HA. apply andb_true_iff in HC as[HK HR]. destruct key as[e|];cbn in *.
 - rewrite(eval_expr_agree e s t(contains_agree _ _ _ _ HK HA)).
   destruct(Z.eqb value(eval_expr t e));[reflexivity|now apply IH].
 - now apply IH.
Qed.
Lemma selected_known_case_safe fuel known s value arms default :
 forallb(fun arm=>known_key known(fst arm)&&match infer_known fuel known(snd arm)with Some k=>containsb k known|None=>false end)arms=true->
 (exists k,infer_known fuel known default=Some k/\containsb k known=true)->
 exists k,infer_known fuel known(select_case_stmt s value arms default)=Some k/\containsb k known=true.
Proof.
 induction arms as[|[key body]rest IH]in default|-*;cbn;intros HC HD;[exact HD|].
 apply andb_true_iff in HC as[HB HR]. apply andb_true_iff in HB as[HK HF].
 assert(Hbody:exists k,infer_known fuel known body=Some k/\containsb k known=true).
 { destruct(infer_known fuel known body)eqn:H;[eauto|discriminate]. }
 destruct key as[e|];[destruct(Z.eqb value(eval_expr s e))|];auto.
Qed.
Lemma contains_refl known : containsb known known=true.
Proof. apply forallb_forall. intros [w r] HI. apply existsb_exists. exists(w,r). split;[exact HI|unfold wire_eqb;cbn;now rewrite !Nat.eqb_refl]. Qed.
Theorem actual_known_execution fuel known st output es et :
 infer_known fuel known st=Some output->InputsAgree(blocking_state es)(blocking_state et)known->
 InputsAgree(blocking_state(exec_stmt fuel st es))(blocking_state(exec_stmt fuel st et))output.
Proof.
 induction fuel as[|fuel IH]in known,st,output,es,et|-*;[cbn;intros H HA;inversion H;subst;exact HA|].
 destruct st as[|nba e l|xs|g a b|scr arms];cbn[infer_known exec_stmt];intros HC HA.
 - inversion HC;subst;exact HA.
 - destruct nba,l as[w r|];try discriminate.
   destruct(known_expr known e)eqn:HE;[|discriminate]. inversion HC;subst output.
   apply scalar_assignment_agree;assumption.
 - induction xs as[|x xs IHr]in known,output,es,et,HC,HA|-*;cbn in *.
   + inversion HC;subst;exact HA.
   + destruct(infer_known fuel known x)as[k|]eqn:HX.
     * apply IHr with(known:=k);[exact HC|now apply IH with(known:=known)].
     * assert(Hnone:forall ys,fold_left(fun acc st=>match acc with Some k=>infer_known fuel k st|None=>None end)ys None=None).
       { intro ys. induction ys;cbn;auto. }
       rewrite Hnone in HC. discriminate.
 - destruct(known_expr known g)eqn:HG;[|discriminate].
   destruct(infer_known fuel known a)as[ka|]eqn:HAk;[|discriminate].
   destruct(infer_known fuel known b)as[kb|]eqn:HBk;[|discriminate].
   destruct(containsb ka known&&containsb kb known)eqn:HK;[|discriminate]. inversion HC;subst output.
   apply andb_true_iff in HK as[HK1 HK2].
   rewrite(eval_expr_agree g(blocking_state es)(blocking_state et)(contains_agree _ _ _ _ HG HA)).
   destruct(Z.eqb(eval_expr(blocking_state et)g)0).
   + eapply contains_agree;[exact HK2|eapply IH;[exact HBk|exact HA]].
   + eapply contains_agree;[exact HK1|eapply IH;[exact HAk|exact HA]].
 - destruct(known_expr known scr&&forallb(fun arm=>known_key known(fst arm)&&
    match infer_known fuel known(snd arm)with Some k=>containsb k known|None=>false end)arms)eqn:HG;[|discriminate].
   inversion HC;subst output. apply andb_true_iff in HG as[HS HK].
   assert(Hkeys:forallb(fun arm=>known_key known(fst arm))arms=true).
   { apply forallb_forall. intros arm HI. apply forallb_forall with(x:=arm)in HK;[|exact HI]. now apply andb_true_iff in HK as[HK _]. }
   rewrite(eval_expr_agree scr(blocking_state es)(blocking_state et)(contains_agree _ _ _ _ HS HA)),
    (selected_known_case_same known(blocking_state es)(blocking_state et)
      (eval_expr(blocking_state et)scr)arms SSkip Hkeys HA).
   destruct(selected_known_case_safe fuel known(blocking_state et)(eval_expr(blocking_state et)scr)arms SSkip HK)
    as[k[HI HO]];[exists known;split;[destruct fuel;reflexivity|apply contains_refl]|].
   eapply contains_agree;[exact HO|eapply IH;[exact HI|exact HA]].
Qed.
Print Assumptions actual_known_execution.
Theorem actual_known_process p proc known output s t :
 infer_known(statement_fuel p)known(process_body proc)=Some output ->
 blocking_onlyb(process_body proc)=true ->InputsAgree s t known ->
 InputsAgree(run_process p s proc)(run_process p t proc)output.
Proof. intros HC HB HA. rewrite !blocking_run_process by exact HB. now apply actual_known_execution with(known:=known). Qed.
End ExtendedSVKnownInputs.
