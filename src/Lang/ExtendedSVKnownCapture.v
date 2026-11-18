(** Definite assignment also certifies equality of captured updates, not just
    final normalized outputs. Original intra-process reads are retained. *)
From Coq Require Import List Bool ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVKnownInputs Lang.ExtendedSVExprAgreement.
Import ListNotations ExtendedSV ExtendedSVKnownInputs ExtendedSVExprAgreement.
Module ExtendedSVKnownCapture.

Theorem actual_known_execution_updates fuel known st output es et :
 infer_known fuel known st=Some output ->
 InputsAgree (blocking_state es) (blocking_state et) known ->
 emitted_updates es=emitted_updates et ->
 emitted_updates (exec_stmt fuel st es)=emitted_updates (exec_stmt fuel st et).
Proof.
 induction fuel as [|fuel IH] in known,st,output,es,et |- *;
   [cbn; intros HC HA HU; exact HU|].
 destruct st as [|nba e l|xs|g a b|scr arms]; cbn [infer_known exec_stmt]; intros HC HA HU.
 - exact HU.
 - destruct nba,l as [w r|]; try discriminate.
   destruct (known_expr known e) eqn:HE; [|discriminate].
   assert (HV:eval_expr (blocking_state es) e=eval_expr (blocking_state et) e).
   { apply eval_expr_agree. exact (contains_agree _ _ _ _ HE HA). }
   cbn [emitted_updates resolve_update resolve_lvalue]. rewrite HU,HV. reflexivity.
 - induction xs as [|x xs IHr] in known,output,es,et,HC,HA,HU |- *; cbn in *.
   + exact HU.
   + destruct (infer_known fuel known x) as [k|] eqn:HX.
     * apply IHr with (known:=k) (output:=output); [exact HC| |].
       -- exact (actual_known_execution fuel known x k es et HX HA).
       -- exact (IH known x k es et HX HA HU).
     * assert (Hnone:forall ys,fold_left (fun acc st=>match acc with
         Some k=>infer_known fuel k st|None=>None end) ys None=None).
       { intro ys. induction ys; cbn; auto. }
       rewrite Hnone in HC. discriminate.
 - destruct (known_expr known g) eqn:HG; [|discriminate].
   destruct (infer_known fuel known a) as [ka|] eqn:HAk; [|discriminate].
   destruct (infer_known fuel known b) as [kb|] eqn:HBk; [|discriminate].
   destruct (containsb ka known&&containsb kb known) eqn:HK; [|discriminate].
   rewrite (eval_expr_agree g (blocking_state es) (blocking_state et)
     (contains_agree _ _ _ _ HG HA)).
   destruct (Z.eqb (eval_expr (blocking_state et) g) 0).
   + exact (IH known b kb es et HBk HA HU).
   + exact (IH known a ka es et HAk HA HU).
 - destruct (known_expr known scr&&forallb (fun arm=>known_key known (fst arm)&&
     match infer_known fuel known (snd arm) with Some k=>containsb k known|None=>false end) arms)
     eqn:HG; [|discriminate].
   apply andb_true_iff in HG as [HS HK].
   assert (Hkeys:forallb (fun arm=>known_key known (fst arm)) arms=true).
   { apply forallb_forall. intros arm HI. apply forallb_forall with (x:=arm) in HK; [|exact HI].
     now apply andb_true_iff in HK as [HK _]. }
   rewrite (eval_expr_agree scr (blocking_state es) (blocking_state et)
       (contains_agree _ _ _ _ HS HA)),
     (selected_known_case_same known (blocking_state es) (blocking_state et)
       (eval_expr (blocking_state et) scr) arms SSkip Hkeys HA).
   destruct (selected_known_case_safe fuel known (blocking_state et)
       (eval_expr (blocking_state et) scr) arms SSkip HK) as [k [HI HO]].
   + exists known. split; [destruct fuel; reflexivity|apply contains_refl].
   + exact (IH known _ k es et HI HA HU).
Qed.

Theorem actual_known_captured_updates p proc known output s t :
 infer_known (statement_fuel p) known (process_body proc)=Some output ->
 InputsAgree s t known -> process_updates p s proc=process_updates p t proc.
Proof.
 intros HC HA. unfold process_updates.
 exact (actual_known_execution_updates (statement_fuel p) known (process_body proc) output
   {|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|}
   {|blocking_state:=t;pending_nba:=[];emitted_updates:=[]|} HC HA eq_refl).
Qed.
End ExtendedSVKnownCapture.
Print Assumptions ExtendedSVKnownCapture.actual_known_execution_updates.
Print Assumptions ExtendedSVKnownCapture.actual_known_captured_updates.
