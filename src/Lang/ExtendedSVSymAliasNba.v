(** Data-flow equations of combinational processes whose assignments are all non-blocking (template route, 2026-11-03).

    Generic, design independent, additive to [ExtendedSVSymAlias] (which is not modified).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.

    A combinational block [always] with a star sensitivity list written with [<=] (for example an immediate decoder, a case on the opcode with
    one non-blocking assignment per arm) is executed by [run_process] as: blocking state never changes, the updates are
    queued and applied at the end.  [pexn] follows the path decided by CONSTANT facts exactly like [pex] and records each
    non-blocking assignment as the equation [norm w r = norm w (eval rhs')]; all right-hand sides and guards are evaluated in
    the state the process starts in, which is what the blocking state still is.  A later queued write to the same
    root replaces the equation.  [pexany] tries [pex] first.  [eqchain2] is [ExtendedSVSymAlias.eqchain] with [pexany]. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVConstantRoot
 Lang.ExtendedSVCombConnection Lang.ExtendedSVCombCut Lang.ExtendedSVAssignment Lang.ExtendedSVExprAgreement
 Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVWordInvariant Lang.ExtendedSVSymAlias.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVConstantRoot
 ExtendedSVCombConnection ExtendedSVCombCut ExtendedSVAssignment ExtendedSVExprAgreement
 ExtendedSVSymExec ExtendedSVFactChain ExtendedSVWordInvariant ExtendedSVSymAlias.
Local Open Scope Z_scope.
Module ExtendedSVSymAliasNba.

Fixpoint pexn (F:Facts) (fuel:nat) (st:Stmt) (acc:list Eqn) {struct fuel} : option (list Eqn) :=
 match fuel with
 | O => Some acc
 | S f =>
  match st with
  | SSkip => Some acc
  | SAssign true rhs (LVar w r) => Some ((w,r,simp F rhs)::drop_root r acc)
  | SAssign _ _ _ => None
  | SSeq l => fold_left (fun o st' => match o with Some acc' => pexn F f st' acc' | None => None end) l (Some acc)
  | SIf g y n => match xeval F [] g with
     | Some z => pexn F f (if Z.eqb z 0 then n else y) acc | None => None end
  | SCase scr arms => match xeval F [] scr with
     | Some v => match cselect F [] v arms SSkip with
        | Some c => pexn F f c acc | None => None end
     | None => None end
  end
 end.

Definition pexany (F:Facts) (fuel:nat) (body:Stmt) : option (list Eqn) :=
 match pex F fuel (nbfix body) [] [] with
 | Some (_,acc) => Some acc
 | None => pexn F fuel body []
 end.

Section Sound.
Variable F : Facts.
Variable s0 : State.
Hypothesis HF : FactsHold s0 F.

Definition NbaAgree (acc:list Eqn) (pend:list Update) : Prop :=
 forall w r e, In (w,r,e) acc -> forall s, norm w (read_signal (apply_nba s pend) r) = norm w (eval_expr s0 e).

Lemma apply_nba_app s l1 l2 : apply_nba s (l1 ++ l2) = apply_nba (apply_nba s l1) l2.
Proof. revert s. induction l1 as [|u rest IH]; intro s; cbn [apply_nba app]; [reflexivity|apply IH]. Qed.

Lemma upd_same s' s w r v : norm w (read_signal (apply_update s' (resolve_update s (LVar w r) v)) r) = norm w v.
Proof.
 unfold apply_update, resolve_update. cbn [resolve_lvalue update_signal update_offset update_width update_value].
 rewrite read_signal_write_same, norm_full_low_write. unfold norm. rewrite <- Z.land_assoc, Z.land_diag. reflexivity.
Qed.
Lemma upd_other s' s w r r' v : r' <> r -> read_signal (apply_update s' (resolve_update s (LVar w r) v)) r' = read_signal s' r'.
Proof.
 intro H. unfold apply_update, resolve_update. cbn [resolve_lvalue update_signal update_offset update_width update_value].
 rewrite read_signal_write_other by congruence. reflexivity.
Qed.

Lemma nba_agree_snoc acc pend w r rhs :
 NbaAgree acc pend ->
 NbaAgree ((w,r,simp F rhs)::drop_root r acc) (pend ++ [resolve_update s0 (LVar w r) (eval_expr s0 rhs)]).
Proof.
 intros H w' r' e' Hin s. rewrite apply_nba_app. cbn [apply_nba].
 destruct Hin as [Hin|Hin].
 - inversion Hin; subst. rewrite upd_same. rewrite (simp_sound F s0 HF rhs). reflexivity.
 - unfold drop_root in Hin. apply filter_In in Hin as [Hin Hneq]. cbn [snd fst] in Hneq.
   apply negb_true_iff in Hneq. apply Nat.eqb_neq in Hneq.
   rewrite upd_other by congruence. exact (H _ _ _ Hin s).
Qed.

Lemma pexn_fold_none : forall (l:list Stmt) f, fold_left (fun o st' => match o with Some acc' => pexn F f st' acc' | None => None end) l None = None.
Proof. induction l; intros; cbn; [reflexivity|apply IHl]. Qed.

Theorem pexn_sound : forall fuel st acc acc' es,
 pexn F fuel st acc = Some acc' -> blocking_state es = s0 -> NbaAgree acc (pending_nba es) ->
 blocking_state (exec_stmt fuel st es) = s0 /\ NbaAgree acc' (pending_nba (exec_stmt fuel st es)).
Proof.
 induction fuel as [|f IH]; intros st acc acc' es H HB HA.
 - cbn in H. inversion H; subst. cbn. split; assumption.
 - destruct st as [|nba rhs lhs|l|g y n|scr arms]; cbn [pexn exec_stmt] in *.
   + inversion H; subst. split; assumption.
   + destruct nba; [|discriminate]. destruct lhs as [w r|]; [|discriminate]. inversion H; subst; clear H.
     cbn [blocking_state pending_nba]. rewrite HB. split; [reflexivity|]. apply nba_agree_snoc. exact HA.
   + assert (Hgen: forall l acc acc' es,
        fold_left (fun o st' => match o with Some acc' => pexn F f st' acc' | None => None end) l (Some acc) = Some acc' ->
        blocking_state es = s0 -> NbaAgree acc (pending_nba es) ->
        blocking_state (fold_left (fun es' st' => exec_stmt f st' es') l es) = s0 /\
        NbaAgree acc' (pending_nba (fold_left (fun es' st' => exec_stmt f st' es') l es))).
     { induction l0 as [|a rest IHl]; intros acc0 acc1 es0 H0 HB0 HA0.
       - cbn in H0. inversion H0; subst. cbn. split; assumption.
       - cbn [fold_left] in H0 |- *. cbn in H0.
         destruct (pexn F f a acc0) as [a1|] eqn:Ea; [|rewrite pexn_fold_none in H0; discriminate].
         destruct (IH _ _ _ es0 Ea HB0 HA0) as [HB1 HA1].
         exact (IHl _ _ _ H0 HB1 HA1). }
     exact (Hgen l acc acc' es H HB HA).
   + destruct (xeval F [] g) as [z|] eqn:Ez; [|discriminate].
     rewrite HB. rewrite (xeval_sound F s0 HF g [] s0 z (agree_nil s0) Ez).
     destruct (Z.eqb z 0); exact (IH _ _ _ _ H HB HA).
   + destruct (xeval F [] scr) as [v|] eqn:Ev; [|discriminate].
     destruct (cselect F [] v arms SSkip) as [c|] eqn:Ec; [|discriminate].
     rewrite HB. rewrite (xeval_sound F s0 HF scr [] s0 v (agree_nil s0) Ev).
     assert (Hsel : select_case_stmt s0 v arms SSkip = c).
     { exact (cselect_sound F s0 HF arms [] [] s0 v SSkip c (conj (fun r _ => eq_refl) (fun _ _ _ H0 => False_ind _ H0)) Ec). }
     rewrite Hsel. exact (IH _ _ _ _ H HB HA).
Qed.

Theorem prunn_sound p proc acc :
 pexn F (statement_fuel p) (process_body proc) [] = Some acc ->
 forall w r e, In (w,r,e) acc -> norm w (read_signal (run_process p s0 proc) r) = norm w (eval_expr s0 e).
Proof.
 intros H w r e Hin. unfold run_process.
 destruct (pexn_sound (statement_fuel p) (process_body proc) [] acc
   {|blocking_state:=s0;pending_nba:=[];emitted_updates:=[]|} H eq_refl
   (fun w0 r0 e0 H0 => False_ind _ H0)) as [HB HA].
 rewrite HB. exact (HA w r e Hin s0).
Qed.

Theorem prunany_sound p proc acc :
 pexany F (statement_fuel p) (process_body proc) = Some acc ->
 forall w r e, In (w,r,e) acc -> norm w (read_signal (run_process p s0 proc) r) = norm w (eval_expr s0 e).
Proof.
 unfold pexany. intros H w r e Hin.
 destruct (pex F (statement_fuel p) (nbfix (process_body proc)) [] []) as [[ov acc0]|] eqn:Hx.
 - inversion H; subst. exact (prun_sound F s0 HF p proc ov acc Hx w r e Hin).
 - exact (prunn_sound p proc acc H w r e Hin).
Qed.
End Sound.

(** ---- transfer to the combinational fixed point ---- *)
Theorem prunany_comb_lfp p ps T k proc F acc seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc ->
 facts_inputs_okb F T k = true ->
 FactsHold fixed F -> CombLFP p seed fixed ->
 pexany F (statement_fuel p) (process_body proc) = Some acc ->
 forall w r e, In (w,r,e) (filter (eq_okb T k) acc) -> norm w (read_signal fixed r) = norm w (eval_expr fixed e).
Proof.
 intros HP HT HN Hok HFH HL Hx w r e Hin.
 apply filter_In in Hin as [Hin Hq]. unfold eq_okb in Hq. cbn [snd fst] in Hq.
 apply andb_true_iff in Hq as [Hr Hq].
 pose proof (eq_trans HP (split_at ps k proc HN)) as Horder.
 rewrite (actual_lfp_pivot_output p (firstn k ps) proc (skipn (S k) ps) r seed fixed Horder (unw_suffix ps T (S k) r HT Hr) HL).
 assert (HF0 : FactsHold (fold_left (run_process p) (firstn k ps) fixed) F).
 { intros e0 zz HI. unfold FactsHold in HFH.
   rewrite <- (HFH e0 zz HI). apply eval_expr_agree. intros wd x Hin'.
   unfold facts_inputs_okb in Hok. rewrite forallb_forall in Hok.
   specialize (Hok (e0,zz) HI). cbn [fst] in Hok. rewrite forallb_forall in Hok.
   specialize (Hok (wd,x) Hin'). cbn [snd] in Hok.
   apply orb_true_iff in Hok as [Hok|Hok].
   - rewrite (fold_run_process_preserves_root p (firstn k ps) x fixed (roots_unwrittenb_sound _ _ (unw_prefix ps T k x HT Hok))). reflexivity.
   - rewrite (actual_lfp_pivot_input p (firstn k ps) proc (skipn (S k) ps) x seed fixed Horder
       (eq_ind (skipn k ps) (fun l => roots_unwrittenb x l = true) (unw_suffix ps T k x HT Hok) _ (skipn_nth_cons ps k proc HN)) HL). reflexivity. }
 rewrite (prunany_sound F _ HF0 p proc acc Hx w r e Hin).
 f_equal. apply eval_expr_agree. intros wd x Hin'.
 rewrite forallb_forall in Hq. specialize (Hq (wd,x) Hin'). cbn [snd] in Hq.
 apply orb_true_iff in Hq as [Hq|Hq].
 - rewrite (fold_run_process_preserves_root p (firstn k ps) x fixed (roots_unwrittenb_sound _ _ (unw_prefix ps T k x HT Hq))). reflexivity.
 - rewrite (actual_lfp_pivot_input p (firstn k ps) proc (skipn (S k) ps) x seed fixed Horder
     (eq_ind (skipn k ps) (fun l => roots_unwrittenb x l = true) (unw_suffix ps T k x HT Hq) _ (skipn_nth_cons ps k proc HN)) HL). reflexivity.
Qed.

Definition step_eqs2 (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (st:nat*list nat) : option (list Eqn) :=
 let k := fst st in
 match nth_error ps k with
 | None => None
 | Some proc =>
   match pexany (filter (tail_okb T k) (pick F (snd st))) fuel (process_body proc) with
   | None => None
   | Some acc => Some (filter (eq_okb T k) acc)
   end
 end.

Fixpoint eqchain2 (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (ks:list (nat*list nat)) : option (list Eqn) :=
 match ks with
 | [] => Some []
 | k::rest => match step_eqs2 ps T fuel F k with
    | Some E => match eqchain2 ps T fuel F rest with Some E' => Some (E ++ E') | None => None end
    | None => None end
 end.

Theorem eqchain2_sound p ps T fuel (ks:list (nat*list nat)) : forall F E seed fixed,
 filter is_comb (processes p) = ps -> TabC ps T -> fuel = statement_fuel p ->
 FactsHold fixed F -> CombLFP p seed fixed -> eqchain2 ps T fuel F ks = Some E -> EqHold fixed E.
Proof.
 induction ks as [|k rest IH]; intros F E seed fixed HP HT Hf HFH HL H; cbn [eqchain2] in H.
 - inversion H; subst. intros w r e Hin. contradiction.
 - destruct (step_eqs2 ps T fuel F k) as [E1|] eqn:Hs; [|discriminate].
   destruct (eqchain2 ps T fuel F rest) as [E2|] eqn:Hc; [|discriminate]. inversion H; subst E; clear H.
   intros w r e Hin. apply in_app_or in Hin as [Hin|Hin].
   + unfold step_eqs2 in Hs. subst fuel.
     destruct (nth_error ps (fst k)) as [proc|] eqn:HN; [|discriminate].
     destruct (pexany (filter (tail_okb T (fst k)) (pick F (snd k))) (statement_fuel p) (process_body proc)) as [acc|] eqn:Hx; [|discriminate].
     inversion Hs; subst E1; clear Hs.
     set (F0 := filter (tail_okb T (fst k)) (pick F (snd k))) in *.
     assert (H0: FactsHold fixed F0).
     { intros e0 z HI. apply filter_In in HI as [HI _]. apply HFH, (pick_in _ _ _ HI). }
     assert (Hok: facts_inputs_okb F0 T (fst k) = true).
     { unfold facts_inputs_okb. apply forallb_forall. intros ez HI. apply filter_In in HI as [_ HT']. exact HT'. }
     exact (prunany_comb_lfp p ps T (fst k) proc F0 acc seed fixed HP HT HN Hok H0 HL Hx w r e Hin).
   + exact (IH F E2 seed fixed HP HT Hf HFH HL Hc w r e Hin).
Qed.

Theorem eqchain2_out p ps T ks F0 copies eqs seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T ->
 FactsHold fixed F0 -> CombLFP p seed fixed ->
 (match eqchain2 ps T (statement_fuel p) F0 ks with
  | Some E => copies_okb E 8 copies && eqs_okb E eqs | None => false end) = true ->
 CopyHold fixed copies /\ EqHold fixed eqs.
Proof.
 intros HP HT HFH HL H.
 destruct (eqchain2 ps T (statement_fuel p) F0 ks) as [E|] eqn:Hc; [|discriminate].
 apply andb_true_iff in H as [Hcp Hq].
 pose proof (eqchain2_sound p ps T (statement_fuel p) ks F0 E seed fixed HP HT eq_refl HFH HL Hc) as HE.
 split.
 - intros w r x Hin. unfold copies_okb in Hcp. rewrite forallb_forall in Hcp.
   specialize (Hcp _ Hin). cbn [fst snd] in Hcp. apply Nat.eqb_eq in Hcp.
   rewrite (resolve_sound E fixed HE 8 w r), Hcp. reflexivity.
 - intros w r e Hin. unfold eqs_okb in Hq. rewrite forallb_forall in Hq.
   specialize (Hq _ Hin). cbn [fst snd] in Hq.
   destruct (eq_find E w r) as [e'|] eqn:Hf; [|discriminate].
   destruct (expr_eq_dec e' e) as [->|]; [|discriminate].
   exact (eq_find_sound E w r e fixed HE Hf).
Qed.
End ExtendedSVSymAliasNba.
Print Assumptions ExtendedSVSymAliasNba.eqchain2_out.
Print Assumptions ExtendedSVSymAliasNba.eqchain2_sound.
