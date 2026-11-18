(** Symbolic execution of comb processes with guards decided THROUGH the in-process overlay (template route, additive; 2026-11-03).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    [oxexec] is [ExtendedSVSymExecSym.sxexec] except that a guard / case scrutinee / case key may read roots assigned earlier in the
    process: it is first substituted by the overlay ([ssub], an expression over the entry state) and then decided by [xeval2] under the
    facts ([dguard]); if undecided, an [if] merges both arms into an [ECond] as before (a case with an undecided scrutinee is refused).
    Soundness, comb-fixed-point transfer, the fact step/pass and a wire request are re-proved for [oxexec]; nothing is assumed.
    Generic: no signal ids. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVConstantRoot
 Lang.ExtendedSVCombConnection Lang.ExtendedSVCombCut Lang.ExtendedSVAssignment Lang.ExtendedSVExprAgreement Lang.ExtendedSVSymExec
 Lang.ExtendedSVWordInvariant Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVConstantRoot
 ExtendedSVCombConnection ExtendedSVCombCut ExtendedSVAssignment ExtendedSVExprAgreement ExtendedSVSymExec ExtendedSVWordInvariant ExtendedSVFactChain ExtendedSVSymExecSym.
Local Open Scope Z_scope.
Module ExtendedSVSymExecOverlay.

Definition dguard (F:Facts) (ov:SOv) (g:Expr) : option Z :=
 match ssub ov g with Some g' => xeval2 F g' | None => None end.

Lemma dguard_sound F s0 (HF : FactsHold s0 F) ov s g z : Agree_s ov s0 s -> dguard F ov g = Some z -> eval_expr s g = z.
Proof.
 intros HA H. unfold dguard in H. destruct (ssub ov g) as [g'|] eqn:E; [|discriminate].
 destruct (ssub_sound ov s0 s HA g g' E) as [Hg _]. rewrite Hg. exact (xeval2_sound F s0 HF g' z H).
Qed.

Fixpoint oselect (F:Facts) (ov:SOv) (v:Z) (arms:list (option Expr * Stmt)) (d:Stmt) : option Stmt :=
 match arms with
 | [] => Some d
 | (None,b)::rest => oselect F ov v rest b
 | (Some k,b)::rest =>
     match dguard F ov k with
     | Some kv => if Z.eqb v kv then Some b else oselect F ov v rest d
     | None => None end
 end.

Fixpoint oxexec (F:Facts) (fuel:nat) (st:Stmt) (ov:SOv) {struct fuel} : option SOv :=
 match fuel with
 | O => Some ov
 | S f =>
  match st with
  | SSkip => Some ov
  | SAssign false rhs (LVar w r) =>
     match ssub ov rhs with Some e => Some ((r,(w,e))::ov) | None => None end
  | SAssign false rhs (LSel w (LVar W r) off) =>
     match ssub ov rhs, ssub ov off with
     | Some e, Some o =>
        match (match sov_lookup ov r with
               | Some (W',eo) => if Nat.eqb W' W then Some eo else None
               | None => Some (EVar W r) end) with
        | Some eo => if Nat.leb w W then Some ((r,(W, patch W w eo o e))::ov) else None
        | None => None end
     | _, _ => None end
  | SAssign _ _ _ => None
  | SSeq l => fold_left (fun o st' => match o with Some ov' => oxexec F f st' ov' | None => None end) l (Some ov)
  | SIf g y n => match dguard F ov g with
      | Some z => oxexec F f (if Z.eqb z 0 then n else y) ov
      | None => match ssub ov g, oxexec F f y ov, oxexec F f n ov with
          | Some g', Some oy, Some on => merge_if g' ov oy on
          | _, _, _ => None end end
  | SCase scr arms =>
      match dguard F ov scr with
      | Some v => match oselect F ov v arms SSkip with
         | Some c => oxexec F f c ov | None => None end
      | None => None end
  end
 end.

Section Ext.
Variable F : Facts.
Lemma ofold_none_e : forall (l:list Stmt) f, fold_left (fun o st' => match o with Some ov' => oxexec F f st' ov' | None => None end) l None = None.
Proof. induction l; intros; cbn; [reflexivity|apply IHl]. Qed.

Theorem oxexec_ext : forall fuel st ov ov', oxexec F fuel st ov = Some ov' -> Ext ov ov'.
Proof.
 induction fuel as [|f IH]; intros st ov ov' H; cbn [oxexec] in H.
 - inversion H; subst. apply ext_refl.
 - destruct st as [|nba rhs lhs|l|g y n|scr arms].
   + inversion H; subst. apply ext_refl.
   + destruct nba; [discriminate|]. destruct lhs as [w r|w base off]; [|destruct base as [W r|]; [|discriminate]].
     * destruct (ssub ov rhs) as [e|]; [|discriminate]. inversion H; subst. exists [(r,(w,e))]. reflexivity.
     * destruct (ssub ov rhs) as [e|]; [|discriminate]. destruct (ssub ov off) as [o|]; [|discriminate].
       destruct (match sov_lookup ov r with Some (W',eo') => if Nat.eqb W' W then Some eo' else None | None => Some (EVar W r) end) as [eo|]; [|discriminate].
       destruct (Nat.leb w W); [|discriminate]. inversion H; subst. exists [(r,(W, patch W w eo o e))]. reflexivity.
   + assert (Hgen : forall l ov ov', fold_left (fun o st' => match o with Some ov' => oxexec F f st' ov' | None => None end) l (Some ov) = Some ov' -> Ext ov ov').
     { induction l0 as [|a rest IHl]; intros ov0 ov1 H0.
       - cbn in H0. inversion H0; subst. apply ext_refl.
       - cbn in H0. destruct (oxexec F f a ov0) as [o1|] eqn:Ea; [|rewrite ofold_none_e in H0; discriminate].
         exact (ext_trans _ _ _ (IH _ _ _ Ea) (IHl _ _ H0)). }
     exact (Hgen l ov ov' H).
   + destruct (dguard F ov g) as [z|].
     * exact (IH _ _ _ H).
     * destruct (ssub ov g) as [g'|]; [|discriminate]. destruct (oxexec F f y ov) as [oy|]; [|discriminate].
       destruct (oxexec F f n ov) as [on|]; [|discriminate]. unfold merge_if in H.
       destruct (merge_all g' oy on _) as [m|]; [|discriminate]. inversion H; subst. exists m. reflexivity.
   + destruct (dguard F ov scr); [|discriminate].
     destruct (oselect F ov z arms SSkip) as [c|]; [|discriminate]. exact (IH _ _ _ H).
Qed.
End Ext.

Section Sound.
Variable F : Facts.
Variable s0 : State.
Hypothesis HF : FactsHold s0 F.

Lemma oselect_sound : forall arms ov s v d c, Agree_s ov s0 s -> oselect F ov v arms d = Some c ->
 select_case_stmt s v arms d = c.
Proof.
 induction arms as [|[[k|] b] rest IH]; intros ov s v d c HA H; cbn [oselect] in H.
 - inversion H; reflexivity.
 - destruct (dguard F ov k) as [kv|] eqn:Ek; [|discriminate].
   cbn [select_case_stmt]. rewrite (dguard_sound F s0 HF ov s k kv HA Ek).
   destruct (Z.eqb v kv); [now inversion H|exact (IH _ _ _ _ _ HA H)].
 - cbn [select_case_stmt]. exact (IH _ _ _ _ _ HA H).
Qed.

Lemma ofold_none : forall (l:list Stmt) f, fold_left (fun o st' => match o with Some ov' => oxexec F f st' ov' | None => None end) l None = None.
Proof. induction l; intros; cbn; [reflexivity|apply IHl]. Qed.

Theorem oxexec_sound : forall fuel st ov ov' es,
 oxexec F fuel st ov = Some ov' -> Agree_s ov s0 (blocking_state es) ->
 Agree_s ov' s0 (blocking_state (exec_stmt fuel st es)) /\
 pending_nba (exec_stmt fuel st es) = pending_nba es.
Proof.
 induction fuel as [|f IH]; intros st ov ov' es H HA.
 - cbn in H. inversion H; subst. cbn. split; [exact HA|reflexivity].
 - destruct st as [|nba rhs lhs|l|g y n|scr arms]; cbn [oxexec exec_stmt] in *.
   + inversion H; subst. split; [exact HA|reflexivity].
   + destruct nba; [discriminate|]. destruct lhs as [w r|w base off]; [|destruct base as [W r|]; [|discriminate]].
     * destruct (ssub ov rhs) as [e|] eqn:Es; [|discriminate]. inversion H; subst.
       cbn [blocking_state pending_nba]. split; [exact (agree_s_var s0 ov _ w r e rhs HA Es)|reflexivity].
     * destruct (ssub ov rhs) as [e|] eqn:Es; [|discriminate]. destruct (ssub ov off) as [o|] eqn:Eo; [|discriminate].
       destruct (match sov_lookup ov r with Some (W',eo') => if Nat.eqb W' W then Some eo' else None | None => Some (EVar W r) end) as [eo|] eqn:Eold; [|discriminate].
       destruct (Nat.leb w W) eqn:Hle; [|discriminate]. inversion H; subst. apply Nat.leb_le in Hle.
       cbn [blocking_state pending_nba]. split; [exact (agree_s_slice s0 ov _ W w r eo o e rhs off HA Es Eo Hle Eold)|reflexivity].
   + assert (Hgen: forall l ov ov' es,
        fold_left (fun o st' => match o with Some ov' => oxexec F f st' ov' | None => None end) l (Some ov) = Some ov' ->
        Agree_s ov s0 (blocking_state es) ->
        Agree_s ov' s0 (blocking_state (fold_left (fun es' st' => exec_stmt f st' es') l es)) /\
        pending_nba (fold_left (fun es' st' => exec_stmt f st' es') l es) = pending_nba es).
     { induction l0 as [|a rest IHl]; intros ov0 ov1 es0 H0 HA0.
       - cbn in H0. inversion H0; subst. cbn. split; [exact HA0|reflexivity].
       - cbn [fold_left] in H0 |- *. cbn in H0.
         destruct (oxexec F f a ov0) as [o1|] eqn:Ea; [|rewrite ofold_none in H0; discriminate].
         destruct (IH _ _ _ es0 Ea HA0) as [HA1 HP1].
         destruct (IHl _ _ _ H0 HA1) as [HA2 HP2]. split; [exact HA2|congruence]. }
     exact (Hgen l ov ov' es H HA).
   + destruct (dguard F ov g) as [z|] eqn:Ez.
     * rewrite (dguard_sound F s0 HF ov _ g z HA Ez). exact (IH _ _ _ _ H HA).
     * destruct (ssub ov g) as [g'|] eqn:Eg; [|discriminate]. destruct (oxexec F f y ov) as [oy|] eqn:Ey; [|discriminate].
       destruct (oxexec F f n ov) as [on|] eqn:En; [|discriminate].
       destruct (IH y ov oy es Ey HA) as [Ay Py]. destruct (IH n ov on es En HA) as [An Pn].
       destruct (ssub_sound ov s0 _ HA g g' Eg) as [Hg _]. rewrite Hg.
       destruct (Z.eqb_spec (eval_expr s0 g') 0) as [Hz|Hz].
       -- split; [|exact Pn]. exact (merge_if_sound s0 g' ov oy on ov' _ _ _ H (oxexec_ext F _ _ _ _ Ey) (oxexec_ext F _ _ _ _ En) Ay An (or_intror (conj Hz eq_refl))).
       -- split; [|exact Py]. exact (merge_if_sound s0 g' ov oy on ov' _ _ _ H (oxexec_ext F _ _ _ _ Ey) (oxexec_ext F _ _ _ _ En) Ay An (or_introl (conj Hz eq_refl))).
   + destruct (dguard F ov scr) as [v|] eqn:Ev; [|discriminate].
     destruct (oselect F ov v arms SSkip) as [c|] eqn:Ec; [|discriminate].
     rewrite (dguard_sound F s0 HF ov _ scr v HA Ev), (oselect_sound _ _ _ _ _ _ HA Ec).
     exact (IH _ _ _ _ H HA).
Qed.

Theorem oxrun_process_sound p proc ov :
 oxexec F (statement_fuel p) (process_body proc) [] = Some ov ->
 forall r w e, sov_lookup ov r = Some (w,e) -> norm w (read_signal (run_process p s0 proc) r) = norm w (eval_expr s0 e).
Proof.
 intros H r w e Hl. unfold run_process.
 destruct (oxexec_sound _ _ _ _ {|blocking_state:=s0;pending_nba:=[];emitted_updates:=[]|} H (agree_s_nil s0)) as [[HA1 _] HP].
 cbn [pending_nba] in HP. rewrite HP. cbn [apply_nba]. exact (HA1 _ _ _ Hl).
Qed.
End Sound.

(** Transfer to the combinational fixed point: the value of a root written by the comb process at position [k]. *)
Theorem oxrun_comb_lfp p ps T k proc F ov seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc ->
 facts_inputs_okb F T k = true ->
 FactsHold fixed F -> CombLFP p seed fixed ->
 oxexec F (statement_fuel p) (nbfix (process_body proc)) [] = Some ov ->
 forall r w e, sov_lookup ov r = Some (w,e) -> wr_lt T r (S k) = true -> inputs_okb T k e = true ->
 norm w (read_signal fixed r) = norm w (eval_expr fixed e).
Proof.
 intros HP HT HN Hok HFH HL Hx r w e Hl Hr Hie.
 pose proof (eq_trans HP (split_at ps k proc HN)) as Horder.
 rewrite (actual_lfp_pivot_output p (firstn k ps) proc (skipn (S k) ps) r seed fixed Horder (unw_suffix ps T (S k) r HT Hr) HL).
 set (S0 := fold_left (run_process p) (firstn k ps) fixed).
 assert (Hagree : forall wd x, wr_ge T x k || wr_lt T x k = true -> norm wd (read_signal S0 x) = norm wd (read_signal fixed x)).
 { intros wd x Hc. unfold S0. apply orb_true_iff in Hc as [Hc|Hc].
   - rewrite (fold_run_process_preserves_root p (firstn k ps) x fixed (roots_unwrittenb_sound _ _ (unw_prefix ps T k x HT Hc))). reflexivity.
   - rewrite (actual_lfp_pivot_input p (firstn k ps) proc (skipn (S k) ps) x seed fixed Horder
       (eq_ind (skipn k ps) (fun l => roots_unwrittenb x l = true) (unw_suffix ps T k x HT Hc) _ (skipn_nth_cons ps k proc HN)) HL). reflexivity. }
 assert (HFS : FactsHold S0 F).
 { intros e0 zz HI. rewrite <- (HFH e0 zz HI). apply eval_expr_agree. intros wd x Hin.
   unfold facts_inputs_okb in Hok. rewrite forallb_forall in Hok.
   specialize (Hok (e0,zz) HI). cbn [fst] in Hok. rewrite forallb_forall in Hok.
   specialize (Hok (wd,x) Hin). cbn [snd] in Hok. exact (Hagree wd x Hok). }
 rewrite run_process_nbfix. rewrite (oxrun_process_sound F S0 HFS p {| process_kind := process_kind proc; process_events := process_events proc; process_body := nbfix (process_body proc); process_source_line := process_source_line proc |} ov Hx r w e Hl).
 f_equal. apply eval_expr_agree. intros wd x Hin.
 unfold inputs_okb in Hie. rewrite forallb_forall in Hie. specialize (Hie (wd,x) Hin). cbn [snd] in Hie.
 exact (Hagree wd x Hie).
Qed.


Definition ox_new_facts (F0:Facts) (T:list (list nat)) (k:nat) (ov:SOv) : Facts :=
 flat_map (fun r => match sov_lookup ov r with
   | Some (w,e) => if wr_lt T r (S k) && inputs_okb T k e then
        match xeval2 F0 e with Some z => [(EVar w r, norm w z)] | None => [] end else []
   | None => [] end) (map fst ov).

Lemma ox_new_facts_sound p ps T k proc F0 ov seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc ->
 facts_inputs_okb F0 T k = true -> FactsHold fixed F0 -> CombLFP p seed fixed ->
 oxexec F0 (statement_fuel p) (nbfix (process_body proc)) [] = Some ov ->
 FactsHold fixed (ox_new_facts F0 T k ov).
Proof.
 intros HP HT HN Hok HF HL Hx e0 z0 HI. unfold ox_new_facts in HI. apply in_flat_map in HI as [r [Hr HI]].
 destruct (sov_lookup ov r) as [[w e]|] eqn:Hl; [|contradiction].
 destruct (wr_lt T r (S k) && inputs_okb T k e) eqn:Hc; [|contradiction].
 apply andb_true_iff in Hc as [Hc1 Hc2].
 destruct (xeval2 F0 e) as [z|] eqn:Hxe; [|contradiction].
 destruct HI as [HI|[]]. inversion HI; subst e0 z0. cbn [eval_expr].
 rewrite (oxrun_comb_lfp p ps T k proc F0 ov seed fixed HP HT HN Hok HF HL Hx r w e Hl Hc1 Hc2).
 rewrite (xeval2_sound F0 fixed HF e z Hxe). reflexivity.
Qed.

Definition ox_step (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (k:nat) : Facts :=
 match nth_error ps k with
 | None => F
 | Some proc =>
   let F0 := filter (tail_okb T k) F in
   match oxexec F0 fuel (nbfix (process_body proc)) [] with
   | None => F
   | Some ov => F ++ ox_new_facts F0 T k ov
   end
 end.

Lemma ox_step_sound p ps T fuel F k seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> fuel = statement_fuel p ->
 FactsHold fixed F -> CombLFP p seed fixed -> FactsHold fixed (ox_step ps T fuel F k).
Proof.
 intros HP HT Hf HF HL. unfold ox_step. subst fuel.
 destruct (nth_error ps k) as [proc|] eqn:HN; [|exact HF].
 set (F0 := filter (tail_okb T k) F).
 destruct (oxexec F0 (statement_fuel p) (nbfix (process_body proc)) []) as [ov|] eqn:Hx; [|exact HF].
 assert (H0 : FactsHold fixed F0) by (intros e z HI; apply filter_In in HI as [HI _]; apply HF, HI).
 assert (Hok : facts_inputs_okb F0 T k = true).
 { unfold facts_inputs_okb. apply forallb_forall. intros ez HI. apply filter_In in HI as [_ HT'].
   exact HT'. }
 intros e z HI. apply in_app_or in HI as [HI|HI]; [apply HF, HI|].
 exact (ox_new_facts_sound p ps T k proc F0 ov seed fixed HP HT HN Hok H0 HL Hx e z HI).
Qed.

Fixpoint ox_pass (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (ks:list nat) : Facts :=
 match ks with [] => F | k::t => ox_pass ps T fuel (ox_step ps T fuel F k) t end.
Fixpoint ox_run (ps:list Process) (T:list (list nat)) (fuel:nat) (rounds:nat) (F:Facts) : Facts :=
 match rounds with O => F | S r => ox_run ps T fuel r (ox_pass ps T fuel F (seq 0 (length ps))) end.

Lemma ox_pass_sound p ps T fuel seed fixed : filter is_comb (processes p) = ps -> TabC ps T -> fuel = statement_fuel p ->
 CombLFP p seed fixed -> forall ks F, FactsHold fixed F -> FactsHold fixed (ox_pass ps T fuel F ks).
Proof.
 intros HP HT Hf HL. induction ks as [|k t IH]; intros F HF; cbn [ox_pass]; [exact HF|].
 apply IH. exact (ox_step_sound p ps T fuel F k seed fixed HP HT Hf HF HL).
Qed.
Lemma ox_run_sound p ps T fuel seed fixed : filter is_comb (processes p) = ps -> TabC ps T -> fuel = statement_fuel p ->
 CombLFP p seed fixed -> forall rounds F, FactsHold fixed F -> FactsHold fixed (ox_run ps T fuel rounds F).
Proof.
 intros HP HT Hf HL. induction rounds as [|r IH]; intros F HF; cbn [ox_run]; [exact HF|].
 apply IH. exact (ox_pass_sound p ps T fuel seed fixed HP HT Hf HL _ F HF).
Qed.

Theorem ox_run_outs p ps T rounds F0 outs seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> FactsHold fixed F0 -> CombLFP p seed fixed ->
 outs_in_facts (ox_run ps T (statement_fuel p) rounds F0) outs = true -> DecOut fixed outs.
Proof.
 intros HP HT HF HL H. 
 pose proof (ox_run_sound p ps T (statement_fuel p) seed fixed HP HT eq_refl HL rounds F0 HF) as HF'.
 intros t Ht'. unfold outs_in_facts in H. rewrite forallb_forall in H. specialize (H t Ht').
 destruct (fact_find (ox_run ps T (statement_fuel p) rounds F0) (EVar (snd (fst t)) (fst (fst t)))) as [z|] eqn:Hf; [|discriminate].
 apply Z.eqb_eq in H. subst z.
 pose proof (fact_find_sound _ _ _ fixed HF' Hf) as Hv. cbn [eval_expr] in Hv. exact Hv.
Qed.


End ExtendedSVSymExecOverlay.
Print Assumptions ExtendedSVSymExecOverlay.oxexec_sound.
Print Assumptions ExtendedSVSymExecOverlay.oxrun_comb_lfp.
Print Assumptions ExtendedSVSymExecOverlay.ox_run_outs.
