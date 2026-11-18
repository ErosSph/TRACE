(** Havoc symbolic executor (template route, additive; 2026-11-04).  generalized_rule.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    Like [oxexec4] but never gives up on a statement it cannot decide: an undecided assignment, [if] (when the branches cannot be merged)
    or [case] is replaced by HAVOC entries, one per static writer, stored with width 0 (so [Agree_s] holds vacuously: [norm 0 _ = 0]).
    Any later read of a havoc root makes [ssub] fail (width 0 < any real read width), so a result never depends on skipped code.
    Frame lemma: [exec_stmt] changes only [stmt_writers] (reused [exec_stmt_preserves_unwritten_root]).  No design-specific ids. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVConstantRoot
 Lang.ExtendedSVCombConnection Lang.ExtendedSVCombCut Lang.ExtendedSVAssignment Lang.ExtendedSVExprAgreement Lang.ExtendedSVSymExec
 Lang.ExtendedSVWordInvariant Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVExpressionFold Lang.ExtendedSVEval3 Lang.ExtendedSVEval4
 Lang.ExtendedSVSymExecOverlay4.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVConstantRoot
 ExtendedSVCombConnection ExtendedSVCombCut ExtendedSVAssignment ExtendedSVExprAgreement ExtendedSVSymExec ExtendedSVWordInvariant ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVExpressionFold ExtendedSVEval3 ExtendedSVEval4 ExtendedSVSymExecOverlay4.
Local Open Scope Z_scope.
Module ExtendedSVSymExecHavoc.

Fixpoint no_nba (st:Stmt) : bool :=
 match st with
 | SSkip => true
 | SAssign nba _ _ => negb nba
 | SSeq l => forallb no_nba l
 | SIf _ y n => no_nba y && no_nba n
 | SCase _ arms => forallb (fun a => no_nba (snd a)) arms
 end.

Lemma no_nba_pending : forall fuel st es, no_nba st = true -> pending_nba (exec_stmt fuel st es) = pending_nba es.
Proof.
 induction fuel as [|f IH]; intros st es H; [reflexivity|].
 destruct st as [|nba rhs lhs|l|g y n|scr arms]; cbn [exec_stmt]; cbn [no_nba] in H.
 - reflexivity.
 - destruct nba; [discriminate|]. reflexivity.
 - assert (Hall : forall l0 es0, forallb no_nba l0 = true ->
      pending_nba (fold_left (fun es' st' => exec_stmt f st' es') l0 es0) = pending_nba es0).
   { induction l0 as [|a rest IHl]; intros es0 H0; [reflexivity|].
     cbn [forallb] in H0. apply andb_true_iff in H0 as [H1 H2]. cbn [fold_left].
     rewrite (IHl _ H2). apply IH, H1. }
   exact (Hall l es H).
 - apply andb_true_iff in H as [Hy Hn]. destruct (Z.eqb _ 0); [apply IH, Hn|apply IH, Hy].
 - assert (Hsel : forall v arms0 d, forallb (fun a => no_nba (snd a)) arms0 = true -> no_nba d = true ->
       no_nba (select_case_stmt (blocking_state es) v arms0 d) = true).
   { intros v. induction arms0 as [|[[k|] b] rest IHa]; intros d H0 Hd; cbn [select_case_stmt]; [exact Hd| | ].
     - cbn [forallb] in H0. apply andb_true_iff in H0 as [H1 H2]. destruct (Z.eqb _ _); [exact H1|exact (IHa _ H2 Hd)].
     - cbn [forallb] in H0. apply andb_true_iff in H0 as [H1 H2]. exact (IHa _ H2 H1). }
   apply IH. apply Hsel; [exact H|reflexivity].
Qed.

Fixpoint esz (e:Expr) : nat := match e with
 | EConst _ _ | EVar _ _ => 1%nat | ESel _ a b | EConcat _ a b | EBinary _ _ a b => S (esz a + esz b)
 | EReplicate _ _ a | EExtend _ _ a | EUnary _ _ a => S (esz a) | ECond _ g a b => S (esz g + esz a + esz b) end.
(** size bound of a substituted right-hand side: a bigger one is havoc'd (guards against exponential growth of
    expressions assembled lane by lane from several arrays that read each other). *)
Definition hbound : nat := 3000%nat.
Definition hok (e:Expr) : bool := Nat.leb (esz e) hbound.

Definition hmk (r:signal) : signal * (nat * Expr) := (r,(0%nat, EConst 0%nat 0)).
Definition hv (st:Stmt) (ov:SOv) : option SOv :=
 if no_nba st then Some (map hmk (stmt_writers st) ++ ov) else None.

Lemma norm0 v : norm 0 v = 0.
Proof. unfold norm, mask. cbn. apply Z.land_0_r. Qed.

Lemma hmk_in : forall ws ov r, In r ws -> sov_lookup (map hmk ws ++ ov) r = Some (0%nat, EConst 0%nat 0).
Proof.
 induction ws as [|a ws IH]; intros ov r H; [destruct H|].
 cbn [map app sov_lookup hmk]. destruct (Nat.eqb r a) eqn:E; [reflexivity|].
 apply IH. destruct H as [->|H]; [rewrite Nat.eqb_refl in E; discriminate|exact H].
Qed.
Lemma hmk_nin : forall ws ov r, ~ In r ws -> sov_lookup (map hmk ws ++ ov) r = sov_lookup ov r.
Proof.
 intros ws ov r H. apply lookup_app_nin. rewrite map_map. cbn [hmk fst]. rewrite map_id. exact H.
Qed.

Lemma hv_ext st ov ov' : hv st ov = Some ov' -> Ext ov ov'.
Proof. unfold hv. destruct (no_nba st); [|discriminate]. intro H. inversion H; subst. exists (map hmk (stmt_writers st)). reflexivity. Qed.

(** Frame + soundness of the havoc fallback. *)
Lemma hv_sound s0 ov ov' st es fuel : hv st ov = Some ov' -> Agree_s ov s0 (blocking_state es) ->
 Agree_s ov' s0 (blocking_state (exec_stmt fuel st es)) /\ pending_nba (exec_stmt fuel st es) = pending_nba es.
Proof.
 intros H [HA1 HA2]. unfold hv in H. destruct (no_nba st) eqn:Hn; [|discriminate]. inversion H; subst ov'. clear H.
 split; [|exact (no_nba_pending fuel st es Hn)].
 assert (Hfr : forall r, ~ In r (stmt_writers st) ->
   read_signal (blocking_state (exec_stmt fuel st es)) r = read_signal (blocking_state es) r)
   by (intros r Hr; exact (proj1 (exec_stmt_preserves_unwritten_root fuel st r es Hr))).
 split.
 - intros r w e Hl. destruct (in_dec Nat.eq_dec r (stmt_writers st)) as [Hin|Hin].
   + rewrite (hmk_in _ _ _ Hin) in Hl. inversion Hl; subst. rewrite !norm0. reflexivity.
   + rewrite (hmk_nin _ _ _ Hin) in Hl. rewrite (Hfr r Hin). exact (HA1 r w e Hl).
 - intros r Hl. destruct (in_dec Nat.eq_dec r (stmt_writers st)) as [Hin|Hin].
   + rewrite (hmk_in _ _ _ Hin) in Hl. discriminate.
   + rewrite (hmk_nin _ _ _ Hin) in Hl. rewrite (Hfr r Hin). exact (HA2 r Hl).
Qed.

Fixpoint hxexec (F:Facts) (fuel:nat) (st:Stmt) (ov:SOv) {struct fuel} : option SOv :=
 match fuel with
 | O => Some ov
 | S f =>
  match st with
  | SSkip => Some ov
  | SAssign false rhs (LVar w r) =>
     match ssub ov rhs with Some e => if hok e then Some ((r,(w,e))::ov) else hv st ov | None => hv st ov end
  | SAssign false rhs (LSel w (LVar W r) off) =>
     match ssub ov rhs with
     | None => hv st ov
     | Some e =>
       match ssub ov off with
       | None => hv st ov
       | Some o =>
        match (match sov_lookup ov r with
               | Some (W',eo) => if Nat.eqb W' W then Some eo else None
               | None => Some (EVar W r) end) with
        | Some eo => if Nat.leb w W && hok e && hok o && hok eo then Some ((r,(W, patch W w eo o e))::ov) else hv st ov
        | None => hv st ov end end end
  | SAssign _ _ _ => hv st ov
  | SSeq l => fold_left (fun o st' => match o with Some ov' => hxexec F f st' ov' | None => None end) l (Some ov)
  | SIf g y n => match dguard4 F ov g with
      | Some z => hxexec F f (if Z.eqb z 0 then n else y) ov
      | None => match ssub ov g with
          | None => hv st ov
          | Some g' => match hxexec F f y ov, hxexec F f n ov with
              | Some oy, Some on => match merge_if g' ov oy on with Some m => Some m | None => hv st ov end
              | _, _ => hv st ov end end end
  | SCase scr arms =>
      match dguard4 F ov scr with
      | Some v => match oselect4 F ov v arms SSkip with
         | Some c => hxexec F f c ov | None => hv st ov end
      | None => hv st ov end
  end
 end.

Section Ext.
Variable F : Facts.
Lemma hfold_none_e : forall (l:list Stmt) f, fold_left (fun o st' => match o with Some ov' => hxexec F f st' ov' | None => None end) l None = None.
Proof. induction l; intros; cbn; [reflexivity|apply IHl]. Qed.

Theorem hxexec_ext : forall fuel st ov ov', hxexec F fuel st ov = Some ov' -> Ext ov ov'.
Proof.
 induction fuel as [|f IH]; intros st ov ov' H; cbn [hxexec] in H.
 - inversion H; subst. apply ext_refl.
 - destruct st as [|nba rhs lhs|l|g y n|scr arms].
   + inversion H; subst. apply ext_refl.
   + destruct nba; [exact (hv_ext _ _ _ H)|]. destruct lhs as [w r|w base off]; [|destruct base as [W r|]; [|exact (hv_ext _ _ _ H)]].
     * destruct (ssub ov rhs) as [e|]; [|exact (hv_ext _ _ _ H)]. destruct (hok e); [|exact (hv_ext _ _ _ H)]. inversion H; subst. exists [(r,(w,e))]. reflexivity.
     * destruct (ssub ov rhs) as [e|]; [|exact (hv_ext _ _ _ H)]. destruct (ssub ov off) as [o|]; [|exact (hv_ext _ _ _ H)].
       destruct (match sov_lookup ov r with Some (W',eo') => if Nat.eqb W' W then Some eo' else None | None => Some (EVar W r) end) as [eo|]; [|exact (hv_ext _ _ _ H)].
       destruct (Nat.leb w W && hok e && hok o && hok eo); [|exact (hv_ext _ _ _ H)]. inversion H; subst. exists [(r,(W, patch W w eo o e))]. reflexivity.
   + assert (Hgen : forall l ov ov', fold_left (fun o st' => match o with Some ov' => hxexec F f st' ov' | None => None end) l (Some ov) = Some ov' -> Ext ov ov').
     { induction l0 as [|a rest IHl]; intros ov0 ov1 H0.
       - cbn in H0. inversion H0; subst. apply ext_refl.
       - cbn in H0. destruct (hxexec F f a ov0) as [o1|] eqn:Ea; [|rewrite hfold_none_e in H0; discriminate].
         exact (ext_trans _ _ _ (IH _ _ _ Ea) (IHl _ _ H0)). }
     exact (Hgen l ov ov' H).
   + destruct (dguard4 F ov g) as [z|].
     * exact (IH _ _ _ H).
     * destruct (ssub ov g) as [g'|]; [|exact (hv_ext _ _ _ H)].
       destruct (hxexec F f y ov) as [oy|] eqn:Ey; [|exact (hv_ext _ _ _ H)].
       destruct (hxexec F f n ov) as [on|] eqn:En; [|exact (hv_ext _ _ _ H)].
       destruct (merge_if g' ov oy on) as [m|] eqn:Em; [|exact (hv_ext _ _ _ H)]. inversion H; subst ov'.
       unfold merge_if in Em. destruct (merge_all g' oy on _) as [m'|]; [|discriminate]. inversion Em; subst. exists m'. reflexivity.
   + destruct (dguard4 F ov scr); [|exact (hv_ext _ _ _ H)].
     destruct (oselect4 F ov z arms SSkip) as [c|]; [|exact (hv_ext _ _ _ H)]. exact (IH _ _ _ H).
Qed.
End Ext.

Section Sound.
Variable F : Facts.
Variable s0 : State.
Hypothesis HF : FactsHold s0 F.

Lemma hfold_none : forall (l:list Stmt) f, fold_left (fun o st' => match o with Some ov' => hxexec F f st' ov' | None => None end) l None = None.
Proof. induction l; intros; cbn; [reflexivity|apply IHl]. Qed.

Theorem hxexec_sound : forall fuel st ov ov' es,
 hxexec F fuel st ov = Some ov' -> Agree_s ov s0 (blocking_state es) ->
 Agree_s ov' s0 (blocking_state (exec_stmt fuel st es)) /\
 pending_nba (exec_stmt fuel st es) = pending_nba es.
Proof.
 induction fuel as [|f IH]; intros st ov ov' es H HA.
 - cbn in H. inversion H; subst. cbn. split; [exact HA|reflexivity].
 - destruct st as [|nba rhs lhs|l|g y n|scr arms]; cbn [hxexec] in H.
   + inversion H; subst. split; [exact HA|reflexivity].
   + destruct nba; [exact (hv_sound s0 _ _ _ es (S f) H HA)|].
     destruct lhs as [w r|w base off]; [|destruct base as [W r|]; [|exact (hv_sound s0 _ _ _ es (S f) H HA)]].
     * destruct (ssub ov rhs) as [e|] eqn:Es; [|exact (hv_sound s0 _ _ _ es (S f) H HA)]. destruct (hok e); [|exact (hv_sound s0 _ _ _ es (S f) H HA)]. inversion H; subst.
       cbn [exec_stmt blocking_state pending_nba]. split; [exact (agree_s_var s0 ov _ w r e rhs HA Es)|reflexivity].
     * destruct (ssub ov rhs) as [e|] eqn:Es; [|exact (hv_sound s0 _ _ _ es (S f) H HA)].
       destruct (ssub ov off) as [o|] eqn:Eo; [|exact (hv_sound s0 _ _ _ es (S f) H HA)].
       destruct (match sov_lookup ov r with Some (W',eo') => if Nat.eqb W' W then Some eo' else None | None => Some (EVar W r) end) as [eo|] eqn:Eold; [|exact (hv_sound s0 _ _ _ es (S f) H HA)].
       destruct (Nat.leb w W && hok e && hok o && hok eo) eqn:Hle; [|exact (hv_sound s0 _ _ _ es (S f) H HA)]. inversion H; subst.
       apply andb_true_iff in Hle as [Hle _]. apply andb_true_iff in Hle as [Hle _]. apply andb_true_iff in Hle as [Hle _]. apply Nat.leb_le in Hle.
       cbn [exec_stmt blocking_state pending_nba]. split; [exact (agree_s_slice s0 ov _ W w r eo o e rhs off HA Es Eo Hle Eold)|reflexivity].
   + cbn [exec_stmt].
     assert (Hgen: forall l ov ov' es,
        fold_left (fun o st' => match o with Some ov' => hxexec F f st' ov' | None => None end) l (Some ov) = Some ov' ->
        Agree_s ov s0 (blocking_state es) ->
        Agree_s ov' s0 (blocking_state (fold_left (fun es' st' => exec_stmt f st' es') l es)) /\
        pending_nba (fold_left (fun es' st' => exec_stmt f st' es') l es) = pending_nba es).
     { induction l0 as [|a rest IHl]; intros ov0 ov1 es0 H0 HA0.
       - cbn in H0. inversion H0; subst. cbn. split; [exact HA0|reflexivity].
       - cbn [fold_left] in H0 |- *. cbn in H0.
         destruct (hxexec F f a ov0) as [o1|] eqn:Ea; [|rewrite hfold_none in H0; discriminate].
         destruct (IH _ _ _ es0 Ea HA0) as [HA1 HP1].
         destruct (IHl _ _ _ H0 HA1) as [HA2 HP2]. split; [exact HA2|congruence]. }
     exact (Hgen l ov ov' es H HA).
   + destruct (dguard4 F ov g) as [z|] eqn:Ez.
     * cbn [exec_stmt]. rewrite (dguard4_sound F s0 HF ov _ g z HA Ez). exact (IH _ _ _ _ H HA).
     * destruct (ssub ov g) as [g'|] eqn:Eg; [|exact (hv_sound s0 _ _ _ es (S f) H HA)].
       destruct (hxexec F f y ov) as [oy|] eqn:Ey; [|exact (hv_sound s0 _ _ _ es (S f) H HA)].
       destruct (hxexec F f n ov) as [on|] eqn:En; [|exact (hv_sound s0 _ _ _ es (S f) H HA)].
       destruct (merge_if g' ov oy on) as [m|] eqn:Em; [|exact (hv_sound s0 _ _ _ es (S f) H HA)]. inversion H; subst m.
       cbn [exec_stmt].
       destruct (IH y ov oy es Ey HA) as [Ay Py]. destruct (IH n ov on es En HA) as [An Pn].
       destruct (ssub_sound ov s0 _ HA g g' Eg) as [Hg _]. rewrite Hg.
       destruct (Z.eqb_spec (eval_expr s0 g') 0) as [Hz|Hz].
       -- split; [|exact Pn]. exact (merge_if_sound s0 g' ov oy on ov' _ _ _ Em (hxexec_ext F _ _ _ _ Ey) (hxexec_ext F _ _ _ _ En) Ay An (or_intror (conj Hz eq_refl))).
       -- split; [|exact Py]. exact (merge_if_sound s0 g' ov oy on ov' _ _ _ Em (hxexec_ext F _ _ _ _ Ey) (hxexec_ext F _ _ _ _ En) Ay An (or_introl (conj Hz eq_refl))).
   + destruct (dguard4 F ov scr) as [v|] eqn:Ev; [|exact (hv_sound s0 _ _ _ es (S f) H HA)].
     destruct (oselect4 F ov v arms SSkip) as [c|] eqn:Ec; [|exact (hv_sound s0 _ _ _ es (S f) H HA)].
     cbn [exec_stmt].
     rewrite (dguard4_sound F s0 HF ov _ scr v HA Ev), (oselect4_sound F s0 HF _ _ _ _ _ _ HA Ec).
     exact (IH _ _ _ _ H HA).
Qed.


Theorem hxrun_process_sound p proc ov :
 hxexec F (statement_fuel p) (process_body proc) [] = Some ov ->
 forall r w e, sov_lookup ov r = Some (w,e) -> norm w (read_signal (run_process p s0 proc) r) = norm w (eval_expr s0 e).
Proof.
 intros H r w e Hl. unfold run_process.
 destruct (hxexec_sound _ _ _ _ {|blocking_state:=s0;pending_nba:=[];emitted_updates:=[]|} H (agree_s_nil s0)) as [[HA1 _] HP].
 cbn [pending_nba] in HP. rewrite HP. cbn [apply_nba]. exact (HA1 _ _ _ Hl).
Qed.
End Sound.

(** ---- split execution: a class-independent prefix of a two-level sequence is executed once (facts F1), the tail under the stronger facts F2 ---- *)
Definition hxl (F:Facts) (f:nat) (l:list Stmt) (ov:SOv) : option SOv :=
 fold_left (fun o st' => match o with Some ov' => hxexec F f st' ov' | None => None end) l (Some ov).

Lemma hxl_none F f l : fold_left (fun o st' => match o with Some ov' => hxexec F f st' ov' | None => None end) l None = None.
Proof. induction l; cbn; auto. Qed.

Lemma hxl_app F f l1 l2 ov : hxl F f (l1 ++ l2) ov = match hxl F f l1 ov with Some o => hxl F f l2 o | None => None end.
Proof.
 unfold hxl. revert ov. induction l1 as [|a t IH]; intro ov; cbn [app fold_left].
 - reflexivity.
 - destruct (hxexec F f a ov) as [o|]; [apply IH|]. rewrite (hxl_none F f (t ++ l2)), (hxl_none F f t). reflexivity.
Qed.

Lemma hxl_sound F s0 (HF:FactsHold s0 F) f l ov ov' es : hxl F f l ov = Some ov' -> Agree_s ov s0 (blocking_state es) ->
 Agree_s ov' s0 (blocking_state (fold_left (fun es' st' => exec_stmt f st' es') l es)) /\
 pending_nba (fold_left (fun es' st' => exec_stmt f st' es') l es) = pending_nba es.
Proof.
 intros H HA. exact (hxexec_sound F s0 HF (S f) (SSeq l) ov ov' es H HA).
Qed.

Theorem hxrun2_process_sound p proc l1 l2 F1 F2 s0 f ovP ov :
 FactsHold s0 F1 -> FactsHold s0 F2 -> process_body proc = SSeq [SSeq (l1 ++ l2)] -> statement_fuel p = S (S f) ->
 hxl F1 f l1 [] = Some ovP -> hxl F2 f l2 ovP = Some ov ->
 forall r w e, sov_lookup ov r = Some (w,e) -> norm w (read_signal (run_process p s0 proc) r) = norm w (eval_expr s0 e).
Proof.
 intros H1 H2 Hb Hf Hp Ht r w e Hl. unfold run_process. rewrite Hf, Hb.
 set (es0 := {|blocking_state:=s0;pending_nba:=[];emitted_updates:=[]|}).
 cbn [exec_stmt fold_left]. rewrite fold_left_app.
 destruct (hxl_sound F1 s0 H1 f l1 [] ovP es0 Hp (agree_s_nil s0)) as [HA1 HP1].
 destruct (hxl_sound F2 s0 H2 f l2 ovP ov _ Ht HA1) as [HA2 HP2].
 cbn [pending_nba] in HP1. rewrite HP2, HP1. cbn [apply_nba]. exact (proj1 HA2 _ _ _ Hl).
Qed.


Theorem hxrun2_comb_lfp p ps T k proc l1 l2 F1 F ovP ov f seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc ->
 facts_inputs_okb F T k = true -> facts_inputs_okb F1 T k = true ->
 FactsHold fixed F -> FactsHold fixed F1 -> CombLFP p seed fixed ->
 nbfix (process_body proc) = SSeq [SSeq (l1 ++ l2)] -> statement_fuel p = S (S f) ->
 hxl F1 f l1 [] = Some ovP -> hxl F f l2 ovP = Some ov ->
 forall r w e, sov_lookup ov r = Some (w,e) -> wr_lt T r (S k) = true -> inputs_okb T k e = true ->
 norm w (read_signal fixed r) = norm w (eval_expr fixed e).
Proof.
 intros HP HT HN Hok Hok1 HFH HFH1 HL Hb Hf Hp Hx r w e Hl Hr Hie.
 pose proof (eq_trans HP (split_at ps k proc HN)) as Horder.
 rewrite (actual_lfp_pivot_output p (firstn k ps) proc (skipn (S k) ps) r seed fixed Horder (unw_suffix ps T (S k) r HT Hr) HL).
 set (S0 := fold_left (run_process p) (firstn k ps) fixed).
 assert (Hagree : forall wd x, wr_ge T x k || wr_lt T x k = true -> norm wd (read_signal S0 x) = norm wd (read_signal fixed x)).
 { intros wd x Hc. unfold S0. apply orb_true_iff in Hc as [Hc|Hc].
   - rewrite (fold_run_process_preserves_root p (firstn k ps) x fixed (roots_unwrittenb_sound _ _ (unw_prefix ps T k x HT Hc))). reflexivity.
   - rewrite (actual_lfp_pivot_input p (firstn k ps) proc (skipn (S k) ps) x seed fixed Horder
       (eq_ind (skipn k ps) (fun l => roots_unwrittenb x l = true) (unw_suffix ps T k x HT Hc) _ (skipn_nth_cons ps k proc HN)) HL). reflexivity. }
 assert (Htr : forall FF, facts_inputs_okb FF T k = true -> FactsHold fixed FF -> FactsHold S0 FF).
 { intros FF Hok' HFH' e0 zz HI. rewrite <- (HFH' e0 zz HI). apply eval_expr_agree. intros wd x Hin.
   unfold facts_inputs_okb in Hok'. rewrite forallb_forall in Hok'.
   specialize (Hok' (e0,zz) HI). cbn [fst] in Hok'. rewrite forallb_forall in Hok'.
   specialize (Hok' (wd,x) Hin). cbn [snd] in Hok'. exact (Hagree wd x Hok'). }
 rewrite run_process_nbfix.
 rewrite (hxrun2_process_sound p {| process_kind := process_kind proc; process_events := process_events proc; process_body := nbfix (process_body proc); process_source_line := process_source_line proc |}
   l1 l2 F1 F S0 f ovP ov (Htr F1 Hok1 HFH1) (Htr F Hok HFH) Hb Hf Hp Hx r w e Hl).
 f_equal. apply eval_expr_agree. intros wd x Hin.
 unfold inputs_okb in Hie. rewrite forallb_forall in Hie. specialize (Hie (wd,x) Hin). cbn [snd] in Hie.
 exact (Hagree wd x Hie).
Qed.

(** Output extraction: the executor's expression for root [r], simplified under the facts, is a given small expression [X]
    (decided by computation); then the root equals [X] at any combinational fixed point satisfying the facts. *)
Definition hx_out_chk (T:list (list nat)) (k:nat) (F:Facts) (ov:SOv) (r:signal) (w:nat) (X:Expr) : bool :=
 match sov_lookup ov r with
 | Some (w',e) => Nat.eqb w w' && (if expr_eq_dec (simp4 F e) X then true else false) && inputs_okb T k e && wr_lt T r (S k)
 | None => false end.

Theorem hx2_out p ps T k proc l1 l2 F1 F ovP ov f seed fixed r w X :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc ->
 facts_inputs_okb F T k = true -> facts_inputs_okb F1 T k = true ->
 FactsHold fixed F -> FactsHold fixed F1 -> CombLFP p seed fixed ->
 nbfix (process_body proc) = SSeq [SSeq (l1 ++ l2)] -> statement_fuel p = S (S f) ->
 hxl F1 f l1 [] = Some ovP -> hxl F f l2 ovP = Some ov ->
 hx_out_chk T k F ov r w X = true ->
 norm w (read_signal fixed r) = norm w (eval_expr fixed X).
Proof.
 intros HP HT HN Hok Hok1 HFH HFH1 HL Hb Hf Hp Hx Hc. unfold hx_out_chk in Hc.
 destruct (sov_lookup ov r) as [[w' e]|] eqn:Hl; [|discriminate].
 apply andb_true_iff in Hc as [Hc Hr]. apply andb_true_iff in Hc as [Hc Hie]. apply andb_true_iff in Hc as [Hw Hs].
 apply Nat.eqb_eq in Hw. subst w'.
 destruct (expr_eq_dec (simp4 F e) X) as [Hxe|]; [|discriminate]. subst X.
 rewrite (simp4_sound F fixed HFH e).
 exact (hxrun2_comb_lfp p ps T k proc l1 l2 F1 F ovP ov f seed fixed HP HT HN Hok Hok1 HFH HFH1 HL Hb Hf Hp Hx r w e Hl Hr Hie).
Qed.


(** One closed boolean check: the tail run and the output comparison are computed together, so no intermediate overlay constant is ever named
    (a freshly built overlay constant costs about a minute on its first use by [vm_compute]). *)
Definition hx_chk2 (T:list (list nat)) (k:nat) (F:Facts) (ovP:SOv) (l2:list Stmt) (f:nat) (r:signal) (w:nat) (X:Expr) : bool :=
 match hxl F f l2 ovP with Some ov => hx_out_chk T k F ov r w X | None => false end.

Theorem hx2_out2 p ps T k proc l1 l2 F1 F ovP f seed fixed r w X :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc ->
 facts_inputs_okb F T k = true -> facts_inputs_okb F1 T k = true ->
 FactsHold fixed F -> FactsHold fixed F1 -> CombLFP p seed fixed ->
 nbfix (process_body proc) = SSeq [SSeq (l1 ++ l2)] -> statement_fuel p = S (S f) ->
 hxl F1 f l1 [] = Some ovP -> hx_chk2 T k F ovP l2 f r w X = true ->
 norm w (read_signal fixed r) = norm w (eval_expr fixed X).
Proof.
 intros HP HT HN Hok Hok1 HFH HFH1 HL Hb Hf Hp Hc. unfold hx_chk2 in Hc.
 destruct (hxl F f l2 ovP) as [ov|] eqn:Hx; [|discriminate].
 exact (hx2_out p ps T k proc l1 l2 F1 F ovP ov f seed fixed r w X HP HT HN Hok Hok1 HFH HFH1 HL Hb Hf Hp Hx Hc).
Qed.

Lemma skipn_in_l (A:Type) (x:A) : forall (l:list A) n, In x (skipn n l) -> In x l.
Proof. induction l as [|a t IH]; intros n HI; cbn in HI.
 - destruct n; contradiction.
 - destruct n; [exact HI|]. right. exact (IH _ HI). Qed.
Lemma factshold_app s a b : FactsHold s a -> FactsHold s b -> FactsHold s (a ++ b).
Proof. intros Ha Hb e z HI. apply in_app_or in HI as [HI|HI]; [exact (Ha _ _ HI)|exact (Hb _ _ HI)]. Qed.
Lemma factshold_app_l s a b : FactsHold s (a ++ b) -> FactsHold s a.
Proof. intros H e z HI. apply H. apply in_or_app. left. exact HI. Qed.
Lemma factshold_skipn s n F : FactsHold s F -> FactsHold s (skipn n F).
Proof. intros H e z HI. apply H. exact (skipn_in_l _ _ _ _ HI). Qed.



(** Transfer to the combinational fixed point: the value of a root written by the comb process at position [k]. *)
Theorem hxrun_comb_lfp p ps T k proc F ov seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc ->
 facts_inputs_okb F T k = true ->
 FactsHold fixed F -> CombLFP p seed fixed ->
 hxexec F (statement_fuel p) (nbfix (process_body proc)) [] = Some ov ->
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
 rewrite run_process_nbfix. rewrite (hxrun_process_sound F S0 HFS p {| process_kind := process_kind proc; process_events := process_events proc; process_body := nbfix (process_body proc); process_source_line := process_source_line proc |} ov Hx r w e Hl).
 f_equal. apply eval_expr_agree. intros wd x Hin.
 unfold inputs_okb in Hie. rewrite forallb_forall in Hie. specialize (Hie (wd,x) Hin). cbn [snd] in Hie.
 exact (Hagree wd x Hie).
Qed.


Definition hx_new_facts (F0:Facts) (T:list (list nat)) (k:nat) (ov:SOv) : Facts :=
 flat_map (fun r => match sov_lookup ov r with
   | Some (w,e) => if wr_lt T r (S k) && inputs_okb T k e then
        match xeval4 F0 e with Some z => [(EVar w r, norm w z)] | None => [] end else []
   | None => [] end) (map fst ov).

Lemma hx_new_facts_sound p ps T k proc F0 ov seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc ->
 facts_inputs_okb F0 T k = true -> FactsHold fixed F0 -> CombLFP p seed fixed ->
 hxexec F0 (statement_fuel p) (nbfix (process_body proc)) [] = Some ov ->
 FactsHold fixed (hx_new_facts F0 T k ov).
Proof.
 intros HP HT HN Hok HF HL Hx e0 z0 HI. unfold hx_new_facts in HI. apply in_flat_map in HI as [r [Hr HI]].
 destruct (sov_lookup ov r) as [[w e]|] eqn:Hl; [|contradiction].
 destruct (wr_lt T r (S k) && inputs_okb T k e) eqn:Hc; [|contradiction].
 apply andb_true_iff in Hc as [Hc1 Hc2].
 destruct (xeval4 F0 e) as [z|] eqn:Hxe; [|contradiction].
 destruct HI as [HI|[]]. inversion HI; subst e0 z0. cbn [eval_expr].
 rewrite (hxrun_comb_lfp p ps T k proc F0 ov seed fixed HP HT HN Hok HF HL Hx r w e Hl Hc1 Hc2).
 rewrite (xeval4_sound F0 fixed HF e z Hxe). reflexivity.
Qed.

Definition hx_step (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (k:nat) : Facts :=
 match nth_error ps k with
 | None => F
 | Some proc =>
   let F0 := filter (tail_okb T k) F in
   match hxexec F0 fuel (nbfix (process_body proc)) [] with
   | None => F
   | Some ov => F ++ hx_new_facts F0 T k ov
   end
 end.

Lemma hx_step_sound p ps T fuel F k seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> fuel = statement_fuel p ->
 FactsHold fixed F -> CombLFP p seed fixed -> FactsHold fixed (hx_step ps T fuel F k).
Proof.
 intros HP HT Hf HF HL. unfold hx_step. subst fuel.
 destruct (nth_error ps k) as [proc|] eqn:HN; [|exact HF].
 set (F0 := filter (tail_okb T k) F).
 destruct (hxexec F0 (statement_fuel p) (nbfix (process_body proc)) []) as [ov|] eqn:Hx; [|exact HF].
 assert (H0 : FactsHold fixed F0) by (intros e z HI; apply filter_In in HI as [HI _]; apply HF, HI).
 assert (Hok : facts_inputs_okb F0 T k = true).
 { unfold facts_inputs_okb. apply forallb_forall. intros ez HI. apply filter_In in HI as [_ HT'].
   exact HT'. }
 intros e z HI. apply in_app_or in HI as [HI|HI]; [apply HF, HI|].
 exact (hx_new_facts_sound p ps T k proc F0 ov seed fixed HP HT HN Hok H0 HL Hx e z HI).
Qed.

Fixpoint hx_pass (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (ks:list nat) : Facts :=
 match ks with [] => F | k::t => hx_pass ps T fuel (hx_step ps T fuel F k) t end.
Fixpoint hx_run (ps:list Process) (T:list (list nat)) (fuel:nat) (rounds:nat) (F:Facts) : Facts :=
 match rounds with O => F | S r => hx_run ps T fuel r (hx_pass ps T fuel F (seq 0 (length ps))) end.

Lemma hx_pass_sound p ps T fuel seed fixed : filter is_comb (processes p) = ps -> TabC ps T -> fuel = statement_fuel p ->
 CombLFP p seed fixed -> forall ks F, FactsHold fixed F -> FactsHold fixed (hx_pass ps T fuel F ks).
Proof.
 intros HP HT Hf HL. induction ks as [|k t IH]; intros F HF; cbn [hx_pass]; [exact HF|].
 apply IH. exact (hx_step_sound p ps T fuel F k seed fixed HP HT Hf HF HL).
Qed.
Lemma hx_run_sound p ps T fuel seed fixed : filter is_comb (processes p) = ps -> TabC ps T -> fuel = statement_fuel p ->
 CombLFP p seed fixed -> forall rounds F, FactsHold fixed F -> FactsHold fixed (hx_run ps T fuel rounds F).
Proof.
 intros HP HT Hf HL. induction rounds as [|r IH]; intros F HF; cbn [hx_run]; [exact HF|].
 apply IH. exact (hx_pass_sound p ps T fuel seed fixed HP HT Hf HL _ F HF).
Qed.

Theorem hx_run_outs p ps T rounds F0 outs seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> FactsHold fixed F0 -> CombLFP p seed fixed ->
 outs_in_facts (hx_run ps T (statement_fuel p) rounds F0) outs = true -> DecOut fixed outs.
Proof.
 intros HP HT HF HL H. 
 pose proof (hx_run_sound p ps T (statement_fuel p) seed fixed HP HT eq_refl HL rounds F0 HF) as HF'.
 intros t Ht'. unfold outs_in_facts in H. rewrite forallb_forall in H. specialize (H t Ht').
 destruct (fact_find (hx_run ps T (statement_fuel p) rounds F0) (EVar (snd (fst t)) (fst (fst t)))) as [z|] eqn:Hf; [|discriminate].
 apply Z.eqb_eq in H. subst z.
 pose proof (fact_find_sound _ _ _ fixed HF' Hf) as Hv. cbn [eval_expr] in Hv. exact Hv.
Qed.


End ExtendedSVSymExecHavoc.
Print Assumptions ExtendedSVSymExecHavoc.hxexec_sound.
Print Assumptions ExtendedSVSymExecHavoc.hxrun_comb_lfp.
Print Assumptions ExtendedSVSymExecHavoc.hx_run_outs.
Print Assumptions ExtendedSVSymExecHavoc.hx2_out.
Print Assumptions ExtendedSVSymExecHavoc.hx_pass_sound.
