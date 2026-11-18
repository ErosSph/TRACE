(** Symbolic executor for NON-BLOCKING sequential processes (template route, additive; 2026-11-04).  generalized_rule.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    A sequential process whose body is a mix of [if]/[case]/non-blocking assignments (any number of statements, later assignments
    overriding earlier ones, whole-root and part-select/lane writes) is executed symbolically: every right-hand side, guard and
    lane offset is an expression over the DRIVEN state [s0] (non-blocking semantics), the result is an overlay root -> (width, expression)
    describing the value of the root after all pending updates are applied.  Branches are merged with [merge_if].
    [seq_nb_value]: the value of a register after a clock phase, when exactly one selected sequential process writes it.
    Replaces the decision-tree converter [ExtendedSVSeqTree.conv] for bodies that are not a single tree. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVConstantRoot
 Lang.ExtendedSVCombConnection Lang.ExtendedSVCombCut Lang.ExtendedSVAssignment Lang.ExtendedSVExprAgreement Lang.ExtendedSVSymExec
 Lang.ExtendedSVWordInvariant Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVExpressionFold Lang.ExtendedSVEval3 Lang.ExtendedSVEval4
 Lang.ExtendedSVProcessSlice Lang.ExtendedSVSeqTree.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVConstantRoot
 ExtendedSVCombConnection ExtendedSVCombCut ExtendedSVAssignment ExtendedSVExprAgreement ExtendedSVSymExec ExtendedSVWordInvariant ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVExpressionFold ExtendedSVEval3 ExtendedSVEval4 ExtendedSVProcessSlice ExtendedSVSeqTree.
Local Open Scope Z_scope.
Module ExtendedSVSymExecNb.

Fixpoint nselect (F:Facts) (v:Z) (arms:list (option Expr * Stmt)) (d:Stmt) : option Stmt :=
 match arms with
 | [] => Some d
 | (None,b)::rest => nselect F v rest b
 | (Some k,b)::rest =>
     match xeval4 F k with
     | Some kv => if Z.eqb v kv then Some b else nselect F v rest d
     | None => None end
 end.

Definition lane_old (ov:SOv) (W:nat) (r:signal) : option Expr :=
 match sov_lookup ov r with Some (W',eo) => if Nat.eqb W' W then Some eo else None | None => Some (EVar W r) end.

Fixpoint nbexec (F:Facts) (fuel:nat) (st:Stmt) (ov:SOv) {struct fuel} : option SOv :=
 match fuel with
 | O => Some ov
 | S f =>
  match st with
  | SSkip => Some ov
  | SAssign true rhs (LVar w r) => Some ((r,(w,rhs))::ov)
  | SAssign true rhs (LSel w (LVar W r) off) =>
      match lane_old ov W r with
      | Some eo => if Nat.leb w W then Some ((r,(W, patch W w eo off rhs))::ov) else None
      | None => None end
  | SAssign _ _ _ => None
  | SSeq l => fold_left (fun o st' => match o with Some ov' => nbexec F f st' ov' | None => None end) l (Some ov)
  | SIf g y n => match xeval4 F g with
      | Some z => nbexec F f (if Z.eqb z 0 then n else y) ov
      | None => match nbexec F f y ov, nbexec F f n ov with
          | Some oy, Some on => merge_if g ov oy on
          | _, _ => None end end
  | SCase scr arms =>
      match xeval4 F scr with
      | Some v => match nselect F v arms SSkip with
         | Some c => nbexec F f c ov | None => None end
      | None => None end
  end
 end.

Section Ext.
Variable F : Facts.
Lemma nfold_none_e : forall (l:list Stmt) f, fold_left (fun o st' => match o with Some ov' => nbexec F f st' ov' | None => None end) l None = None.
Proof. induction l; intros; cbn; [reflexivity|apply IHl]. Qed.

Theorem nbexec_ext : forall fuel st ov ov', nbexec F fuel st ov = Some ov' -> Ext ov ov'.
Proof.
 induction fuel as [|f IH]; intros st ov ov' H; cbn [nbexec] in H.
 - inversion H; subst. apply ext_refl.
 - destruct st as [|nba rhs lhs|l|g y n|scr arms].
   + inversion H; subst. apply ext_refl.
   + destruct nba; [|discriminate]. destruct lhs as [w r|w base off]; [|destruct base as [W r|]; [|discriminate]].
     * inversion H; subst. exists [(r,(w,rhs))]. reflexivity.
     * destruct (lane_old ov W r) as [eo|]; [|discriminate]. destruct (Nat.leb w W); [|discriminate].
       inversion H; subst. exists [(r,(W, patch W w eo off rhs))]. reflexivity.
   + assert (Hgen : forall l ov ov', fold_left (fun o st' => match o with Some ov' => nbexec F f st' ov' | None => None end) l (Some ov) = Some ov' -> Ext ov ov').
     { induction l0 as [|a rest IHl]; intros ov0 ov1 H0.
       - cbn in H0. inversion H0; subst. apply ext_refl.
       - cbn in H0. destruct (nbexec F f a ov0) as [o1|] eqn:Ea; [|rewrite nfold_none_e in H0; discriminate].
         exact (ext_trans _ _ _ (IH _ _ _ Ea) (IHl _ _ H0)). }
     exact (Hgen l ov ov' H).
   + destruct (xeval4 F g) as [z|].
     * exact (IH _ _ _ H).
     * destruct (nbexec F f y ov) as [oy|]; [|discriminate]. destruct (nbexec F f n ov) as [on|]; [|discriminate].
       unfold merge_if in H. destruct (merge_all g oy on _) as [m|]; [|discriminate]. inversion H; subst. exists m. reflexivity.
   + destruct (xeval4 F scr); [|discriminate]. destruct (nselect F z arms SSkip) as [c|]; [|discriminate]. exact (IH _ _ _ H).
Qed.
End Ext.

Section Sound.
Variable F : Facts.
Variable s0 : State.
Hypothesis HF : FactsHold s0 F.

Definition NInv (ov:SOv) (es:ExecState) : Prop :=
 blocking_state es = s0 /\ emitted_updates es = pending_nba es /\ Agree_s ov s0 (apply_nba s0 (pending_nba es)).

Lemma apply_nba_app : forall a b s, apply_nba s (a ++ b) = apply_nba (apply_nba s a) b.
Proof. induction a as [|u a IH]; intros b s; cbn; [reflexivity|apply IH]. Qed.

Lemma nselect_sound : forall arms v d c, nselect F v arms d = Some c -> select_case_stmt s0 v arms d = c.
Proof.
 induction arms as [|[[k|] b] rest IH]; intros v d c H; cbn [nselect] in H.
 - inversion H; reflexivity.
 - destruct (xeval4 F k) as [kv|] eqn:Ek; [|discriminate].
   cbn [select_case_stmt]. rewrite (xeval4_sound F s0 HF k kv Ek).
   destruct (Z.eqb v kv); [now inversion H|exact (IH _ _ _ H)].
 - cbn [select_case_stmt]. exact (IH _ _ _ H).
Qed.

Lemma agree_n_var ov s w r rhs : Agree_s ov s0 s ->
 Agree_s ((r,(w,rhs))::ov) s0 (apply_update s (resolve_update s0 (LVar w r) (eval_expr s0 rhs))).
Proof.
 intros [H1 H2].
 unfold apply_update, resolve_update. cbn [resolve_lvalue update_signal update_offset update_width update_value].
 split.
 - intros r' w' e' Hl. cbn [sov_lookup] in Hl.
   destruct (Nat.eqb r' r) eqn:Hr.
   + apply Nat.eqb_eq in Hr; subst. inversion Hl; subst.
     rewrite read_signal_write_same, norm_full_low_write. unfold norm. rewrite <- Z.land_assoc, Z.land_diag. reflexivity.
   + rewrite read_signal_write_other by (intro E; apply Nat.eqb_neq in Hr; congruence).
     exact (H1 _ _ _ Hl).
 - intros r' Hl. cbn [sov_lookup] in Hl.
   destruct (Nat.eqb r' r) eqn:Hr; [discriminate|].
   rewrite read_signal_write_other by (intro E; apply Nat.eqb_neq in Hr; congruence).
   exact (H2 _ Hl).
Qed.

Lemma agree_n_slice ov s W w r eo rhs off : Agree_s ov s0 s -> (w <= W)%nat ->
 lane_old ov W r = Some eo ->
 Agree_s ((r,(W, patch W w eo off rhs))::ov) s0
   (apply_update s (resolve_update s0 (LSel w (LVar W r) off) (eval_expr s0 rhs))).
Proof.
 intros HA Hw Hold.
 assert (HR : norm W (read_signal s r) = norm W (eval_expr s0 eo)).
 { destruct HA as [H1 H2]. unfold lane_old in Hold. destruct (sov_lookup ov r) as [[W' eo']|] eqn:Hl.
   - destruct (Nat.eqb W' W) eqn:HW; [|discriminate]. apply Nat.eqb_eq in HW; subst. inversion Hold; subst. exact (H1 _ _ _ Hl).
   - inversion Hold; subst. cbn [eval_expr]. rewrite (H2 _ Hl). unfold norm. rewrite <- Z.land_assoc, Z.land_diag. reflexivity. }
 destruct HA as [H1 H2].
 unfold apply_update, resolve_update. cbn [resolve_lvalue update_signal update_offset update_width update_value].
 split.
 - intros r' w' e' Hl. cbn [sov_lookup] in Hl.
   destruct (Nat.eqb r' r) eqn:Hr.
   + apply Nat.eqb_eq in Hr; subst. inversion Hl; subst.
     rewrite read_signal_write_same.
     rewrite (patch_arith _ w (read_signal s r) (eval_expr s0 eo) (eval_expr s0 off) (eval_expr s0 rhs) Hw (eval_nonneg s0 off) HR) by lia.
     cbn [patch eval_expr]. rewrite norm_idempotent. reflexivity.
   + rewrite read_signal_write_other by (intro E; apply Nat.eqb_neq in Hr; congruence).
     exact (H1 _ _ _ Hl).
 - intros r' Hl. cbn [sov_lookup] in Hl.
   destruct (Nat.eqb r' r) eqn:Hr; [discriminate|].
   rewrite read_signal_write_other by (intro E; apply Nat.eqb_neq in Hr; congruence).
   exact (H2 _ Hl).
Qed.

Theorem nbexec_sound : forall fuel st ov ov' es,
 nbexec F fuel st ov = Some ov' -> NInv ov es -> NInv ov' (exec_stmt fuel st es).
Proof.
 induction fuel as [|f IH]; intros st ov ov' es H HI.
 - cbn in H. inversion H; subst. exact HI.
 - destruct HI as [Hb [He HA]].
   destruct st as [|nba rhs lhs|l|g y n|scr arms]; cbn [nbexec] in H.
   + inversion H; subst. cbn. exact (conj Hb (conj He HA)).
   + destruct nba; [|discriminate].
     destruct lhs as [w r|w base off]; [|destruct base as [W r|]; [|discriminate]].
     * inversion H; subst. cbn [exec_stmt]. rewrite Hb.
       unfold NInv. cbn [blocking_state pending_nba emitted_updates]. split; [reflexivity|]. split.
       -- rewrite He. reflexivity.
       -- rewrite apply_nba_app. cbn [apply_nba]. exact (agree_n_var ov _ w r rhs HA).
     * destruct (lane_old ov W r) as [eo|] eqn:Hold; [|discriminate]. destruct (Nat.leb w W) eqn:Hle; [|discriminate].
       inversion H; subst. apply Nat.leb_le in Hle. cbn [exec_stmt]. rewrite Hb.
       unfold NInv. cbn [blocking_state pending_nba emitted_updates]. split; [reflexivity|]. split.
       -- rewrite He. reflexivity.
       -- rewrite apply_nba_app. cbn [apply_nba]. exact (agree_n_slice ov _ W w r eo rhs off HA Hle Hold).
   + cbn [exec_stmt].
     assert (Hgen: forall l ov ov' es,
        fold_left (fun o st' => match o with Some ov' => nbexec F f st' ov' | None => None end) l (Some ov) = Some ov' ->
        NInv ov es -> NInv ov' (fold_left (fun es' st' => exec_stmt f st' es') l es)).
     { induction l0 as [|a rest IHl]; intros ov0 ov1 es0 H0 HI0.
       - cbn in H0. inversion H0; subst. exact HI0.
       - cbn [fold_left] in H0 |- *. cbn in H0.
         destruct (nbexec F f a ov0) as [o1|] eqn:Ea; [|rewrite nfold_none_e in H0; discriminate].
         exact (IHl _ _ _ H0 (IH _ _ _ es0 Ea HI0)). }
     exact (Hgen l ov ov' es H (conj Hb (conj He HA))).
   + cbn [exec_stmt]. rewrite Hb.
     destruct (xeval4 F g) as [z|] eqn:Ez.
     * rewrite (xeval4_sound F s0 HF g z Ez). exact (IH _ _ _ _ H (conj Hb (conj He HA))).
     * destruct (nbexec F f y ov) as [oy|] eqn:Ey; [|discriminate]. destruct (nbexec F f n ov) as [on|] eqn:En; [|discriminate].
       pose proof (IH y ov oy es Ey (conj Hb (conj He HA))) as [Byy [Eyy Ay]].
       pose proof (IH n ov on es En (conj Hb (conj He HA))) as [Bn [En' An]].
       destruct (Z.eqb_spec (eval_expr s0 g) 0) as [Hz|Hz].
       -- refine (conj Bn (conj En' _)).
          exact (merge_if_sound s0 g ov oy on ov' _ _ _ H (nbexec_ext F _ _ _ _ Ey) (nbexec_ext F _ _ _ _ En) Ay An (or_intror (conj Hz eq_refl))).
       -- refine (conj Byy (conj Eyy _)).
          exact (merge_if_sound s0 g ov oy on ov' _ _ _ H (nbexec_ext F _ _ _ _ Ey) (nbexec_ext F _ _ _ _ En) Ay An (or_introl (conj Hz eq_refl))).
   + cbn [exec_stmt]. rewrite Hb.
     destruct (xeval4 F scr) as [v|] eqn:Ev; [|discriminate].
     destruct (nselect F v arms SSkip) as [c|] eqn:Ec; [|discriminate].
     rewrite (xeval4_sound F s0 HF scr v Ev), (nselect_sound _ _ _ _ Ec).
     exact (IH _ _ _ _ H (conj Hb (conj He HA))).
Qed.
End Sound.

Lemma apply_updates_nba : forall l s, apply_updates s l = apply_nba s l.
Proof. induction l as [|u l IH]; intros s; cbn; [reflexivity|apply IH]. Qed.

(** Phase level: the value of a register after a clock phase when exactly one selected sequential process writes it. *)
Theorem seq_nb_value p ev pre r P F ov w e :
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 FactsHold (phase_driven_state p ev pre) F ->
 nbexec F (statement_fuel p) (process_body P) [] = Some ov -> sov_lookup ov r = Some (w,e) ->
 norm w (read_signal (PhaseSemantics p ev pre) r) = norm w (eval_expr (phase_driven_state p ev pre) e).
Proof.
 intros HU HE HW HFH Hx Hl.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain, selected_on_transition.
 rewrite process_slice_sound.
 rewrite filter_swap, HW. cbn [flat_map]. rewrite app_nil_r.
 rewrite <- (driven_unchanged p ev pre r HU HE).
 rewrite <- read_signal_apply_updates.
 set (driven := phase_driven_state p ev pre) in *.
 pose proof (nbexec_sound F driven HFH (statement_fuel p) (process_body P) [] ov
   {| blocking_state := driven; pending_nba := []; emitted_updates := [] |} Hx
   (conj eq_refl (conj eq_refl (agree_s_nil driven)))) as [_ [He [HA1 _]]].
 unfold process_updates. rewrite He, apply_updates_nba. exact (HA1 r w e Hl).
Qed.

(** hold: a register the process leaves out keeps its value *)
Theorem seq_nb_hold p ev pre r P F ov :
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 FactsHold (phase_driven_state p ev pre) F ->
 nbexec F (statement_fuel p) (process_body P) [] = Some ov -> sov_lookup ov r = None ->
 read_signal (PhaseSemantics p ev pre) r = read_signal pre r.
Proof.
 intros HU HE HW HFH Hx Hl.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain, selected_on_transition.
 rewrite process_slice_sound.
 rewrite filter_swap, HW. cbn [flat_map]. rewrite app_nil_r.
 rewrite <- (driven_unchanged p ev pre r HU HE).
 rewrite <- read_signal_apply_updates.
 set (driven := phase_driven_state p ev pre) in *.
 pose proof (nbexec_sound F driven HFH (statement_fuel p) (process_body P) [] ov
   {| blocking_state := driven; pending_nba := []; emitted_updates := [] |} Hx
   (conj eq_refl (conj eq_refl (agree_s_nil driven)))) as [_ [He [_ HA2]]].
 unfold process_updates. rewrite He, apply_updates_nba. rewrite (HA2 r Hl).
 reflexivity.
Qed.

Definition nb_out_chk (F:Facts) (ov:SOv) (r:signal) (w:nat) (X:Expr) : bool :=
 match sov_lookup ov r with
 | Some (w',e) => Nat.eqb w w' && (if expr_eq_dec (simp4 F e) X then true else false)
 | None => false end.

(** the register value after the phase, as a decided small expression over the driven state *)
Theorem seq_nb_out p ev pre r P F ov w X :
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 FactsHold (phase_driven_state p ev pre) F ->
 nbexec F (statement_fuel p) (process_body P) [] = Some ov -> nb_out_chk F ov r w X = true ->
 norm w (read_signal (PhaseSemantics p ev pre) r) = norm w (eval_expr (phase_driven_state p ev pre) X).
Proof.
 intros HU HE HW HFH Hx Hc. unfold nb_out_chk in Hc.
 destruct (sov_lookup ov r) as [[w' e]|] eqn:Hl; [|discriminate].
 apply andb_true_iff in Hc as [Hw Hs]. apply Nat.eqb_eq in Hw. subst w'.
 destruct (expr_eq_dec (simp4 F e) X) as [Hxe|]; [|discriminate]. subst X.
 rewrite (simp4_sound F (phase_driven_state p ev pre) HFH e).
 exact (seq_nb_value p ev pre r P F ov w e HU HE HW HFH Hx Hl).
Qed.


Definition nb_chk2 (F:Facts) (fuel:nat) (body:Stmt) (r:signal) (w:nat) (X:Expr) : bool :=
 match nbexec F fuel body [] with Some ov => nb_out_chk F ov r w X | None => false end.

Theorem seq_nb_out2 p ev pre r P F w X :
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 FactsHold (phase_driven_state p ev pre) F ->
 nb_chk2 F (statement_fuel p) (process_body P) r w X = true ->
 norm w (read_signal (PhaseSemantics p ev pre) r) = norm w (eval_expr (phase_driven_state p ev pre) X).
Proof.
 intros HU HE HW HFH Hc. unfold nb_chk2 in Hc.
 destruct (nbexec F (statement_fuel p) (process_body P) []) as [ov|] eqn:Hx; [|discriminate].
 exact (seq_nb_out p ev pre r P F ov w X HU HE HW HFH Hx Hc).
Qed.

Lemma hw_from_sel p pre d r L : selected_on_transition p pre d = L ->
 filter (process_matches_states pre d) (filter (writes_rootb r) (processes p)) = filter (writes_rootb r) L.
Proof.
 intro H. rewrite filter_swap. f_equal. exact H.
Qed.

End ExtendedSVSymExecNb.
Print Assumptions ExtendedSVSymExecNb.nbexec_sound.
Print Assumptions ExtendedSVSymExecNb.seq_nb_value.
Print Assumptions ExtendedSVSymExecNb.seq_nb_hold.
Print Assumptions ExtendedSVSymExecNb.seq_nb_out.
Print Assumptions ExtendedSVSymExecNb.seq_nb_out2.
