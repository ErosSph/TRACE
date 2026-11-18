(** Slice-overlay path executor for blocking combinational processes (template route, 2026-11-03).

    Generic, design independent.  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.

    [ExtendedSVSymAlias.pex] rejects partial writes.  Here [sx] runs a blocking comb process along the path chosen by
    constant facts (every guard / case scrutinee is decided by the facts, nothing written earlier is read), and keeps for
    every written root an overlay of slice equations [(r, l, w, e)] : "bits [l .. l+w-1] of root r hold [e]".  A write
    [r[l +: w] = rhs] with a constant [l] (also [LVar w r], which is the slice (0,w)) replaces the overlapped slices and
    adds the new one; so the later write of the adder gap bits (set to 1, then cleared in the subtract branch) simply
    replaces the earlier slice.  Information about a larger slice that is partly overwritten is dropped (never wrong).
    The right-hand side is evaluated in the state in which the process starts ([unwrittenb ov rhs]).

    Soundness: [sx_sound] (against [exec_stmt] = [resolve_update] + [apply_update] = [write_slice]).
    Transfer to the combinational fixed point: a slice written by the process at comb position [k] holds at [fixed]
    if (a) its right-hand side reads roots that are either not written by the prefix, or not written from [k] on
    (the pivot-input condition of ExtendedSVFactChain / SymAlias), and (b) no LATER process may touch the bits
    ([late_okb], checked through the writer table [T]).  A root written by many single-slice processes (generate loops)
    therefore needs no special treatment: every process contributes its own slices, and the facts are combined
    by the chain [slchain] exactly as in ExtendedSVFactChain.  Nothing is assumed: the facts are hypotheses. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVConstantRoot
 Lang.ExtendedSVCombConnection Lang.ExtendedSVCombCut Lang.ExtendedSVExprAgreement
 Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymAlias Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVSliceBits.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVConstantRoot
 ExtendedSVCombConnection ExtendedSVCombCut ExtendedSVExprAgreement
 ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymAlias ExtendedSVWordInvariant ExtendedSVSliceBits.
Local Open Scope Z_scope.
Module ExtendedSVSliceExec.

Definition SEqn := (signal * Z * nat * Expr)%type.

Definition const_lsb (e:Expr) : option Z := match e with EConst k c => Some (norm k c) | _ => None end.

Definition disjointb (l1:Z) (w1:nat) (l2:Z) (w2:nat) : bool :=
 (l2 + Z.of_nat w2 <=? l1) || (l1 + Z.of_nat w1 <=? l2).

Definition drop_overlap (r:signal) (l:Z) (w:nat) (sl:list SEqn) : list SEqn :=
 filter (fun q => match q with (r',l',w',_) => negb (Nat.eqb r' r) || disjointb l w l' w' end) sl.

(** ---- the executor ---- *)
Fixpoint sx (F:Facts) (fuel:nat) (st:Stmt) (ov:Ov) (sl:list SEqn) {struct fuel} : option (Ov * list SEqn) :=
 match fuel with
 | O => Some (ov,sl)
 | S f =>
  match st with
  | SSkip => Some (ov,sl)
  | SAssign false rhs lhs =>
     if unwrittenb ov rhs then
      match lhs with
      | LVar w r => Some ((r,(0%nat,0))::ov, (r,0,w,simp F rhs)::drop_overlap r 0 w sl)
      | LSel w (LVar _ r) lsb =>
         match const_lsb lsb with
         | Some l => Some ((r,(0%nat,0))::ov, (r,l,w,simp F rhs)::drop_overlap r l w sl)
         | None => None end
      | LSel _ _ _ => None
      end
     else None
  | SAssign true _ _ => None
  | SSeq l => fold_left (fun o st' => match o with Some (ov',sl') => sx F f st' ov' sl' | None => None end) l (Some (ov,sl))
  | SIf g y n => match ceval F ov g with
     | Some z => sx F f (if Z.eqb z 0 then n else y) ov sl | None => None end
  | SCase scr arms => match ceval F ov scr with
     | Some v => match cselect F ov v arms SSkip with
        | Some c => sx F f c ov sl | None => None end
     | None => None end
  end
 end.

Definition AgreeS (s0:State) (ov:Ov) (sl:list SEqn) (s:State) : Prop :=
 (forall r, ov_lookup ov r = None -> read_signal s r = read_signal s0 r) /\
 (forall r l w e, In (r,l,w,e) sl -> 0 <= l /\ norm w (Z.shiftr (read_signal s r) l) = norm w (eval_expr s0 e)).

Lemma agreeS_upd s0 ov sl s r l w v e :
 AgreeS s0 ov sl s -> 0 <= l -> v = eval_expr s0 e ->
 AgreeS s0 ((r,(0%nat,0))::ov) ((r,l,w,e)::drop_overlap r l w sl)
  (apply_update s {| update_signal := r; update_offset := l; update_width := w; update_value := norm w v |}).
Proof.
 intros [H1 H2] Hl Hv. unfold apply_update. cbn [update_signal update_offset update_width update_value].
 split.
 - intros r' Hl'. cbn [ov_lookup] in Hl'. destruct (Nat.eqb r' r) eqn:Hr; [discriminate|].
   apply Nat.eqb_neq in Hr. rewrite read_signal_write_other by congruence. exact (H1 _ Hl').
 - intros r' l' w' e' Hin. destruct Hin as [Hin|Hin].
   + inversion Hin; subst. split; [exact Hl|]. rewrite read_signal_write_same.
     rewrite (slice_after_write_nat (read_signal s r') l' w' (norm w' (eval_expr s0 e')) Hl).
     rewrite norm_idempotent. reflexivity.
   + unfold drop_overlap in Hin. apply filter_In in Hin as [Hin Hf].
     destruct (H2 _ _ _ _ Hin) as [Hl' Hv']. split; [exact Hl'|].
     cbn beta in Hf. apply orb_true_iff in Hf as [Hf|Hf].
     * apply negb_true_iff in Hf. apply Nat.eqb_neq in Hf.
       rewrite read_signal_write_other by congruence. exact Hv'.
     * unfold disjointb in Hf. apply orb_true_iff in Hf as [Hf|Hf]; apply Z.leb_le in Hf.
       -- destruct (Nat.eq_dec r' r) as [->|Hn].
          ++ rewrite read_signal_write_same. rewrite (slice_disjoint_nat (read_signal s r) l w (norm w v) l' w' Hl Hl'); [exact Hv'|lia].
          ++ rewrite read_signal_write_other by congruence. exact Hv'.
       -- destruct (Nat.eq_dec r' r) as [->|Hn].
          ++ rewrite read_signal_write_same. rewrite (slice_disjoint_nat (read_signal s r) l w (norm w v) l' w' Hl Hl'); [exact Hv'|lia].
          ++ rewrite read_signal_write_other by congruence. exact Hv'.
Qed.

Section Sound.
Variable F : Facts.
Variable s0 : State.
Hypothesis HF : FactsHold s0 F.

Lemma agreeS_E ov sl s : AgreeS s0 ov sl s -> AgreeE s0 ov [] s.
Proof. intros [H1 _]. split; [exact H1|intros w r e Hin; contradiction]. Qed.

Lemma sx_fold_none : forall (l:list Stmt) f, fold_left (fun o st' => match o with Some (ov',sl') => sx F f st' ov' sl' | None => None end) l None = None.
Proof. induction l; intros; cbn; [reflexivity|apply IHl]. Qed.

Theorem sx_sound : forall fuel st ov sl ov' sl' es,
 sx F fuel st ov sl = Some (ov',sl') -> AgreeS s0 ov sl (blocking_state es) ->
 AgreeS s0 ov' sl' (blocking_state (exec_stmt fuel st es)) /\
 pending_nba (exec_stmt fuel st es) = pending_nba es.
Proof.
 induction fuel as [|f IH]; intros st ov sl ov' sl' es H HA.
 - cbn in H. inversion H; subst. cbn. split; [exact HA|reflexivity].
 - destruct st as [|nba rhs lhs|l|g y n|scr arms]; cbn [sx exec_stmt] in *.
   + inversion H; subst. split; [exact HA|reflexivity].
   + destruct nba; [discriminate|].
     destruct (unwrittenb ov rhs) eqn:Hu; [|discriminate].
     assert (Hv : eval_expr (blocking_state es) rhs = eval_expr s0 (simp F rhs)).
     { rewrite (simp_sound F s0 HF rhs).
       exact (unwritten_agree s0 ov rhs (blocking_state es) (proj1 HA) Hu). }
     cbn [pending_nba blocking_state].
     destruct lhs as [w r|w base lsb].
     * inversion H; subst; clear H. split; [|reflexivity].
       unfold resolve_update. cbn [resolve_lvalue].
       exact (agreeS_upd s0 ov sl _ r 0 w _ (simp F rhs) HA (Z.le_refl 0) Hv).
     * destruct base as [W r|]; [|discriminate].
       destruct lsb as [k c| | | | | | | |]; try discriminate.
       cbn [const_lsb] in H. inversion H; subst; clear H. split; [|reflexivity].
       unfold resolve_update. cbn [resolve_lvalue eval_expr].
       replace (0 + norm k c) with (norm k c) by lia.
       exact (agreeS_upd s0 ov sl _ r (norm k c) w _ (simp F rhs) HA (norm_nonneg k c) Hv).
   + assert (Hgen: forall l ov sl ov' sl' es,
        fold_left (fun o st' => match o with Some (ov',sl') => sx F f st' ov' sl' | None => None end) l (Some (ov,sl)) = Some (ov',sl') ->
        AgreeS s0 ov sl (blocking_state es) ->
        AgreeS s0 ov' sl' (blocking_state (fold_left (fun es' st' => exec_stmt f st' es') l es)) /\
        pending_nba (fold_left (fun es' st' => exec_stmt f st' es') l es) = pending_nba es).
     { induction l0 as [|a rest IHl]; intros ov0 sl0 ov1 sl1 es0 H0 HA0.
       - cbn in H0. inversion H0; subst. cbn. split; [exact HA0|reflexivity].
       - cbn [fold_left] in H0 |- *. cbn in H0.
         destruct (sx F f a ov0 sl0) as [[o1 a1]|] eqn:Ea; [|rewrite sx_fold_none in H0; discriminate].
         destruct (IH _ _ _ _ _ es0 Ea HA0) as [HA1 HP1].
         destruct (IHl _ _ _ _ _ H0 HA1) as [HA2 HP2]. split; [exact HA2|congruence]. }
     exact (Hgen l ov sl ov' sl' es H HA).
   + destruct (ceval F ov g) as [z|] eqn:Ez; [|discriminate].
     rewrite (ceval_sound F s0 HF _ _ _ _ _ (agreeS_E _ _ _ HA) Ez). exact (IH _ _ _ _ _ _ H HA).
   + destruct (ceval F ov scr) as [v|] eqn:Ev; [|discriminate].
     destruct (cselect F ov v arms SSkip) as [c|] eqn:Ec; [|discriminate].
     rewrite (ceval_sound F s0 HF _ _ _ _ _ (agreeS_E _ _ _ HA) Ev), (cselect_sound F s0 HF _ _ _ _ _ _ _ (agreeS_E _ _ _ HA) Ec).
     exact (IH _ _ _ _ _ _ H HA).
Qed.

Theorem srun_sound p proc ov sl :
 sx F (statement_fuel p) (nbfix (process_body proc)) [] [] = Some (ov,sl) ->
 forall r l w e, In (r,l,w,e) sl -> 0 <= l /\ norm w (Z.shiftr (read_signal (run_process p s0 proc) r) l) = norm w (eval_expr s0 e).
Proof.
 intros H r l w e Hin. rewrite run_process_nbfix. unfold run_process. cbn [process_body].
 assert (HA : AgreeS s0 [] [] (blocking_state {|blocking_state:=s0;pending_nba:=[];emitted_updates:=[]|})).
 { split; [intros; reflexivity|intros r0 l0 w0 e0 H0; contradiction]. }
 destruct (sx_sound _ _ _ _ _ _ _ H HA) as [[_ HA2] HP].
 cbn [pending_nba] in HP. rewrite HP. cbn [apply_nba]. exact (HA2 _ _ _ _ Hin).
Qed.
End Sound.

(** ---- bits a process may touch (static footprint) ---- *)
Fixpoint touches (st:Stmt) (r:signal) (l:Z) (w:nat) : bool :=
 match st with
 | SSkip => false
 | SAssign nba _ lhs => nba || (Nat.eqb (lvalue_root lhs) r &&
     match lhs with
     | LVar w' _ => negb (disjointb l w 0 w')
     | LSel w' (LVar _ _) lsb => match const_lsb lsb with Some l' => negb (disjointb l w l' w') | None => true end
     | LSel _ _ _ => true end)
 | SSeq ss => existsb (fun s' => touches s' r l w) ss
 | SIf _ y n => touches y r l w || touches n r l w
 | SCase _ arms => existsb (fun a => touches (snd a) r l w) arms
 end.

Lemma select_untouched r l w s v : forall arms d, existsb (fun a => touches (snd a) r l w) arms = false -> touches d r l w = false ->
 touches (select_case_stmt s v arms d) r l w = false.
Proof.
 induction arms as [|[[k|] b] rest IH]; intros d Ha Hd; cbn [select_case_stmt]; [exact Hd| |].
 - cbn [existsb snd] in Ha. apply orb_false_iff in Ha as [Hb Hr].
   destruct (Z.eqb v (eval_expr s k)); [exact Hb|exact (IH d Hr Hd)].
 - cbn [existsb snd] in Ha. apply orb_false_iff in Ha as [Hb Hr]. exact (IH b Hr Hb).
Qed.

Lemma resolve_root s lv : fst (fst (resolve_lvalue s lv)) = lvalue_root lv.
Proof.
 induction lv as [w x|w base IH lsb]; cbn [resolve_lvalue lvalue_root]; [reflexivity|].
 destruct (resolve_lvalue s base) as [[id off] wd]. cbn [fst] in IH |- *. exact IH.
Qed.

Lemma update_root s lv v : update_signal (resolve_update s lv v) = lvalue_root lv.
Proof.
 unfold resolve_update. pose proof (resolve_root s lv) as H.
 destruct (resolve_lvalue s lv) as [[id off] wd]. cbn [fst] in H. cbn. exact H.
Qed.

Lemma exec_keeps r l w : 0 <= l -> forall fuel st es, touches st r l w = false ->
 norm w (Z.shiftr (read_signal (blocking_state (exec_stmt fuel st es)) r) l) = norm w (Z.shiftr (read_signal (blocking_state es) r) l) /\
 pending_nba (exec_stmt fuel st es) = pending_nba es.
Proof.
 intros Hl. induction fuel as [|f IH]; intros st es Ht.
 - cbn. split; reflexivity.
 - destruct st as [|nba rhs lhs|ss|g y n|scr arms]; cbn [exec_stmt]; cbn [touches] in Ht.
   + split; reflexivity.
   + apply orb_false_iff in Ht as [Hn Ht]. subst nba.
     cbn [blocking_state pending_nba]. split; [|reflexivity].
     destruct (Nat.eq_dec (lvalue_root lhs) r) as [Heq|Hne].
     * unfold apply_update, resolve_update. rewrite Heq in Ht. rewrite Nat.eqb_refl, andb_true_l in Ht.
       destruct lhs as [w' x|w' base lsb]; cbn [lvalue_root] in Heq.
       -- subst x. cbn [resolve_lvalue update_signal update_offset update_width update_value].
          apply negb_false_iff in Ht. unfold disjointb in Ht.
          rewrite read_signal_write_same. apply orb_true_iff in Ht as [Ht|Ht]; apply Z.leb_le in Ht;
          (rewrite (slice_disjoint_nat (read_signal (blocking_state es) r) 0 w' (norm w' (eval_expr (blocking_state es) rhs)) l w (Z.le_refl 0) Hl); [reflexivity|lia]).
       -- destruct base as [W x|]; [|discriminate Ht]. cbn [lvalue_root] in Heq. subst x.
          destruct (const_lsb lsb) as [l'|] eqn:Hc; [|discriminate Ht].
          destruct lsb as [k c| | | | | | | |]; try discriminate. cbn [const_lsb] in Hc. inversion Hc; subst l'; clear Hc.
          cbn [resolve_lvalue eval_expr update_signal update_offset update_width update_value].
          replace (0 + norm k c) with (norm k c) by lia.
          apply negb_false_iff in Ht. unfold disjointb in Ht.
          rewrite read_signal_write_same. apply orb_true_iff in Ht as [Ht|Ht]; apply Z.leb_le in Ht;
          (rewrite (slice_disjoint_nat (read_signal (blocking_state es) r) (norm k c) w' (norm w' (eval_expr (blocking_state es) rhs)) l w (norm_nonneg k c) Hl); [reflexivity|lia]).
     * unfold apply_update. rewrite read_signal_write_other; [reflexivity|].
       rewrite (update_root (blocking_state es) lhs). congruence.
   + assert (Hgen: forall l0 es0, existsb (fun s' => touches s' r l w) l0 = false ->
        norm w (Z.shiftr (read_signal (blocking_state (fold_left (fun es' st' => exec_stmt f st' es') l0 es0)) r) l) = norm w (Z.shiftr (read_signal (blocking_state es0) r) l) /\
        pending_nba (fold_left (fun es' st' => exec_stmt f st' es') l0 es0) = pending_nba es0).
     { induction l0 as [|a rest IHl]; intros es0 H0; cbn [fold_left]; [split; reflexivity|].
       cbn [existsb] in H0. apply orb_false_iff in H0 as [Ha Hr].
       destruct (IH a es0 Ha) as [A1 A2]. destruct (IHl (exec_stmt f a es0) Hr) as [B1 B2]. split; congruence. }
     exact (Hgen ss es Ht).
   + apply orb_false_iff in Ht as [Hy Hn]. destruct (Z.eqb (eval_expr (blocking_state es) g) 0); [exact (IH n es Hn)|exact (IH y es Hy)].
   + exact (IH _ es (select_untouched r l w _ _ arms SSkip Ht eq_refl)).
Qed.

Lemma run_process_keeps p proc r l w s : 0 <= l -> touches (nbfix (process_body proc)) r l w = false ->
 norm w (Z.shiftr (read_signal (run_process p s proc) r) l) = norm w (Z.shiftr (read_signal s r) l).
Proof.
 intros Hl Ht. rewrite run_process_nbfix. unfold run_process. cbn [process_body].
 destruct (exec_keeps r l w Hl (statement_fuel p) _ {|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|} Ht) as [H1 H2].
 cbn [pending_nba blocking_state] in H1, H2. rewrite H2. cbn [apply_nba]. exact H1.
Qed.

(** ---- the writer table says which later processes could touch the bits ---- *)
Definition late_okb (ps:list Process) (T:list (list nat)) (k:nat) (r:signal) (l:Z) (w:nat) : bool :=
 forallb (fun j => Nat.leb j k || match nth_error ps j with Some pr => negb (touches (nbfix (process_body pr)) r l w) | None => false end) (nth r T []).

Lemma suffix_keeps p r l w : forall suf s,
 (forall pr, In pr suf -> forall s', norm w (Z.shiftr (read_signal (run_process p s' pr) r) l) = norm w (Z.shiftr (read_signal s' r) l)) ->
 norm w (Z.shiftr (read_signal (fold_left (run_process p) suf s) r) l) = norm w (Z.shiftr (read_signal s r) l).
Proof.
 induction suf as [|pr rest IH]; intros s H; cbn [fold_left]; [reflexivity|].
 rewrite IH by (intros pr' Hin; apply H; right; exact Hin).
 apply H. left. reflexivity.
Qed.

Lemma late_keeps p ps T k r l w : 0 <= l -> TabC ps T -> late_okb ps T k r l w = true ->
 forall pr, In pr (skipn (S k) ps) -> forall s, norm w (Z.shiftr (read_signal (run_process p s pr) r) l) = norm w (Z.shiftr (read_signal s r) l).
Proof.
 intros Hl HT Hlate pr Hin s. destruct (in_skipn_idx ps (S k) pr Hin) as [i HN].
 destruct (existsb (Nat.eqb r) (process_writers pr)) eqn:Ew.
 - apply existsb_exists in Ew as [y [Hy Ey]]. apply Nat.eqb_eq in Ey. subst y.
   pose proof (HT (S k + i)%nat pr r HN Hy) as Hin2.
   unfold late_okb in Hlate. rewrite forallb_forall in Hlate. specialize (Hlate _ Hin2).
   apply orb_true_iff in Hlate as [Hle|Hlate].
   + apply Nat.leb_le in Hle. lia.
   + rewrite HN in Hlate. apply negb_true_iff in Hlate. exact (run_process_keeps p pr r l w s Hl Hlate).
 - assert (Hnw : ~ In r (process_writers pr)).
   { intro Hc. assert (E : existsb (Nat.eqb r) (process_writers pr) = true) by (apply existsb_exists; exists r; split; [exact Hc|apply Nat.eqb_refl]).
     rewrite Ew in E. discriminate. }
   pose proof (fold_run_process_preserves_root p [pr] r s (ltac:(intros p' [<-|[]]; exact Hnw))) as H.
   cbn [fold_left] in H. rewrite H. reflexivity.
Qed.

(** ---- transfer to the combinational fixed point ---- *)
Definition inputs_okb (T:list (list nat)) (k:nat) (e:Expr) : bool :=
 forallb (fun wr => wr_ge T (snd wr) k || wr_lt T (snd wr) k) (expr_inputs e).

Lemma inputs_agree p ps T k proc seed fixed e :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc -> CombLFP p seed fixed ->
 inputs_okb T k e = true ->
 eval_expr (fold_left (run_process p) (firstn k ps) fixed) e = eval_expr fixed e.
Proof.
 intros HP HT HN HL Hq. pose proof (eq_trans HP (split_at ps k proc HN)) as Horder.
 apply eval_expr_agree. intros wd x Hin'.
 unfold inputs_okb in Hq. rewrite forallb_forall in Hq. specialize (Hq (wd,x) Hin'). cbn [snd] in Hq.
 apply orb_true_iff in Hq as [Hq|Hq].
 - rewrite (fold_run_process_preserves_root p (firstn k ps) x fixed (roots_unwrittenb_sound _ _ (unw_prefix ps T k x HT Hq))). reflexivity.
 - rewrite (actual_lfp_pivot_input p (firstn k ps) proc (skipn (S k) ps) x seed fixed Horder
     (eq_ind (skipn k ps) (fun l => roots_unwrittenb x l = true) (unw_suffix ps T k x HT Hq) _ (skipn_nth_cons ps k proc HN)) HL). reflexivity.
Qed.

Definition sl_okb (ps:list Process) (T:list (list nat)) (k:nat) (q:SEqn) : bool :=
 match q with (r,l,w,e) => inputs_okb T k e && late_okb ps T k r l w end.

Theorem prun_slices_comb_lfp p ps T k proc F ov sl seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc ->
 (forall e z, In (e,z) F -> inputs_okb T k e = true) ->
 FactsHold fixed F -> CombLFP p seed fixed ->
 sx F (statement_fuel p) (nbfix (process_body proc)) [] [] = Some (ov,sl) ->
 forall r l w e, In (r,l,w,e) (filter (sl_okb ps T k) sl) -> SliceEq fixed r l w e.
Proof.
 intros HP HT HN Hok HFH HL Hx r l w e Hin.
 apply filter_In in Hin as [Hin Hq]. cbn [sl_okb] in Hq. apply andb_true_iff in Hq as [Hq Hlate].
 set (Sk := fold_left (run_process p) (firstn k ps) fixed) in *.
 assert (H0 : FactsHold Sk F).
 { intros e0 z HI. rewrite <- (HFH _ _ HI). exact (inputs_agree p ps T k proc seed fixed e0 HP HT HN HL (Hok _ _ HI)). }
 destruct (srun_sound F Sk H0 p proc ov sl Hx r l w e Hin) as [Hl Hv].
 split; [exact Hl|].
 assert (Hfx : fold_left (run_process p) ps fixed = fixed).
 { destruct HL as [n fixed' Hit Hfixed]. unfold comb_round in Hfixed. rewrite HP in Hfixed. exact Hfixed. }
 assert (E : fold_left (run_process p) ps fixed = fold_left (run_process p) (skipn (S k) ps) (run_process p Sk proc)).
 { transitivity (fold_left (run_process p) (firstn k ps ++ proc :: skipn (S k) ps) fixed);
   [f_equal; exact (split_at ps k proc HN)|rewrite fold_left_app; reflexivity]. }
 assert (Hr : read_signal fixed r = read_signal (fold_left (run_process p) (skipn (S k) ps) (run_process p Sk proc)) r)
  by (rewrite <- E, Hfx; reflexivity).
 rewrite Hr.
 rewrite (suffix_keeps p r l w (skipn (S k) ps) (run_process p Sk proc) (late_keeps p ps T k r l w Hl HT Hlate)).
 rewrite Hv. f_equal. exact (inputs_agree p ps T k proc seed fixed e HP HT HN HL Hq).
Qed.

(** ---- chain over comb positions (like ExtendedSVFactChain.chain) ---- *)
Definition sstep (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (st:nat*list nat) : option (list SEqn) :=
 let k := fst st in
 match nth_error ps k with
 | None => None
 | Some proc =>
   match sx (filter (tail_okb T k) (pick F (snd st))) fuel (nbfix (process_body proc)) [] [] with
   | None => None
   | Some (_,sl) => Some (filter (sl_okb ps T k) sl)
   end
 end.

Fixpoint slchain (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (ks:list (nat*list nat)) : option (list SEqn) :=
 match ks with
 | [] => Some []
 | k::rest => match sstep ps T fuel F k with
    | Some E => match slchain ps T fuel F rest with Some E' => Some (E ++ E') | None => None end
    | None => None end
 end.

Theorem slchain_sound p ps T fuel (ks:list (nat*list nat)) : forall F E seed fixed,
 filter is_comb (processes p) = ps -> TabC ps T -> fuel = statement_fuel p ->
 FactsHold fixed F -> CombLFP p seed fixed -> slchain ps T fuel F ks = Some E -> SliceHold fixed E.
Proof.
 induction ks as [|k rest IH]; intros F E seed fixed HP HT Hf HFH HL H; cbn [slchain] in H.
 - inversion H; subst. intros r l w e Hin. contradiction.
 - destruct (sstep ps T fuel F k) as [E1|] eqn:Hs; [|discriminate].
   destruct (slchain ps T fuel F rest) as [E2|] eqn:Hc; [|discriminate]. inversion H; subst E; clear H.
   intros r l w e Hin. apply in_app_or in Hin as [Hin|Hin].
   + unfold sstep in Hs. subst fuel.
     destruct (nth_error ps (fst k)) as [proc|] eqn:HN; [|discriminate].
     destruct (sx (filter (tail_okb T (fst k)) (pick F (snd k))) (statement_fuel p) (nbfix (process_body proc)) [] []) as [[ov sl]|] eqn:Hx; [|discriminate].
     inversion Hs; subst E1; clear Hs.
     set (F0 := filter (tail_okb T (fst k)) (pick F (snd k))) in *.
     assert (H0: FactsHold fixed F0).
     { intros e0 z HI. apply filter_In in HI as [HI _]. apply HFH, (pick_in _ _ _ HI). }
     assert (Hok: forall e z, In (e,z) F0 -> inputs_okb T (fst k) e = true).
     { intros e1 z1 HI. apply filter_In in HI as [_ HT']. exact HT'. }
     exact (prun_slices_comb_lfp p ps T (fst k) proc F0 ov sl seed fixed HP HT HN Hok H0 HL Hx r l w e Hin).
   + exact (IH F E2 seed fixed HP HT Hf HFH HL Hc r l w e Hin).
Qed.

(** Statement forms the generators produce: a list of wanted slice equations, each present in the chain output. *)
Definition seqn_eq_dec : forall a b : SEqn, {a=b}+{a<>b}.
Proof.
 intros [[[r1 l1] w1] e1] [[[r2 l2] w2] e2].
 destruct (Nat.eq_dec r1 r2), (Z.eq_dec l1 l2), (Nat.eq_dec w1 w2), (expr_eq_dec e1 e2); subst;
  try (left; reflexivity); right; intro H; inversion H; congruence.
Defined.

Definition slices_in_okb (E want:list SEqn) : bool :=
 forallb (fun q => if in_dec seqn_eq_dec q E then true else false) want.

Lemma slices_in_sound s E want : slices_in_okb E want = true -> SliceHold s E -> SliceHold s want.
Proof.
 intros H HE r l w e Hin. unfold slices_in_okb in H. rewrite forallb_forall in H.
 specialize (H _ Hin). destruct (in_dec seqn_eq_dec (r,l,w,e) E) as [Hi|]; [|discriminate]. exact (HE _ _ _ _ Hi).
Qed.

Theorem slchain_out p ps T ks F0 want seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T ->
 FactsHold fixed F0 -> CombLFP p seed fixed ->
 (match slchain ps T (statement_fuel p) F0 ks with Some E => slices_in_okb E want | None => false end) = true ->
 SliceHold fixed want.
Proof.
 intros HP HT HFH HL H.
 destruct (slchain ps T (statement_fuel p) F0 ks) as [E|] eqn:Hc; [|discriminate].
 exact (slices_in_sound fixed E want H (slchain_sound p ps T (statement_fuel p) ks F0 E seed fixed HP HT eq_refl HFH HL Hc)).
Qed.

End ExtendedSVSliceExec.
Print Assumptions ExtendedSVSliceExec.slchain_out.
Print Assumptions ExtendedSVSliceExec.sx_sound.
