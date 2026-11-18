(** Bit-level stability certificate for combinational settling (generic).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    Part 1: agreement of two states on a per-root bit mask, expression reads. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV.
Import ListNotations ExtendedSV.
Local Open Scope Z_scope.

Module ExtendedSVBitStability.

(** masks: list Z indexed by root, default -1 (all bits) *)
Definition kg (K : list Z) (r : nat) : Z := nth r K (-1).

Fixpoint kset (K : list Z) (r : nat) (f : Z -> Z) : list Z :=
  match K, r with
  | [], O => [f (-1)]
  | [], S r' => (-1) :: kset [] r' f
  | k :: K', O => f k :: K'
  | k :: K', S r' => k :: kset K' r' f
  end.

Lemma nth_nil_m1 : forall r, nth r (@nil Z) (-1) = -1.
Proof. destruct r; reflexivity. Qed.

Lemma kg_kset : forall K r f r',
  kg (kset K r f) r' = if Nat.eqb r r' then f (kg K r) else kg K r'.
Proof.
  unfold kg. induction K as [|k K IH]; intros r f r'.
  - revert r'. induction r as [|r IHr]; intros r'.
    + destruct r'; simpl; [reflexivity | destruct r'; reflexivity].
    + destruct r'; simpl; [reflexivity | ].
      rewrite (IHr r'). rewrite ?nth_nil_m1. destruct (Nat.eqb r r'); reflexivity.
  - destruct r, r'; simpl; try reflexivity; apply IH.
Qed.

(** bit-wise agreement *)
Definition Agree (K : list Z) (a b : State) : Prop :=
  forall r i, 0 <= i -> Z.testbit (kg K r) i = true ->
    Z.testbit (read_signal a r) i = Z.testbit (read_signal b r) i.

Definition Ksub (K2 K1 : list Z) : Prop :=
  forall r i, 0 <= i -> Z.testbit (kg K2 r) i = true -> Z.testbit (kg K1 r) i = true.

Lemma agree_sub : forall K1 K2 a b, Ksub K2 K1 -> Agree K1 a b -> Agree K2 a b.
Proof. intros K1 K2 a b Hs Ha r i Hi Hb. apply Ha; auto. Qed.

Lemma agree_refl : forall K a, Agree K a a.
Proof. intros K a r i _ _; reflexivity. Qed.

Lemma agree_sym : forall K a b, Agree K a b -> Agree K b a.
Proof. intros K a b H r i Hi Hb. symmetry. apply H; auto. Qed.

(** mask m is contained in k *)
Definition bitsub (m k : Z) : bool := Z.eqb (Z.land m k) m.

Lemma bitsub_spec : forall m k, bitsub m k = true -> forall i, 0 <= i -> Z.testbit m i = true -> Z.testbit k i = true.
Proof.
  intros m k H i Hi Hm. unfold bitsub in H. apply Z.eqb_eq in H.
  rewrite <- H in Hm. rewrite Z.land_spec in Hm. apply andb_true_iff in Hm. tauto.
Qed.

(** ---- small bit lemmas ---- *)
Lemma mask_ones : forall w, mask w = Z.ones (Z.of_nat w).
Proof. intros w. unfold mask. rewrite Z.ones_equiv. lia. Qed.

Lemma testbit_mask : forall w i, 0 <= i -> Z.testbit (mask w) i = (i <? Z.of_nat w).
Proof. intros w i Hi. rewrite mask_ones. apply Z.testbit_ones_nonneg; lia. Qed.

Lemma mask_nonneg : forall w, 0 <= mask w.
Proof. intros w. unfold mask. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat w)). lia. Qed.

Lemma norm_nonneg : forall w v, 0 <= norm w v.
Proof. intros w v. unfold norm. apply Z.land_nonneg. right. apply mask_nonneg. Qed.

Lemma testbit_norm : forall w v i, 0 <= i ->
  Z.testbit (norm w v) i = andb (i <? Z.of_nat w) (Z.testbit v i).
Proof. intros w v i Hi. unfold norm. rewrite Z.land_spec, testbit_mask by auto. apply andb_comm. Qed.

Lemma norm_ext : forall w v v', (forall i, 0 <= i -> i < Z.of_nat w -> Z.testbit v i = Z.testbit v' i) ->
  norm w v = norm w v'.
Proof.
  intros w v v' H. apply Z.bits_inj'. intros i Hi. rewrite !testbit_norm by auto.
  destruct (Z.ltb_spec i (Z.of_nat w)) as [Hl|Hl]; simpl; [rewrite (H i); auto | reflexivity].
Qed.

(** expression reads *)
Definition const_val (e : Expr) : option Z :=
  match e with EConst w v => Some (norm w v) | _ => None end.

Definition sel_shape (b l : Expr) : option (nat * nat * nat * Z) :=
  match b, l with
  | EVar wb x, EConst kw kv => Some (wb, x, kw, kv)
  | _, _ => None
  end.

Fixpoint reads (e : Expr) : list (nat * Z) :=
  match e with
  | EConst _ _ => []
  | EVar w x => [(x, mask w)]
  | ESel w b l =>
      match sel_shape b l with
      | Some (wb, x, kw, kv) => [(x, Z.land (Z.shiftl (mask w) (norm kw kv)) (mask wb))]
      | None => reads b ++ reads l
      end
  | EConcat _ h l => reads h ++ reads l
  | EReplicate _ _ b => reads b
  | EExtend _ _ b => reads b
  | EUnary _ _ b => reads b
  | EBinary _ _ l r => reads l ++ reads r
  | ECond _ g y n => reads g ++ reads y ++ reads n
  end.

Definition RK (K : list Z) (l : list (nat * Z)) : bool :=
  forallb (fun p => bitsub (snd p) (kg K (fst p))) l.
Definition eknown (K : list Z) (e : Expr) : bool := RK K (reads e).

Lemma RK_app : forall K l1 l2, RK K (l1 ++ l2) = true -> RK K l1 = true /\ RK K l2 = true.
Proof. intros. unfold RK in *. rewrite forallb_app in H. apply andb_true_iff in H. exact H. Qed.

Lemma eval_agree : forall K a b, Agree K a b -> forall e, eknown K e = true -> eval_expr a e = eval_expr b e.
Proof.
  intros K a b HA. induction e; unfold eknown; intros Hk; cbn [reads] in Hk; try (simpl; reflexivity).
  - (* EVar *)
    simpl. apply norm_ext. intros i Hi Hl. apply HA; auto.
    unfold RK in Hk. simpl in Hk. rewrite andb_true_r in Hk.
    apply (bitsub_spec _ _ Hk); auto. rewrite testbit_mask by auto. apply Z.ltb_lt; auto.
  - (* ESel *)
    destruct (sel_shape e1 e2) as [[[[wb x] kw] kv]|] eqn:Hs.
    + destruct e1, e2; simpl in Hs; try discriminate. inversion Hs; subst. simpl.
      assert (Hk0 : 0 <= norm kw kv) by apply norm_nonneg.
      apply norm_ext. intros i Hi Hl. rewrite !Z.shiftr_spec by lia.
      rewrite !testbit_norm by lia.
      destruct (Z.ltb_spec (i + norm kw kv) (Z.of_nat wb)) as [Hw|Hw]; simpl; [ | reflexivity].
      apply HA; [lia | ].
      unfold RK in Hk. simpl in Hk. rewrite andb_true_r in Hk.
      apply (bitsub_spec _ _ Hk); [lia | ].
      rewrite Z.land_spec, Z.shiftl_spec by lia. rewrite testbit_mask by lia.
      replace (i + norm kw kv - norm kw kv) with i by lia.
      rewrite testbit_mask by lia. 
      assert (i <? Z.of_nat width = true) by (apply Z.ltb_lt; lia).
      assert (i + norm kw kv <? Z.of_nat wb = true) by (apply Z.ltb_lt; lia).
      rewrite H, H0. reflexivity.
    + apply RK_app in Hk as [H1 H2].
      simpl. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - apply RK_app in Hk as [H1 H2]. simpl. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - simpl. rewrite (IHe Hk). reflexivity.
  - simpl. rewrite (IHe Hk). reflexivity.
  - simpl. rewrite (IHe Hk). reflexivity.
  - apply RK_app in Hk as [H1 H2]. simpl. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - apply RK_app in Hk as [H1 H23]. apply RK_app in H23 as [H2 H3]. simpl.
    rewrite (IHe1 H1), (IHe2 H2), (IHe3 H3). reflexivity.
Qed.

(** ---- state read/write ---- *)
Lemma read_write : forall s x v y,
  read_signal (write_signal s x v) y = if Nat.eqb x y then v else read_signal s y.
Proof.
  induction s as [|h s IH]; intros x v y.
  - revert y. induction x as [|x IHx]; intros y;
      [destruct y; reflexivity | destruct y as [|y]; [reflexivity | simpl; rewrite IHx; destruct (Nat.eqb x y); reflexivity]].
  - destruct x, y; simpl; try reflexivity. apply IH.
Qed.

Lemma length_write_signal : forall s x v, (x < length s)%nat -> length (write_signal s x v) = length s.
Proof.
  induction s as [|h s IH]; intros x v Hx; [simpl in Hx; lia|].
  destruct x; simpl; [reflexivity | f_equal; apply IH; simpl in Hx; lia].
Qed.

Lemma write_slice_bit : forall old lsb w v i, 0 <= lsb -> 0 <= i ->
  Z.testbit (write_slice old lsb (Z.of_nat w) v) i =
  if (lsb <=? i) && (i <? lsb + Z.of_nat w) then Z.testbit v (i - lsb) else Z.testbit old i.
Proof.
  intros old lsb w v i Hl Hi. unfold write_slice. cbv zeta.
  replace (2 ^ Z.of_nat w - 1) with (Z.ones (Z.of_nat w)) by (rewrite Z.ones_equiv; lia).
  rewrite Z.lor_spec, Z.land_spec, Z.land_spec, Z.lnot_spec by lia.
  rewrite !Z.shiftl_spec by lia.
  destruct (Z.ltb_spec (i - lsb) 0) as [Hn|Hn].
  - rewrite (Z.testbit_neg_r (Z.ones (Z.of_nat w)) (i - lsb)) by lia.
    rewrite (Z.testbit_neg_r v (i - lsb)) by lia.
    destruct (Z.leb_spec lsb i); [lia | simpl]. destruct (Z.testbit old i); reflexivity.
  - rewrite Z.testbit_ones_nonneg by lia.
    destruct (Z.leb_spec lsb i); [ | lia].
    destruct (Z.ltb_spec (i - lsb) (Z.of_nat w)); destruct (Z.ltb_spec i (lsb + Z.of_nat w)); try lia;
      simpl; destruct (Z.testbit old i), (Z.testbit v (i - lsb)); reflexivity.
Qed.

(** ---- lvalues ---- *)
Fixpoint lv_offs (lv : LValue) : list Expr :=
  match lv with LVar _ _ => [] | LSel _ b l => lv_offs b ++ [l] end.

Fixpoint lv_static (lv : LValue) : option Z :=
  match lv with
  | LVar _ _ => Some 0
  | LSel _ b l =>
      match lv_static b, const_val l with Some o, Some c => Some (o + c) | _, _ => None end
  end.

(** upper bound of an expression value *)
Fixpoint ub (e : Expr) : Z :=
  match e with
  | EConst w v => norm w v
  | EVar w _ => mask w
  | ESel w b _ => Z.min (mask w) (ub b)
  | EExtend w false b => Z.min (mask w) (ub b)
  | EBinary w BShiftL l (EConst kw kv) => Z.min (mask w) (Z.shiftl (ub l) (norm kw kv))
  | _ => mask (expr_width e)
  end.

Lemma norm_mod : forall w v, norm w v = v mod 2 ^ Z.of_nat w.
Proof. intros. unfold norm. rewrite mask_ones. apply Z.land_ones. lia. Qed.

Lemma norm_le_mask : forall w v, norm w v <= mask w.
Proof.
  intros. rewrite norm_mod. unfold mask.
  assert (0 < 2 ^ Z.of_nat w) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound v (2 ^ Z.of_nat w) H). lia.
Qed.

Lemma norm_le_self : forall w v, 0 <= v -> norm w v <= v.
Proof.
  intros. rewrite norm_mod. apply Z.mod_le; auto. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma shiftr_le : forall a n, 0 <= a -> 0 <= n -> Z.shiftr a n <= a.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by auto. apply Z.div_le_upper_bound.
  - apply Z.pow_pos_nonneg; lia.
  - pose proof (Z.pow_pos_nonneg 2 n). nia.
Qed.

Lemma eval_bounds : forall s e, 0 <= eval_expr s e <= ub e.
Proof.
  intros s. induction e; simpl; try (split; [apply norm_nonneg | apply norm_le_mask]).
  - pose proof (norm_nonneg width value). lia.
  - split; [apply norm_nonneg | ]. apply Z.min_glb; [apply norm_le_mask | ].
    destruct IHe1 as [H1 H2]. destruct IHe2 as [H3 H4].
    eapply Z.le_trans; [apply norm_le_self; apply Z.shiftr_nonneg; lia | ].
    eapply Z.le_trans; [apply shiftr_le; lia | lia].
  - destruct signed.
    + split; [apply norm_nonneg | apply norm_le_mask].
    + split; [apply norm_nonneg | ]. apply Z.min_glb; [apply norm_le_mask | ].
      destruct IHe as [H1 H2]. eapply Z.le_trans; [apply norm_le_self; lia | lia].
  - destruct op; try (split; [apply norm_nonneg | apply norm_le_mask]).
    destruct e2; try (split; [apply norm_nonneg | apply norm_le_mask]).
    split; [apply norm_nonneg | ]. apply Z.min_glb; [apply norm_le_mask | ].
    destruct IHe1 as [H1 H2].
    assert (Hk : 0 <= norm width0 value) by apply norm_nonneg.
    assert (Hp : 0 < 2 ^ norm width0 value) by (apply Z.pow_pos_nonneg; lia).
    rewrite !Z.shiftl_mul_pow2 by lia.
    assert (Hm : 0 <= eval_expr s e1 * 2 ^ norm width0 value) by (apply Z.mul_nonneg_nonneg; lia).
    eapply Z.le_trans; [apply norm_le_self; exact Hm | ].
    apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Fixpoint lv_maxoff (lv : LValue) : Z :=
  match lv with LVar _ _ => 0 | LSel _ b l => lv_maxoff b + ub l end.

Definition lv_mask (lv : LValue) : Z :=
  match lv_static lv with
  | Some c => Z.shiftl (mask (lvalue_width lv)) c
  | None => 2 ^ (lv_maxoff lv + Z.of_nat (lvalue_width lv)) - 1
  end.

Lemma const_val_eval : forall s e c, const_val e = Some c -> eval_expr s e = c.
Proof. intros s e c H. destruct e; simpl in H; inversion H; reflexivity. Qed.

Lemma resolve_spec : forall s lv,
  lvalue_root lv = fst (fst (resolve_lvalue s lv)) /\
  lvalue_width lv = snd (resolve_lvalue s lv) /\
  0 <= snd (fst (resolve_lvalue s lv)) <= lv_maxoff lv /\
  (forall c, lv_static lv = Some c -> snd (fst (resolve_lvalue s lv)) = c).
Proof.
  intros s. induction lv as [w x | w b IH l]; simpl.
  - repeat split; auto; try lia. intros c H. inversion H. reflexivity.
  - destruct (resolve_lvalue s b) as [[id bo] bw] eqn:E. simpl in *.
    destruct IH as [H1 [H2 [H3 H4]]]. destruct (eval_bounds s l) as [B1 B2].
    repeat split; auto; try lia.
    intros c H. destruct (lv_static b) as [o|]; [ | discriminate].
    destruct (const_val l) as [cv|] eqn:Ec; [ | discriminate]. inversion H; subst.
    rewrite (H4 o eq_refl). rewrite (const_val_eval s l cv Ec). reflexivity.
Qed.

Lemma resolve_offs_same : forall a b lv,
  (forall l, In l (lv_offs lv) -> eval_expr a l = eval_expr b l) ->
  resolve_lvalue a lv = resolve_lvalue b lv.
Proof.
  intros a b lv. induction lv as [w x | w bb IH l]; simpl; intros H; [reflexivity | ].
  rewrite IH by (intros l' Hl'; apply H; apply in_or_app; left; exact Hl').
  rewrite (H l) by (apply in_or_app; right; left; reflexivity). reflexivity.
Qed.

Lemma region_in_mask : forall s lv i, 0 <= i ->
  snd (fst (resolve_lvalue s lv)) <= i ->
  i < snd (fst (resolve_lvalue s lv)) + Z.of_nat (lvalue_width lv) ->
  Z.testbit (lv_mask lv) i = true.
Proof.
  intros s lv i Hi H1 H2. destruct (resolve_spec s lv) as [_ [_ [[Ho1 Ho2] Hc]]].
  unfold lv_mask. destruct (lv_static lv) as [c|] eqn:Es.
  - rewrite (Hc c eq_refl) in *. rewrite Z.shiftl_spec by lia.
    rewrite testbit_mask by lia. apply Z.ltb_lt. lia.
  - replace (2 ^ (lv_maxoff lv + Z.of_nat (lvalue_width lv)) - 1) with (Z.ones (lv_maxoff lv + Z.of_nat (lvalue_width lv)))
      by (rewrite Z.ones_equiv; lia).
    rewrite Z.testbit_ones_nonneg by lia. apply Z.ltb_lt. lia.
Qed.

Lemma apply_update_bit : forall s lv v r i id o w, 0 <= i ->
  resolve_lvalue s lv = (id, o, w) ->
  Z.testbit (read_signal (apply_update s (resolve_update s lv v)) r) i =
  if Nat.eqb id r && ((o <=? i) && (i <? o + Z.of_nat w)) then Z.testbit (norm w v) (i - o)
  else Z.testbit (read_signal s r) i.
Proof.
  intros s lv v r i id o w Hi H.
  destruct (resolve_spec s lv) as [_ [_ [[Ho _] _]]]. rewrite H in Ho. simpl in Ho.
  unfold resolve_update, apply_update. rewrite H. simpl.
  rewrite read_write. destruct (Nat.eqb id r) eqn:E; simpl; [ | reflexivity].
  apply Nat.eqb_eq in E. subst r. rewrite write_slice_bit by lia. reflexivity.
Qed.

(** blocking-only executor *)
Fixpoint ex (f : nat) (st : Stmt) (s : State) : State :=
  match f with
  | O => s
  | S f' =>
    match st with
    | SSkip => s
    | SAssign _ rhs lhs => apply_update s (resolve_update s lhs (eval_expr s rhs))
    | SSeq l => fold_left (fun s' st' => ex f' st' s') l s
    | SIf g y n => ex f' (if Z.eqb (eval_expr s g) 0 then n else y) s
    | SCase scr arms => ex f' (select_case_stmt s (eval_expr s scr) arms SSkip) s
    end
  end.

Fixpoint nbafree (st : Stmt) : bool :=
  match st with
  | SSkip => true
  | SAssign nb _ _ => negb nb
  | SSeq l => forallb nbafree l
  | SIf _ y n => andb (nbafree y) (nbafree n)
  | SCase _ arms => forallb (fun a => nbafree (snd a)) arms
  end.

Fixpoint depth (st : Stmt) : nat :=
  match st with
  | SSkip => 1%nat
  | SAssign _ _ _ => 1%nat
  | SSeq l => S (fold_right Nat.max 0%nat (map depth l))
  | SIf _ y n => S (Nat.max (depth y) (depth n))
  | SCase _ arms => S (fold_right Nat.max 0%nat (map (fun a => depth (snd a)) arms))
  end.

Lemma ex_exec : forall f st es, nbafree st = true ->
  blocking_state (exec_stmt f st es) = ex f st (blocking_state es) /\
  pending_nba (exec_stmt f st es) = pending_nba es.
Proof.
  induction f as [|f IH]; intros st es Hn; [simpl; auto | ].
  destruct st as [|nb rhs lhs|l|g y n|scr arms]; simpl in *.
  - auto.
  - destruct nb; simpl in Hn; [discriminate | ]. simpl. auto.
  - assert (Hg : forall l0 es0, forallb nbafree l0 = true ->
      blocking_state (fold_left (fun es' st' => exec_stmt f st' es') l0 es0) =
        fold_left (fun s' st' => ex f st' s') l0 (blocking_state es0) /\
      pending_nba (fold_left (fun es' st' => exec_stmt f st' es') l0 es0) = pending_nba es0).
    { induction l0 as [|st0 l0 IHl]; intros es0 H0; simpl; [auto | ].
      apply andb_true_iff in H0 as [H1 H2].
      destruct (IH st0 es0 H1) as [E1 E2].
      destruct (IHl (exec_stmt f st0 es0) H2) as [E3 E4]. rewrite E3, E4, E1, E2. auto. }
    apply Hg; auto.
  - apply andb_true_iff in Hn as [H1 H2]. destruct (Z.eqb (eval_expr (blocking_state es) g) 0); apply IH; auto.
  - assert (Hs : forall s0 v0 arms0 d, forallb (fun a => nbafree (snd a)) arms0 = true -> nbafree d = true ->
        nbafree (select_case_stmt s0 v0 arms0 d) = true).
    { induction arms0 as [|[ko b] arms0 IHa]; intros d H0 Hd; simpl in *; [auto | ].
      apply andb_true_iff in H0 as [H1 H2]. destruct ko as [k|].
      - destruct (Z.eqb v0 (eval_expr s0 k)); auto.
      - apply IHa; auto. }
    apply IH. apply Hs; auto.
Qed.

(** ---- case selection ---- *)
Lemma select_in : forall s v arms d,
  select_case_stmt s v arms d = d \/ In (select_case_stmt s v arms d) (map snd arms).
Proof.
  intros s v. induction arms as [|[ko b] arms IH]; intros d; simpl; [left; reflexivity | ].
  destruct ko as [k|].
  - destruct (Z.eqb v (eval_expr s k)); [right; left; reflexivity | ].
    destruct (IH d) as [H|H]; [left; exact H | right; right; exact H].
  - destruct (IH b) as [H|H]; right; [left; symmetry; exact H | right; exact H].
Qed.

Lemma select_in_none : forall s v arms d, In None (map fst arms) ->
  In (select_case_stmt s v arms d) (map snd arms).
Proof.
  intros s v. induction arms as [|[ko b] arms IH]; intros d H; simpl in *; [contradiction | ].
  destruct ko as [k|].
  - destruct H as [H|H]; [discriminate | ].
    destruct (Z.eqb v (eval_expr s k)); [left; reflexivity | right; apply IH; exact H].
  - destruct (select_in s v arms b) as [H1|H1]; [left; symmetry; exact H1 | right; exact H1].
Qed.

Lemma select_in_match : forall s v arms d k b, In (Some k, b) arms -> v = eval_expr s k ->
  In (select_case_stmt s v arms d) (map snd arms).
Proof.
  intros s v. induction arms as [|[ko b0] arms IH]; intros d k b H Hv; simpl in *; [contradiction | ].
  destruct H as [H|H].
  - inversion H; subst. rewrite Z.eqb_refl. left. reflexivity.
  - destruct ko as [k0|].
    + destruct (Z.eqb v (eval_expr s k0)); [left; reflexivity | right; eapply IH; eauto].
    + destruct (select_in s v arms b0) as [H1|H1]; [left; symmetry; exact H1 | right; exact H1].
Qed.

Lemma select_same : forall a b va vb arms d,
  va = vb -> (forall k bb, In (Some k, bb) arms -> eval_expr a k = eval_expr b k) ->
  select_case_stmt a va arms d = select_case_stmt b vb arms d.
Proof.
  intros a b va vb arms d Hv H. subst vb. revert d H.
  induction arms as [|[ko b0] arms IH]; intros d H; simpl in *; [reflexivity | ].
  destruct ko as [k|].
  - rewrite (H k b0) by (left; reflexivity). destruct (Z.eqb va (eval_expr b k)); [reflexivity | ].
    apply IH. intros k' bb Hk'. apply (H k' bb). right. exact Hk'.
  - apply IH. intros k' bb Hk'. apply (H k' bb). right. exact Hk'.
Qed.

(** ---- footprints, frame and kill ---- *)
Definition NotFp (l : list (nat * Z)) (r : nat) (i : Z) : Prop :=
  forall p, In p l -> fst p = r -> Z.testbit (snd p) i = false.

Fixpoint fpl (st : Stmt) : list (nat * Z) :=
  match st with
  | SSkip => []
  | SAssign _ _ lv => [(lvalue_root lv, lv_mask lv)]
  | SSeq l => flat_map fpl l
  | SIf _ y n => fpl y ++ fpl n
  | SCase _ arms => flat_map (fun a => fpl (snd a)) arms
  end.

Lemma NotFp_app : forall l1 l2 r i, NotFp (l1 ++ l2) r i <-> NotFp l1 r i /\ NotFp l2 r i.
Proof.
  unfold NotFp; split; intros H.
  - split; intros p Hp; apply H; apply in_or_app; [left|right]; auto.
  - intros p Hp. apply in_app_or in Hp. destruct H as [H1 H2]. destruct Hp; [apply H1 | apply H2]; auto.
Qed.

Lemma NotFp_flat : forall {A} (g : A -> list (nat * Z)) l r i x,
  NotFp (flat_map g l) r i -> In x l -> NotFp (g x) r i.
Proof. unfold NotFp; intros A g l r i x H Hx p Hp. apply H; auto. apply in_flat_map. exists x; auto. Qed.

Lemma apply_update_frame : forall s lv v r i, 0 <= i ->
  NotFp [(lvalue_root lv, lv_mask lv)] r i ->
  Z.testbit (read_signal (apply_update s (resolve_update s lv v)) r) i = Z.testbit (read_signal s r) i.
Proof.
  intros s lv v r i Hi HN.
  destruct (resolve_lvalue s lv) as [[id o] w] eqn:E.
  rewrite (apply_update_bit s lv v r i id o w Hi E).
  destruct (Nat.eqb id r && ((o <=? i) && (i <? o + Z.of_nat w))) eqn:C; [ | reflexivity].
  exfalso. apply andb_true_iff in C as [C1 C2]. apply andb_true_iff in C2 as [C2 C3].
  apply Nat.eqb_eq in C1. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
  destruct (resolve_spec s lv) as [Hr [Hw _]]. rewrite E in Hr, Hw. simpl in Hr, Hw.
  assert (Hm : Z.testbit (lv_mask lv) i = true).
  { apply (region_in_mask s lv i Hi); rewrite E; simpl; [lia | rewrite Hw; lia]. }
  assert (H2 := HN (lvalue_root lv, lv_mask lv) (or_introl eq_refl)).
  simpl in H2. rewrite Hm in H2. subst r. rewrite <- Hr in H2. specialize (H2 eq_refl). discriminate.
Qed.

Lemma ex_frame : forall f st s r i, 0 <= i -> NotFp (fpl st) r i ->
  Z.testbit (read_signal (ex f st s) r) i = Z.testbit (read_signal s r) i.
Proof.
  induction f as [|f IH]; intros st s r i Hi HN; [reflexivity | ].
  destruct st as [|nb rhs lhs|l|g y n|scr arms]; simpl in *.
  - reflexivity.
  - apply apply_update_frame; auto.
  - assert (Hg : forall l0 s0, (forall st0, In st0 l0 -> NotFp (fpl st0) r i) ->
      Z.testbit (read_signal (fold_left (fun s' st' => ex f st' s') l0 s0) r) i = Z.testbit (read_signal s0 r) i).
    { induction l0 as [|st0 l0 IHl]; intros s0 H0; simpl; [reflexivity | ].
      rewrite IHl by (intros; apply H0; right; auto).
      apply IH; auto. apply H0. left. reflexivity. }
    apply (Hg l s). intros st0 H0. eapply NotFp_flat; eauto.
  - apply NotFp_app in HN as [H1 H2]. destruct (Z.eqb (eval_expr s g) 0); apply IH; auto.
  - destruct (select_in s (eval_expr s scr) arms SSkip) as [H|H].
    + rewrite H. destruct f; reflexivity.
    + apply IH; auto. apply in_map_iff in H as [[ko b] [Hb Hin]]. simpl in Hb. subst b.
      exact (NotFp_flat (fun a : option Expr * Stmt => fpl (snd a)) arms r i (ko, select_case_stmt s (eval_expr s scr) arms SSkip) HN Hin).
Qed.

Definition killl (K : list Z) (l : list (nat * Z)) : list Z :=
  fold_left (fun K p => kset K (fst p) (fun m => Z.land m (Z.lnot (snd p)))) l K.

Lemma killl_spec : forall l K r i, 0 <= i ->
  Z.testbit (kg (killl K l) r) i = true -> Z.testbit (kg K r) i = true /\ NotFp l r i.
Proof.
  induction l as [|p l IH]; intros K r i Hi H; unfold killl in H; simpl in H.
  - split; [exact H | intros q Hq; contradiction].
  - fold (killl (kset K (fst p) (fun m => Z.land m (Z.lnot (snd p)))) l) in H.
    destruct (IH _ r i Hi H) as [H1 H2]. rewrite kg_kset in H1.
    destruct (Nat.eqb (fst p) r) eqn:E.
    + rewrite Z.land_spec, Z.lnot_spec in H1 by lia. apply andb_true_iff in H1 as [H1 H3].
      apply negb_true_iff in H3. apply Nat.eqb_eq in E. rewrite E in H1. split; [exact H1 | ].
      intros q Hq Hqr. destruct Hq as [Hq|Hq]; [subst q; exact H3 | apply H2; auto].
    + split; [exact H1 | ]. intros q Hq Hqr. destruct Hq as [Hq|Hq];
        [subst q; apply Nat.eqb_neq in E; contradiction | apply H2; auto].
Qed.

Lemma kill_frame : forall K a b f st, Agree K a b -> Agree (killl K (fpl st)) (ex f st a) (ex f st b).
Proof.
  intros K a b f st HA r i Hi Hk. destruct (killl_spec _ _ _ _ Hi Hk) as [H1 H2].
  rewrite (ex_frame f st a r i Hi H2), (ex_frame f st b r i Hi H2). apply HA; auto.
Qed.

(** ---- meet ---- *)
Fixpoint meet (K1 K2 : list Z) : list Z :=
  match K1, K2 with
  | [], l => l
  | l, [] => l
  | a :: K1', b :: K2' => Z.land a b :: meet K1' K2'
  end.

Lemma land_m1_l : forall b, Z.land (-1) b = b.
Proof. intros. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_m1 by auto. reflexivity. Qed.
Lemma land_m1_r : forall b, Z.land b (-1) = b.
Proof. intros. rewrite Z.land_comm. apply land_m1_l. Qed.

Lemma kg_meet : forall K1 K2 r, kg (meet K1 K2) r = Z.land (kg K1 r) (kg K2 r).
Proof.
  unfold kg. induction K1 as [|a K1 IH]; intros K2 r.
  - rewrite nth_nil_m1, land_m1_l. reflexivity.
  - destruct K2 as [|b K2]; simpl.
    + destruct r; simpl; rewrite land_m1_r; reflexivity.
    + destruct r; simpl; [reflexivity | apply IH].
Qed.

Lemma meet_sub_l : forall K1 K2, Ksub (meet K1 K2) K1.
Proof.
  intros K1 K2 r i Hi H. rewrite kg_meet in H. rewrite Z.land_spec in H.
  apply andb_true_iff in H. tauto.
Qed.
Lemma meet_sub_r : forall K1 K2, Ksub (meet K1 K2) K2.
Proof.
  intros K1 K2 r i Hi H. rewrite kg_meet in H. rewrite Z.land_spec in H.
  apply andb_true_iff in H. tauto.
Qed.
Lemma Ksub_trans : forall A B C, Ksub A B -> Ksub B C -> Ksub A C.
Proof. intros A B C H1 H2 r i Hi H. apply H2; auto. Qed.

Lemma fold_meet_init : forall L init, Ksub (fold_left meet L init) init.
Proof.
  induction L as [|z L0 IH0]; intros init0.
  - intros r i Hi Hh. exact Hh.
  - simpl. eapply Ksub_trans; [apply IH0 | apply meet_sub_l].
Qed.

Lemma fold_meet_sub : forall L init x, In x L -> Ksub (fold_left meet L init) x.
Proof.
  induction L as [|y L IH]; intros init x H; simpl in H; [contradiction | ]. simpl.
  destruct H as [H|H].
  - subst y. assert (Hs : forall L0 init0, Ksub (fold_left meet L0 init0) init0).
    { induction L0 as [|z L0 IH0]; intros init0.
      - intros r i Hi Hh. exact Hh.
      - simpl. eapply Ksub_trans; [apply IH0 | apply meet_sub_l]. }
    eapply Ksub_trans; [apply Hs | apply meet_sub_r].
  - apply IH; auto.
Qed.

(** ---- the known-bit transfer ---- *)
Definition ok_assign (K : list Z) (rhs : Expr) (lv : LValue) : bool :=
  andb (eknown K rhs) (forallb (eknown K) (lv_offs lv)).

Definition key_known (K : list Z) (a : option Expr * Stmt) : bool :=
  match fst a with Some k => eknown K k | None => true end.

Definition arm_hits (v : Z) (a : option Expr * Stmt) : bool :=
  match fst a with Some k => match const_val k with Some c => Z.eqb c v | None => false end | None => false end.

Definition exhaustive (scr : Expr) (arms : list (option Expr * Stmt)) : bool :=
  andb (Nat.leb (expr_width scr) 12)
    (forallb (fun v => existsb (arm_hits v) arms) (map Z.of_nat (seq 0 (Nat.pow 2 (expr_width scr))))).

Definition has_none (arms : list (option Expr * Stmt)) : bool :=
  existsb (fun a => match fst a with None => true | Some _ => false end) arms.

Definition case_ok (K : list Z) (scr : Expr) (arms : list (option Expr * Stmt)) : bool :=
  andb (eknown K scr) (forallb (key_known K) arms).

Definition case_total (scr : Expr) (arms : list (option Expr * Stmt)) : bool :=
  orb (has_none arms) (exhaustive scr arms).

Fixpoint slx (K : list Z) (st : Stmt) : list Z :=
  match st with
  | SSkip => K
  | SAssign _ rhs lv =>
      if ok_assign K rhs lv
      then match lv_static lv with
           | Some _ => kset K (lvalue_root lv) (fun m => Z.lor m (lv_mask lv))
           | None => K
           end
      else kset K (lvalue_root lv) (fun m => Z.land m (Z.lnot (lv_mask lv)))
  | SSeq l => fold_left (fun K' st' => slx K' st') l K
  | SIf g y n =>
      if eknown K g then meet (slx K y) (slx K n) else killl K (fpl st)
  | SCase scr arms =>
      if case_ok K scr arms
      then fold_left meet (map (fun a => slx K (snd a)) arms) (if case_total scr arms then [] else K)
      else killl K (fpl st)
  end.

Lemma mask_static_bit : forall lv c i, 0 <= c -> 0 <= i -> lv_static lv = Some c ->
  Z.testbit (lv_mask lv) i = true -> c <= i /\ i < c + Z.of_nat (lvalue_width lv).
Proof.
  intros lv c i Hc Hi Hs H. unfold lv_mask in H. rewrite Hs in H. rewrite Z.shiftl_spec in H by lia.
  destruct (Z.ltb_spec (i - c) 0) as [Hn|Hn].
  - rewrite Z.testbit_neg_r in H by lia. discriminate.
  - rewrite testbit_mask in H by lia. apply Z.ltb_lt in H. lia.
Qed.

Lemma assign_sound : forall f K a b nb rhs lv, Agree K a b ->
  Agree (slx K (SAssign nb rhs lv)) (ex (S f) (SAssign nb rhs lv) a) (ex (S f) (SAssign nb rhs lv) b).
Proof.
  intros f K a b nb rhs lv HA r i Hi Hk. simpl ex.
  destruct (resolve_lvalue a lv) as [[ida oa] wa] eqn:Ea.
  destruct (resolve_lvalue b lv) as [[idb ob] wb] eqn:Eb.
  rewrite (apply_update_bit a lv _ r i ida oa wa Hi Ea), (apply_update_bit b lv _ r i idb ob wb Hi Eb).
  destruct (resolve_spec a lv) as [Ra [Wa [[Oa1 Oa2] Ca]]]. rewrite Ea in Ra, Wa, Oa1, Oa2, Ca. simpl in Ra, Wa, Oa1, Oa2, Ca.
  destruct (resolve_spec b lv) as [Rb [Wb [[Ob1 Ob2] Cb]]]. rewrite Eb in Rb, Wb, Ob1, Ob2, Cb. simpl in Rb, Wb, Ob1, Ob2, Cb.
  simpl slx in Hk.
  destruct (ok_assign K rhs lv) eqn:Eok.
  - unfold ok_assign in Eok. apply andb_true_iff in Eok as [E1 E2].
    assert (Hv : eval_expr a rhs = eval_expr b rhs) by (apply (eval_agree K a b HA); exact E1).
    assert (Hres : resolve_lvalue a lv = resolve_lvalue b lv).
    { apply resolve_offs_same. intros l Hl. apply (eval_agree K a b HA).
      rewrite forallb_forall in E2. apply E2; exact Hl. }
    rewrite Ea, Eb in Hres. inversion Hres; subst ida oa wa.
    rewrite Hv.
    destruct (Nat.eqb idb r && ((ob <=? i) && (i <? ob + Z.of_nat wb))) eqn:C; [reflexivity | ].
    apply HA; [exact Hi | ].
    destruct (lv_static lv) as [c|] eqn:Es; [ | exact Hk].
    rewrite kg_kset in Hk. destruct (Nat.eqb (lvalue_root lv) r) eqn:Er; [ | exact Hk].
    apply Nat.eqb_eq in Er. subst r.
    rewrite Z.lor_spec in Hk. apply orb_true_iff in Hk. destruct Hk as [Hk|Hk]; [exact Hk | exfalso].
    pose proof (Ca c eq_refl) as Hcc.
    destruct (mask_static_bit lv c i ltac:(lia) Hi Es Hk) as [M1 M2].
    rewrite Wb in M2. 
    assert (Hidr : Nat.eqb idb (lvalue_root lv) = true) by (apply Nat.eqb_eq; symmetry; exact Rb).
    rewrite Hidr in C. simpl in C. 
    apply andb_false_iff in C. destruct C as [C|C]; [rewrite Z.leb_gt in C | rewrite Z.ltb_nlt in C]; lia.
  - rewrite kg_kset in Hk.
    assert (Hnot : forall id o w s0, resolve_lvalue s0 lv = (id, o, w) -> Z.testbit (lv_mask lv) i = false ->
        (Nat.eqb id r && ((o <=? i) && (i <? o + Z.of_nat w))) = false).
    { intros id o w s0 E Hm. destruct (resolve_spec s0 lv) as [R0 [W0 _]]. rewrite E in R0, W0. simpl in R0, W0.
      destruct (Nat.eqb id r && ((o <=? i) && (i <? o + Z.of_nat w))) eqn:C; [ | reflexivity].
      exfalso. apply andb_true_iff in C as [C1 C2]. apply andb_true_iff in C2 as [C2 C3].
      apply Z.leb_le in C2. apply Z.ltb_lt in C3.
      assert (Hm' : Z.testbit (lv_mask lv) i = true).
      { apply (region_in_mask s0 lv i Hi); rewrite E; simpl; [lia | rewrite W0; lia]. }
      rewrite Hm in Hm'. discriminate. }
    destruct (Nat.eqb (lvalue_root lv) r) eqn:Er.
    + apply Nat.eqb_eq in Er. subst r.
      rewrite Z.land_spec, Z.lnot_spec in Hk by lia. apply andb_true_iff in Hk as [Hk1 Hk2].
      apply negb_true_iff in Hk2.
      rewrite (Hnot ida oa wa a Ea Hk2), (Hnot idb ob wb b Eb Hk2). apply HA; auto.
    + assert (Ha : Nat.eqb ida r = false) by (apply Nat.eqb_neq; rewrite <- Ra; apply Nat.eqb_neq; exact Er).
      assert (Hb : Nat.eqb idb r = false) by (apply Nat.eqb_neq; rewrite <- Rb; apply Nat.eqb_neq; exact Er).
      rewrite Ha, Hb. simpl. apply HA; auto.
Qed.

Lemma eval_le_width : forall s e, 0 <= eval_expr s e <= mask (expr_width e).
Proof.
  intros s e. split; [destruct (eval_bounds s e); auto | ].
  destruct e; simpl; apply norm_le_mask.
Qed.

Lemma depth_pos : forall st, (1 <= depth st)%nat.
Proof. destruct st; simpl; lia. Qed.

Lemma depth_seq_in : forall l st, In st l -> (depth st <= fold_right Nat.max 0%nat (map depth l))%nat.
Proof.
  induction l as [|x l IH]; intros st H; simpl in *; [contradiction | ].
  destruct H as [H|H]; [subst; apply Nat.le_max_l | ].
  eapply Nat.le_trans; [apply IH; exact H | apply Nat.le_max_r].
Qed.

Lemma depth_case_in : forall (arms : list (option Expr * Stmt)) st, In st (map snd arms) ->
  (depth st <= fold_right Nat.max 0%nat (map (fun a => depth (snd a)) arms))%nat.
Proof.
  induction arms as [|x arms IH]; intros st H; simpl in *; [contradiction | ].
  destruct H as [H|H]; [subst; apply Nat.le_max_l | ].
  eapply Nat.le_trans; [apply IH; exact H | apply Nat.le_max_r].
Qed.

Lemma exhaustive_hit : forall s scr arms, exhaustive scr arms = true ->
  exists k b, In (Some k, b) arms /\ eval_expr s scr = eval_expr s k.
Proof.
  intros s scr arms H. unfold exhaustive in H. apply andb_true_iff in H as [H1 H2].
  rewrite forallb_forall in H2.
  destruct (eval_le_width s scr) as [B1 B2].
  assert (Hin : In (eval_expr s scr) (map Z.of_nat (seq 0 (Nat.pow 2 (expr_width scr))))).
  { apply in_map_iff. exists (Z.to_nat (eval_expr s scr)). split; [apply Z2Nat.id; auto | ].
    apply in_seq. split; [lia | ]. simpl.
    assert (Hp : Z.of_nat (Nat.pow 2 (expr_width scr)) = 2 ^ Z.of_nat (expr_width scr)) by (rewrite Nat2Z.inj_pow; reflexivity).
    unfold mask in B2. apply Nat2Z.inj_lt. rewrite Z2Nat.id by auto. rewrite Hp. lia. }
  specialize (H2 _ Hin). apply existsb_exists in H2 as [[ko b] [Hab Hh]].
  unfold arm_hits in Hh. simpl in Hh. destruct ko as [k|]; [ | discriminate].
  destruct (const_val k) as [c|] eqn:Ec; [ | discriminate].
  apply Z.eqb_eq in Hh. exists k, b. split; auto.
  rewrite (const_val_eval s k c Ec). auto.
Qed.

Theorem slx_sound : forall f st K a b, (depth st <= f)%nat -> Agree K a b ->
  Agree (slx K st) (ex f st a) (ex f st b).
Proof.
  induction f as [|f IH]; intros st K a b Hd HA.
  - pose proof (depth_pos st). lia.
  - destruct st as [|nb rhs lhs|l|g y n|scr arms].
    + simpl. exact HA.
    + apply assign_sound; auto.
    + simpl in Hd. assert (Hl : forall l0 K0 a0 b0, (forall st0, In st0 l0 -> (depth st0 <= f)%nat) -> Agree K0 a0 b0 ->
        Agree (fold_left (fun K' st' => slx K' st') l0 K0) (fold_left (fun s' st' => ex f st' s') l0 a0)
          (fold_left (fun s' st' => ex f st' s') l0 b0)).
      { induction l0 as [|st0 l0 IHl]; intros K0 a0 b0 H0 HA0; simpl; [exact HA0 | ].
        apply IHl; [intros; apply H0; right; auto | ]. apply IH; [apply H0; left; reflexivity | exact HA0]. }
      simpl. apply Hl; [ | exact HA]. intros st0 H0.
      pose proof (depth_seq_in l st0 H0). lia.
    + simpl in Hd. simpl. destruct (eknown K g) eqn:Eg.
      * assert (Hg : eval_expr a g = eval_expr b g) by (apply (eval_agree K a b HA); exact Eg).
        rewrite Hg.
        assert (Hdy : (depth y <= f)%nat) by lia. assert (Hdn : (depth n <= f)%nat) by lia.
        destruct (Z.eqb (eval_expr b g) 0).
        -- eapply agree_sub; [apply meet_sub_r | apply IH; auto].
        -- eapply agree_sub; [apply meet_sub_l | apply IH; auto].
      * pose proof (kill_frame K a b (S f) (SIf g y n) HA) as Hkf. exact Hkf.
    + simpl in Hd. simpl slx. destruct (case_ok K scr arms) eqn:Ec.
      * unfold case_ok in Ec. apply andb_true_iff in Ec as [Ec1 Ec3].
        assert (Hs : eval_expr a scr = eval_expr b scr) by (apply (eval_agree K a b HA); exact Ec1).
        assert (Hk : forall k bb, In (Some k, bb) arms -> eval_expr a k = eval_expr b k).
        { intros k bb Hin. rewrite forallb_forall in Ec3. specialize (Ec3 _ Hin).
          unfold key_known in Ec3. simpl in Ec3. apply (eval_agree K a b HA); exact Ec3. }
        simpl ex.
        rewrite (select_same a b _ _ arms SSkip Hs Hk).
        set (c := select_case_stmt b (eval_expr b scr) arms SSkip).
        destruct (case_total scr arms) eqn:Et.
        -- assert (Hcin : In c (map snd arms)).
           { unfold case_total in Et. apply orb_true_iff in Et as [E|E].
             - unfold has_none in E. apply existsb_exists in E as [[ko bb] [Hab Hn]]. destruct ko; [discriminate | ].
               apply select_in_none. apply in_map_iff. exists (None, bb). split; auto.
             - destruct (exhaustive_hit b scr arms E) as [k [bb [Hin Hv]]].
               eapply select_in_match; [exact Hin | exact Hv]. }
           assert (Hdc : (depth c <= f)%nat).
           { pose proof (depth_case_in arms c Hcin). lia. }
           eapply agree_sub; [ | apply IH; [exact Hdc | exact HA]].
           apply fold_meet_sub. apply in_map_iff. apply in_map_iff in Hcin as [[ko bb] [Hb Hin]].
           simpl in Hb. subst bb. exists (ko, c). split; [reflexivity | exact Hin].
        -- destruct (select_in b (eval_expr b scr) arms SSkip) as [Hc|Hcin].
           ++ fold c in Hc. rewrite Hc. eapply agree_sub; [apply fold_meet_init | ].
              destruct f; exact HA.
           ++ fold c in Hcin.
              assert (Hdc : (depth c <= f)%nat).
              { pose proof (depth_case_in arms c Hcin). lia. }
              eapply agree_sub; [ | apply IH; [exact Hdc | exact HA]].
              apply fold_meet_sub. apply in_map_iff. apply in_map_iff in Hcin as [[ko bb] [Hb Hin]].
              simpl in Hb. subst bb. exists (ko, c). split; [reflexivity | exact Hin].
      * pose proof (kill_frame K a b (S f) (SCase scr arms) HA) as Hkf. exact Hkf.
Qed.

(** ---- processes ---- *)
Definition latch_shape (st : Stmt) : option (Expr * Expr * nat * nat) :=
  match st with
  | SSeq [st1] =>
    match st1 with
    | SSeq [st2] =>
      match st2 with
      | SIf g y n =>
        match y, n with
        | SAssign true rhs (LVar w x), SSkip => Some (g, rhs, w, x)
        | _, _ => None
        end
      | _ => None
      end
    | _ => None
    end
  | _ => None
  end.

Definition latch_upd (s : State) (rhs : Expr) (w x : nat) : State :=
  apply_update s (resolve_update s (LVar w x) (eval_expr s rhs)).

Lemma run_latch : forall p s proc g rhs w x, (4 <= statement_fuel p)%nat ->
  latch_shape (process_body proc) = Some (g, rhs, w, x) ->
  run_process p s proc = if Z.eqb (eval_expr s g) 0 then s else latch_upd s rhs w x.
Proof.
  intros p s proc g rhs w x Hf Hs. unfold run_process.
  destruct proc as [pk pe pb pl]. simpl in *.
  destruct pb as [|? ? ?|[|st1 [|? ?]]|? ? ?|? ?]; try (unfold latch_shape in Hs; discriminate).
  destruct st1 as [|? ? ?|[|st2 [|? ?]]|? ? ?|? ?]; try (unfold latch_shape in Hs; discriminate).
  destruct st2 as [|? ? ?|?|g1 y1 n1|? ?]; try (unfold latch_shape in Hs; discriminate).
  destruct y1 as [|nb1 rhs1 lhs1|?|? ? ?|? ?]; try (unfold latch_shape in Hs; discriminate).
  destruct nb1; try (unfold latch_shape in Hs; discriminate). destruct lhs1 as [w1 x1|? ? ?]; try (unfold latch_shape in Hs; discriminate).
  destruct n1; try (unfold latch_shape in Hs; discriminate). simpl in Hs; inversion Hs; subst.
  destruct (statement_fuel p) as [|[|[|[|k]]]]; try (exfalso; lia).
  simpl. destruct (Z.eqb (eval_expr s g) 0); reflexivity.
Qed.

Lemma run_nbafree : forall p s proc, nbafree (process_body proc) = true ->
  run_process p s proc = ex (statement_fuel p) (process_body proc) s.
Proof.
  intros p s proc H. unfold run_process.
  destruct (ex_exec (statement_fuel p) (process_body proc)
    {| blocking_state := s; pending_nba := []; emitted_updates := [] |} H) as [E1 E2].
  rewrite E1, E2. reflexivity.
Qed.

Definition procs (p : Program) : list Process := filter is_comb (processes p).
Definition fpp (pr : Process) : list (nat * Z) := fpl (process_body pr).
Definition dummy_proc : Process :=
  {| process_kind := Combinational; process_events := []; process_body := SSkip; process_source_line := 0%nat |}.

Definition trs (K : list Z) (ps : list Process) : list Z :=
  fold_left (fun K' pr => slx K' (process_body pr)) ps K.

Definition tr_latch (K : list Z) (g rhs : Expr) (w x : nat) : list Z :=
  if andb (eknown K g) (eknown K rhs)
  then kset K x (fun m => Z.lor m (mask w))
  else kset K x (fun m => Z.land m (Z.lnot (mask w))).

Definition runs (p : Program) (ps : list Process) (s : State) : State := fold_left (run_process p) ps s.

Definition PGood (p : Program) (x : nat) (pr : Process) : Prop :=
  nbafree (process_body pr) = true /\ (depth (process_body pr) <= statement_fuel p)%nat /\
  forall q, In q (fpp pr) -> fst q <> x.

Lemma runs_agree : forall p ps K a b,
  (forall pr, In pr ps -> nbafree (process_body pr) = true /\ (depth (process_body pr) <= statement_fuel p)%nat) ->
  Agree K a b -> Agree (trs K ps) (runs p ps a) (runs p ps b).
Proof.
  intros p ps. induction ps as [|pr ps IH]; intros K a b H HA; simpl; [exact HA | ].
  unfold trs, runs. simpl. fold (trs (slx K (process_body pr)) ps). fold (runs p ps (run_process p a pr)).
  fold (runs p ps (run_process p b pr)).
  apply IH; [intros; apply H; right; auto | ].
  destruct (H pr (or_introl eq_refl)) as [H1 H2].
  rewrite !run_nbafree by exact H1. apply slx_sound; auto.
Qed.

Lemma runs_root_frame : forall p ps x s,
  (forall pr, In pr ps -> PGood p x pr) -> read_signal (runs p ps s) x = read_signal s x.
Proof.
  intros p ps x. induction ps as [|pr ps IH]; intros s H; [reflexivity | ].
  unfold runs. simpl. fold (runs p ps (run_process p s pr)).
  rewrite IH by (intros; apply H; right; auto).
  destruct (H pr (or_introl eq_refl)) as [H1 [H2 H3]].
  rewrite run_nbafree by exact H1. apply Z.bits_inj'. intros i Hi.
  apply ex_frame; auto. intros q Hq Hqx. exfalso. apply (H3 q Hq Hqx).
Qed.

Lemma run_latch_bit : forall s g rhs w x r i, 0 <= i ->
  (Nat.eqb x r && (i <? Z.of_nat w)) = false ->
  Z.testbit (read_signal (if Z.eqb (eval_expr s g) 0 then s else latch_upd s rhs w x) r) i =
  Z.testbit (read_signal s r) i.
Proof.
  intros s g rhs w x r i Hi H. destruct (Z.eqb (eval_expr s g) 0); [reflexivity | ].
  unfold latch_upd. rewrite (apply_update_bit s (LVar w x) _ r i x 0 w Hi eq_refl).
  destruct (Nat.eqb x r && ((0 <=? i) && (i <? 0 + Z.of_nat w))) eqn:C; [ | reflexivity].
  exfalso. apply andb_true_iff in C as [C1 C2]. apply andb_true_iff in C2 as [C2 C3].
  rewrite C1 in H. simpl in H. rewrite Z.add_0_l in C3. rewrite C3 in H. discriminate.
Qed.

Lemma latch_step : forall p proc g rhs w x K a1 b1, (4 <= statement_fuel p)%nat ->
  latch_shape (process_body proc) = Some (g, rhs, w, x) ->
  Agree K a1 b1 -> read_signal b1 x = read_signal (run_process p a1 proc) x ->
  Agree (tr_latch K g rhs w x) (run_process p a1 proc) (run_process p b1 proc).
Proof.
  intros p proc g rhs w x K a1 b1 Hf Hs HA Hx.
  rewrite (run_latch p a1 proc g rhs w x Hf Hs) in *. rewrite (run_latch p b1 proc g rhs w x Hf Hs).
  intros r i Hi Hk. unfold tr_latch in Hk.
  destruct (eknown K g && eknown K rhs) eqn:Ek.
  - apply andb_true_iff in Ek as [Eg Er].
    assert (Hg : eval_expr a1 g = eval_expr b1 g) by (apply (eval_agree K a1 b1 HA); exact Eg).
    assert (Hr : eval_expr a1 rhs = eval_expr b1 rhs) by (apply (eval_agree K a1 b1 HA); exact Er).
    rewrite kg_kset in Hk.
    destruct (Z.eqb (eval_expr a1 g) 0) eqn:E0.
    + rewrite <- Hg. rewrite E0.
      destruct (Nat.eqb x r) eqn:Exr.
      * apply Nat.eqb_eq in Exr. subst r. rewrite Z.lor_spec in Hk. apply orb_true_iff in Hk as [Hk|Hk].
        -- apply HA; auto.
        -- rewrite Hx. reflexivity.
      * apply HA; auto.
    + rewrite <- Hg. rewrite E0.
      unfold latch_upd. rewrite !(apply_update_bit _ (LVar w x) _ r i x 0 w Hi eq_refl).
      rewrite <- Hr. 
      destruct (Nat.eqb x r && ((0 <=? i) && (i <? 0 + Z.of_nat w))) eqn:C; [reflexivity | ].
      apply HA; auto.
      destruct (Nat.eqb x r) eqn:Exr; [ | exact Hk].
      apply Nat.eqb_eq in Exr. subst r. rewrite Z.lor_spec in Hk. apply orb_true_iff in Hk as [Hk|Hk]; [exact Hk | exfalso].
      rewrite testbit_mask in Hk by auto. apply Z.ltb_lt in Hk.
      assert (Hi0 : (0 <=? i) = true) by (apply Z.leb_le; lia).
      simpl in C. rewrite Hi0 in C. simpl in C. rewrite ?Z.add_0_l in C. rewrite (proj2 (Z.ltb_lt _ _) Hk) in C. discriminate.
  - rewrite kg_kset in Hk.
    destruct (Nat.eqb x r) eqn:Exr.
    + apply Nat.eqb_eq in Exr. subst r. rewrite Z.land_spec, Z.lnot_spec in Hk by auto.
      apply andb_true_iff in Hk as [Hk1 Hk2]. apply negb_true_iff in Hk2. rewrite testbit_mask in Hk2 by auto.
      assert (Hc : (Nat.eqb x x && (i <? Z.of_nat w)) = false) by (rewrite Nat.eqb_refl; simpl; exact Hk2).
      rewrite (run_latch_bit a1 g rhs w x x i Hi Hc), (run_latch_bit b1 g rhs w x x i Hi Hc). apply HA; auto.
    + assert (Hc : (Nat.eqb x r && (i <? Z.of_nat w)) = false) by (rewrite Exr; reflexivity).
      rewrite (run_latch_bit a1 g rhs w x r i Hi Hc), (run_latch_bit b1 g rhs w x r i Hi Hc). apply HA; auto.
Qed.

Lemma latch_shape_inv : forall st g rhs w x, latch_shape st = Some (g, rhs, w, x) ->
  st = SSeq [SSeq [SIf g (SAssign true rhs (LVar w x)) SSkip]].
Proof.
  intros st g rhs w x H.
  destruct st as [|? ? ?|[|st1 [|? ?]]|? ? ?|? ?]; try (unfold latch_shape in H; discriminate).
  destruct st1 as [|? ? ?|[|st2 [|? ?]]|? ? ?|? ?]; try (unfold latch_shape in H; discriminate).
  destruct st2 as [|? ? ?|?|g1 y1 n1|? ?]; try (unfold latch_shape in H; discriminate).
  destruct y1 as [|nb1 rhs1 lhs1|?|? ? ?|? ?]; try (unfold latch_shape in H; discriminate).
  destruct nb1; try (unfold latch_shape in H; discriminate).
  destruct lhs1 as [w1 x1|? ? ?]; try (unfold latch_shape in H; discriminate).
  destruct n1; try (unfold latch_shape in H; discriminate).
  unfold latch_shape in H. inversion H; subst. reflexivity.
Qed.

Lemma latch_fp : forall st g rhs w x, latch_shape st = Some (g, rhs, w, x) ->
  fpl st = [(x, lv_mask (LVar w x))].
Proof. intros st g rhs w x H. apply latch_shape_inv in H. subst st. reflexivity. Qed.

Lemma list_split : forall {A} (l : list A) j d, (j < length l)%nat ->
  l = firstn j l ++ nth j l d :: skipn (S j) l.
Proof.
  induction l as [|a l IH]; intros j d H; simpl in H; [lia | ].
  destruct j; simpl; [reflexivity | ]. f_equal. apply IH. lia.
Qed.

Definition Cert (p : Program) (j : nat) (g rhs : Expr) (w x : nat) : Prop :=
  (j < length (procs p))%nat /\
  latch_shape (process_body (nth j (procs p) dummy_proc)) = Some (g, rhs, w, x) /\
  (4 <= statement_fuel p)%nat /\
  (forall pr, In pr (firstn j (procs p)) \/ In pr (skipn (S j) (procs p)) -> PGood p x pr).

Definition Kround (p : Program) (j : nat) (K : list Z) : list Z :=
  match latch_shape (process_body (nth j (procs p) dummy_proc)) with
  | Some (g, rhs, w, x) =>
      trs (tr_latch (trs K (firstn j (procs p))) g rhs w x) (skipn (S j) (procs p))
  | None => K
  end.

Lemma comb_round_split : forall p j s, (j < length (procs p))%nat ->
  comb_round p s = runs p (skipn (S j) (procs p))
     (run_process p (runs p (firstn j (procs p)) s) (nth j (procs p) dummy_proc)).
Proof.
  intros p j s H. unfold comb_round, runs, procs in *.
  set (l := filter is_comb (processes p)) in *.
  rewrite (list_split l j dummy_proc H) at 1.
  rewrite fold_left_app. reflexivity.
Qed.

Theorem round_sound : forall p j g rhs w x K A B,
  Cert p j g rhs w x -> Agree K A B -> B = comb_round p A ->
  Agree (Kround p j K) B (comb_round p B).
Proof.
  intros p j g rhs w x K A B [Hj [Hs [Hf Hg]]] HA HB. unfold Kround. rewrite Hs.
  set (L := nth j (procs p) dummy_proc) in *.
  set (a1 := runs p (firstn j (procs p)) A).
  set (b1 := runs p (firstn j (procs p)) B).
  assert (Hpre : forall pr, In pr (firstn j (procs p)) -> PGood p x pr) by (intros pr H; apply Hg; left; exact H).
  assert (Hpost : forall pr, In pr (skipn (S j) (procs p)) -> PGood p x pr) by (intros pr H; apply Hg; right; exact H).
  assert (Hag : Agree (trs K (firstn j (procs p))) a1 b1).
  { apply runs_agree; [ | exact HA]. intros pr H. destruct (Hpre pr H) as [H1 [H2 _]]. auto. }
  assert (Hx : read_signal b1 x = read_signal (run_process p a1 L) x).
  { unfold b1. rewrite (runs_root_frame p _ x B Hpre). rewrite HB. rewrite (comb_round_split p j A Hj).
    rewrite (runs_root_frame p _ x _ Hpost). reflexivity. }
  pose proof (latch_step p L g rhs w x _ a1 b1 Hf Hs Hag Hx) as Hl.
  rewrite HB at 1. rewrite (comb_round_split p j A Hj). rewrite (comb_round_split p j B Hj).
  fold a1 b1.
  apply runs_agree; [ | exact Hl]. intros pr H. destruct (Hpost pr H) as [H1 [H2 _]]. auto.
Qed.

(** ---- base case, lengths, iteration ---- *)
Definition PFrameOk (pr : Process) : Prop :=
  nbafree (process_body pr) = true \/
  exists g rhs w x, latch_shape (process_body pr) = Some (g, rhs, w, x).

Lemma run_frame : forall p pr s r i, (4 <= statement_fuel p)%nat -> 0 <= i -> PFrameOk pr ->
  NotFp (fpp pr) r i ->
  Z.testbit (read_signal (run_process p s pr) r) i = Z.testbit (read_signal s r) i.
Proof.
  intros p pr s r i Hf Hi [H|[g [rhs [w [x Hs]]]]] HN.
  - rewrite run_nbafree by exact H. apply ex_frame; auto.
  - rewrite (run_latch p s pr g rhs w x Hf Hs).
    destruct (Z.eqb (eval_expr s g) 0); [reflexivity | ].
    unfold latch_upd. apply apply_update_frame; [exact Hi | ].
    unfold fpp in HN. rewrite (latch_fp _ g rhs w x Hs) in HN. exact HN.
Qed.

Lemma runs_frame : forall p ps s r i, (4 <= statement_fuel p)%nat -> 0 <= i ->
  (forall pr, In pr ps -> PFrameOk pr) -> NotFp (flat_map fpp ps) r i ->
  Z.testbit (read_signal (runs p ps s) r) i = Z.testbit (read_signal s r) i.
Proof.
  intros p ps. induction ps as [|pr ps IH]; intros s r i Hf Hi H HN; [reflexivity | ].
  unfold runs. simpl. fold (runs p ps (run_process p s pr)).
  simpl flat_map in HN. apply NotFp_app in HN as [H1 H2].
  rewrite IH by (auto; intros; apply H; right; auto).
  apply run_frame; auto. apply H. left. reflexivity.
Qed.

Definition K0 (p : Program) : list Z := killl [] (flat_map fpp (procs p)).

Lemma base_agree : forall p s, (4 <= statement_fuel p)%nat ->
  (forall pr, In pr (procs p) -> PFrameOk pr) -> Agree (K0 p) s (comb_round p s).
Proof.
  intros p s Hf H r i Hi Hk. unfold K0 in Hk. destruct (killl_spec _ _ _ _ Hi Hk) as [_ HN].
  unfold comb_round. change (fold_left (run_process p) (filter is_comb (processes p)) s) with (runs p (procs p) s).
  symmetry. apply runs_frame; auto.
Qed.

Lemma resolve_update_signal : forall s lv v, update_signal (resolve_update s lv v) = lvalue_root lv.
Proof.
  intros s lv v. destruct (resolve_spec s lv) as [Hr _]. unfold resolve_update.
  destruct (resolve_lvalue s lv) as [[id o] w]. simpl in *. symmetry. exact Hr.
Qed.

Lemma ex_len : forall f st s n, length s = n -> (forall q, In q (fpl st) -> (fst q < n)%nat) ->
  length (ex f st s) = n.
Proof.
  induction f as [|f IH]; intros st s n Hl HR; [exact Hl | ].
  destruct st as [|nb rhs lhs|l|g y n0|scr arms]; simpl in *.
  - exact Hl.
  - unfold apply_update. rewrite length_write_signal; [exact Hl | ].
    rewrite resolve_update_signal, Hl. apply (HR (lvalue_root lhs, lv_mask lhs)). left. reflexivity.
  - assert (Hg : forall l0 s0, length s0 = n -> (forall st0, In st0 l0 -> forall q, In q (fpl st0) -> (fst q < n)%nat) ->
      length (fold_left (fun s' st' => ex f st' s') l0 s0) = n).
    { induction l0 as [|st0 l0 IHl]; intros s0 H0 H1; simpl; [exact H0 | ].
      apply IHl.
      - apply IH; [exact H0 | intros q Hq; apply (H1 st0 (or_introl eq_refl) q Hq)].
      - intros st1 Hst1 q Hq. apply (H1 st1 (or_intror Hst1) q Hq). }
    apply Hg; auto. intros st0 H0 q Hq. apply HR. apply in_flat_map. exists st0. auto.
  - destruct (Z.eqb (eval_expr s g) 0); apply IH; auto; intros q Hq; apply HR; apply in_or_app; auto.
  - destruct (select_in s (eval_expr s scr) arms SSkip) as [H|H].
    + rewrite H. destruct f; exact Hl.
    + apply IH; auto. intros q Hq. apply HR. apply in_flat_map.
      apply in_map_iff in H as [[ko b] [Hb Hin]]. simpl in Hb. subst b. exists (ko, select_case_stmt s (eval_expr s scr) arms SSkip). auto.
Qed.

Lemma run_len : forall p pr s n, (4 <= statement_fuel p)%nat -> PFrameOk pr -> length s = n ->
  (forall q, In q (fpp pr) -> (fst q < n)%nat) -> length (run_process p s pr) = n.
Proof.
  intros p pr s n Hf [H|[g [rhs [w [x Hs]]]]] Hl HR.
  - rewrite run_nbafree by exact H. apply ex_len; auto.
  - rewrite (run_latch p s pr g rhs w x Hf Hs). destruct (Z.eqb (eval_expr s g) 0); [exact Hl | ].
    unfold latch_upd, apply_update. rewrite length_write_signal; [exact Hl | ].
    simpl. rewrite Hl. apply (HR (x, lv_mask (LVar w x))). unfold fpp. rewrite (latch_fp _ g rhs w x Hs). left. reflexivity.
Qed.

Lemma runs_len : forall p ps s n, (4 <= statement_fuel p)%nat -> (forall pr, In pr ps -> PFrameOk pr) -> length s = n ->
  (forall pr q, In pr ps -> In q (fpp pr) -> (fst q < n)%nat) -> length (runs p ps s) = n.
Proof.
  intros p ps. induction ps as [|pr ps IH]; intros s n Hf H Hl HR; [exact Hl | ].
  unfold runs. simpl. fold (runs p ps (run_process p s pr)).
  apply IH; auto; [intros; apply H; right; auto | | intros; eapply HR; [right; eauto | eauto]].
  apply run_len; auto; [apply H; left; reflexivity | intros q Hq; eapply HR; [left; reflexivity | exact Hq]].
Qed.

Lemma comb_iter_S_r : forall p n s, comb_iter p (S n) s = comb_round p (comb_iter p n s).
Proof. intros p n. induction n as [|n IH]; intros s; [reflexivity | ]. simpl. simpl in IH. rewrite IH. reflexivity. Qed.

Lemma list_ext : forall (l1 l2 : list Z), length l1 = length l2 ->
  (forall r, (r < length l1)%nat -> read_signal l1 r = read_signal l2 r) -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] Hl H; simpl in Hl; try discriminate; [reflexivity | ].
  f_equal; [apply (H 0%nat); simpl; lia | ]. apply IH; [lia | ]. intros r Hr. apply (H (S r)). simpl. lia.
Qed.

Fixpoint Kiter (p : Program) (j : nat) (N : nat) : list Z :=
  match N with O => K0 p | S n => Kround p j (Kiter p j n) end.

Definition all_known (K : list Z) (n : nat) : bool :=
  forallb (fun r => Z.eqb (kg K r) (-1)) (seq 0 n).

Theorem comb_stable : forall p j g rhs w x N,
  Cert p j g rhs w x ->
  (forall pr, In pr (procs p) -> PFrameOk pr) ->
  (forall pr q, In pr (procs p) -> In q (fpp pr) -> (fst q < signal_count p)%nat) ->
  all_known (Kiter p j N) (signal_count p) = true ->
  forall seed, length seed = signal_count p ->
  comb_round p (comb_iter p N seed) = comb_iter p N seed.
Proof.
  intros p j g rhs w x N Hc Hfr HR Hk seed Hl.
  assert (Hf : (4 <= statement_fuel p)%nat) by (destruct Hc as [_ [_ [Hf _]]]; exact Hf).
  assert (Hlen : forall n, length (comb_iter p n seed) = signal_count p).
  { induction n as [|n IH]; [exact Hl | ]. rewrite comb_iter_S_r.
    unfold comb_round. change (fold_left (run_process p) (filter is_comb (processes p)) (comb_iter p n seed))
      with (runs p (procs p) (comb_iter p n seed)).
    apply runs_len; auto. }
  assert (Hag : forall n, Agree (Kiter p j n) (comb_iter p n seed) (comb_round p (comb_iter p n seed))).
  { induction n as [|n IH]; [apply base_agree; auto | ].
    simpl Kiter. rewrite comb_iter_S_r.
    eapply round_sound; [exact Hc | exact IH | reflexivity]. }
  symmetry. apply list_ext.
  - assert (Hl2 : length (comb_round p (comb_iter p N seed)) = signal_count p).
    { rewrite <- (comb_iter_S_r p N seed). apply Hlen. }
    rewrite Hl2, Hlen. reflexivity.
  - intros r Hr. rewrite Hlen in Hr. apply Z.bits_inj'. intros i Hi.
    apply (Hag N r i Hi).
    unfold all_known in Hk. rewrite forallb_forall in Hk.
    assert (Hr' : In r (seq 0 (signal_count p))) by (apply in_seq; lia).
    pose proof (Hk r Hr') as Hk0. apply Z.eqb_eq in Hk0 as Hk1.
    rewrite Hk1. rewrite Z.bits_m1 by auto. reflexivity.
Qed.

(** ---- boolean certificate front end (checked by computation) ---- *)
Definition pgood_b (p : Program) (x : nat) (pr : Process) : bool :=
  andb (andb (nbafree (process_body pr)) (Nat.leb (depth (process_body pr)) (statement_fuel p)))
       (forallb (fun q => negb (Nat.eqb (fst q) x)) (fpp pr)).

Definition cert_b (p : Program) (j : nat) : bool :=
  match latch_shape (process_body (nth j (procs p) dummy_proc)) with
  | Some (_, _, _, x) =>
      andb (andb (Nat.ltb j (length (procs p))) (Nat.leb 4 (statement_fuel p)))
           (forallb (pgood_b p x) (firstn j (procs p) ++ skipn (S j) (procs p)))
  | None => false
  end.

Definition frame_b (p : Program) : bool :=
  forallb (fun pr => orb (nbafree (process_body pr))
    (match latch_shape (process_body pr) with Some _ => true | None => false end)) (procs p).

Definition roots_b (p : Program) : bool :=
  forallb (fun pr => forallb (fun q => Nat.ltb (fst q) (signal_count p)) (fpp pr)) (procs p).

Lemma cert_b_sound : forall p j, cert_b p j = true -> exists g rhs w x, Cert p j g rhs w x.
Proof.
  intros p j H. unfold cert_b in H.
  destruct (latch_shape (process_body (nth j (procs p) dummy_proc))) as [[[[g rhs] w] x]|] eqn:Es; [ | discriminate].
  apply andb_true_iff in H as [H1 H2]. apply andb_true_iff in H1 as [H11 H12].
  exists g, rhs, w, x. refine (conj _ (conj _ (conj _ _))).
  - apply Nat.ltb_lt. exact H11.
  - exact Es.
  - apply Nat.leb_le. exact H12.
  - intros pq Hin. rewrite forallb_forall in H2.
    assert (Hin' : In pq (firstn j (procs p) ++ skipn (S j) (procs p))) by (apply in_or_app; auto).
    pose proof (H2 pq Hin') as Hp. unfold pgood_b in Hp.
    apply andb_true_iff in Hp as [Hp1 Hp2]. apply andb_true_iff in Hp1 as [Hp11 Hp12].
    unfold PGood. split; [exact Hp11 | split; [apply Nat.leb_le; exact Hp12 | ]].
    intros q Hq Hqx. rewrite forallb_forall in Hp2. specialize (Hp2 q Hq).
    apply negb_true_iff in Hp2. apply Nat.eqb_neq in Hp2. contradiction.
Qed.

Theorem comb_stable_b : forall p j N,
  cert_b p j = true -> frame_b p = true -> roots_b p = true ->
  all_known (Kiter p j N) (signal_count p) = true ->
  forall seed, length seed = signal_count p ->
  comb_round p (comb_iter p N seed) = comb_iter p N seed.
Proof.
  intros p j N Hc Hf Hr Hk. destruct (cert_b_sound p j Hc) as [g [rhs [w [x Hcert]]]].
  eapply comb_stable; [exact Hcert | | | exact Hk].
  - intros pr Hin. unfold frame_b in Hf. rewrite forallb_forall in Hf. specialize (Hf pr Hin).
    apply orb_true_iff in Hf as [H|H]; [left; exact H | right].
    destruct (latch_shape (process_body pr)) as [[[[g' rhs'] w'] x']|]; [ | discriminate].
    exists g', rhs', w', x'. reflexivity.
  - intros pr q Hin Hq. unfold roots_b in Hr. rewrite forallb_forall in Hr. specialize (Hr pr Hin).
    rewrite forallb_forall in Hr. specialize (Hr q Hq). apply Nat.ltb_lt in Hr. exact Hr.
Qed.

End ExtendedSVBitStability.
Print Assumptions ExtendedSVBitStability.comb_stable_b.
