(** Generic comb-invariant library (template route, CV32E40P C3/C4 agent, 2026-11-04).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    A list [L] of facts [(root, width, value)] ("norm width (read s root) = value") is an INVARIANT of every combinational round of a program when
    every assignment of every combinational process either targets a root outside [L], or writes a value that the 1-bit-OR aware evaluator
    [xeval4] derives from [L] itself (whole-root assignment) or a constant slice that agrees with the value (slice assignment).
    This covers constant tie-off slice writers (roots whose comb writers only drive constant slices) and alias latches.
    [hold_driven]: the invariant survives [phase_driven_state] (the changed signal not being a root of [L]). *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVEval3 Lang.ExtendedSVEval4.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVEval3 ExtendedSVEval4.
Local Open Scope Z_scope.
Module ExtendedSVHoldInv.

Definition HCl := (nat * nat * Z)%type.   (* root, width, value *)
Definition HHold (s : State) (L : list HCl) : Prop :=
  forall c, In c L -> norm (snd (fst c)) (read_signal s (fst (fst c))) = snd c.
Definition F_of (L : list HCl) : Facts := map (fun c => (EVar (snd (fst c)) (fst (fst c)), snd c)) L.

Lemma hhold_facts s L : HHold s L -> FactsHold s (F_of L).
Proof.
  intros H e z Hin. unfold F_of in Hin. apply in_map_iff in Hin as [c [Hc Hin]]. inversion Hc; subst.
  cbn [eval_expr]. apply H. exact Hin.
Qed.

Lemma ones_tb n m : 0 <= n -> 0 <= m -> Z.testbit (Z.ones n) m = (m <? n).
Proof.
  intros Hn Hm. destruct (Z.ltb_spec m n) as [H|H].
  - apply Z.ones_spec_low. lia.
  - apply Z.ones_spec_high. lia.
Qed.

(** ---- bit lemma: rewriting a slice with its own value changes nothing below the width ---- *)
Lemma norm_ones w x : norm w x = Z.land x (Z.ones (Z.of_nat w)).
Proof. unfold norm, mask. f_equal. rewrite Z.ones_equiv. lia. Qed.

Lemma write_slice_hold old off w val W c :
  0 <= off -> 0 <= w -> off + w <= W -> 0 <= W ->
  Z.land old (Z.ones W) = c -> Z.land (Z.shiftr c off) (Z.ones w) = val ->
  Z.land (write_slice old off w val) (Z.ones W) = c.
Proof.
  intros Ho Hw Hf HW Hold Hval.
  apply Z.bits_inj'. intros n Hn.
  assert (Hcn : Z.testbit c n = andb (Z.testbit old n) (n <? W)).
  { rewrite <- Hold. rewrite Z.land_spec. rewrite ones_tb by lia. reflexivity. }
  assert (Hfm : Z.testbit (Z.shiftl (2 ^ w - 1) off) n = andb (off <=? n) (n - off <? w)).
  { replace (2 ^ w - 1) with (Z.ones w) by (rewrite Z.ones_equiv; lia). rewrite Z.shiftl_spec by lia.
    destruct (Z.leb_spec off n) as [H|H].
    - rewrite ones_tb by lia. reflexivity.
    - rewrite Z.testbit_neg_r by lia. reflexivity. }
  assert (Hvs : Z.testbit (Z.shiftl val off) n = andb (off <=? n) (andb (Z.testbit c n) (n - off <? w))).
  { rewrite Z.shiftl_spec by lia. destruct (Z.leb_spec off n) as [H|H].
    - rewrite <- Hval. rewrite Z.land_spec, Z.shiftr_spec by lia. rewrite ones_tb by lia.
      replace (n - off + off) with n by lia. reflexivity.
    - rewrite Z.testbit_neg_r by lia. reflexivity. }
  unfold write_slice.
  rewrite Z.land_spec, Z.lor_spec, !Z.land_spec, Z.lnot_spec by lia.
  rewrite Hfm, Hvs, ones_tb by lia. rewrite Hcn.
  destruct (Z.leb_spec off n); destruct (Z.ltb_spec (n - off) w); destruct (Z.ltb_spec n W); cbn;
    try lia; destruct (Z.testbit old n); reflexivity.
Qed.


(** ---- updates ---- *)
Definition upd_ok (L : list HCl) (u : Update) : Prop :=
  forall c, In c L -> fst (fst c) = update_signal u ->
    0 <= update_offset u /\ update_offset u + Z.of_nat (update_width u) <= Z.of_nat (snd (fst c)) /\
    Z.land (Z.shiftr (snd c) (update_offset u)) (Z.ones (Z.of_nat (update_width u))) = update_value u.

Lemma apply_update_hold s L u : HHold s L -> upd_ok L u -> HHold (apply_update s u) L.
Proof.
  intros H U c Hc. unfold apply_update.
  destruct (Nat.eq_dec (fst (fst c)) (update_signal u)) as [E|E].
  - destruct (U c Hc E) as (U1 & U2 & U3).
    pose proof (H c Hc) as Hn. rewrite E in Hn. rewrite norm_ones in Hn.
    rewrite E. rewrite read_signal_write_same. rewrite norm_ones.
    exact (write_slice_hold _ _ _ _ _ _ U1 (Nat2Z.is_nonneg _) U2 (Nat2Z.is_nonneg _) Hn U3).
  - rewrite read_signal_write_other by congruence. apply H. exact Hc.
Qed.

Lemma apply_nba_hold L : forall us s, HHold s L -> (forall u, In u us -> upd_ok L u) -> HHold (apply_nba s us) L.
Proof.
  induction us as [|u rest IH]; intros s H U; cbn [apply_nba]; [exact H|].
  apply IH; [apply apply_update_hold; [exact H|apply U; left; reflexivity]|].
  intros u' Hu'. apply U. right. exact Hu'.
Qed.

(** ---- the assignment check ---- *)
Definition assign_ok_one (F : Facts) (rhs : Expr) (lhs : LValue) (c : HCl) : bool :=
  if Nat.eqb (fst (fst c)) (lvalue_root lhs) then
    match lhs with
    | LVar w r => Nat.eqb w (snd (fst c)) &&
        match xeval4 F rhs with Some z => Z.eqb (norm w z) (snd c) | None => false end
    | LSel w (LVar W r) (EConst k lsb) => Nat.eqb W (snd (fst c)) &&
        (Z.leb 0 (norm k lsb) && Z.leb (norm k lsb + Z.of_nat w) (Z.of_nat W)) &&
        match xeval4 F rhs with Some z => Z.eqb (Z.land (Z.shiftr (snd c) (norm k lsb)) (Z.ones (Z.of_nat w))) (norm w z) | None => false end
    | _ => false end
  else true.

Lemma resolve_root s lv : fst (fst (resolve_lvalue s lv)) = lvalue_root lv.
Proof.
  induction lv as [w id|w base IH lsb]; cbn [resolve_lvalue lvalue_root]; [reflexivity|].
  destruct (resolve_lvalue s base) as [[id off] w0]. cbn. cbn in IH. exact IH.
Qed.

Lemma assign_upd_ok L bs rhs lhs : HHold bs L -> forallb (assign_ok_one (F_of L) rhs lhs) L = true ->
  upd_ok L (resolve_update bs lhs (eval_expr bs rhs)).
Proof.
  unfold upd_ok. intros H Ha c Hc. rewrite forallb_forall in Ha. specialize (Ha c Hc). unfold assign_ok_one in Ha.
  pose proof (resolve_root bs lhs) as HR.
  unfold resolve_update. destruct (resolve_lvalue bs lhs) as [[id off] wd] eqn:Er.
  cbn [update_signal update_offset update_width update_value]. intros E.
  cbn in HR. subst id.
  rewrite E in Ha. rewrite Nat.eqb_refl in Ha.
  pose proof (hhold_facts bs L H) as HF.
  destruct lhs as [w r | w base lsb].
  - cbn in Er. inversion Er; subst. apply andb_prop in Ha as [Hw Hz]. apply Nat.eqb_eq in Hw.
    destruct (xeval4 (F_of L) rhs) as [z|] eqn:Ex; [|discriminate]. apply Z.eqb_eq in Hz.
    pose proof (xeval4_sound _ _ HF _ _ Ex) as Hev. rewrite Hev. cbn [update_offset update_width update_value].
    split; [lia|]. split; [lia|]. rewrite <- Hz. rewrite Z.shiftr_0_r. rewrite norm_ones.
    rewrite <- Z.land_assoc. rewrite Z.land_diag. reflexivity.
  - destruct base as [W r0 | ]; [|discriminate]. destruct lsb as [k lsb0| | | | | | | |]; try discriminate.
    cbn in Er. inversion Er; subst. apply andb_prop in Ha as [Hh Hz]. apply andb_prop in Hh as [Hw Hr]. apply andb_prop in Hr as [Hr1 Hr2].
    apply Nat.eqb_eq in Hw. apply Z.leb_le in Hr1. apply Z.leb_le in Hr2.
    destruct (xeval4 (F_of L) rhs) as [z|] eqn:Ex; [|discriminate]. apply Z.eqb_eq in Hz.
    pose proof (xeval4_sound _ _ HF _ _ Ex) as Hev. rewrite Hev. cbn [update_offset update_width update_value eval_expr].
    split; [lia|]. split; [lia|]. rewrite Hz. rewrite norm_ones. reflexivity.
Qed.

(** ---- statements ---- *)
Fixpoint stmt_okf (L : list HCl) (n : nat) (st : Stmt) {struct n} : bool :=
  match st with
  | SSkip => true
  | _ => match n with
         | O => false
         | S n' => match st with
                   | SSkip => true
                   | SAssign _ rhs lhs => forallb (assign_ok_one (F_of L) rhs lhs) L
                   | SSeq l => forallb (stmt_okf L n') l
                   | SIf _ y no => andb (stmt_okf L n' y) (stmt_okf L n' no)
                   | SCase _ arms => forallb (fun a => stmt_okf L n' (snd a)) arms
                   end
         end
  end.

Definition EInv (L : list HCl) (es : ExecState) : Prop :=
  HHold (blocking_state es) L /\ forall u, In u (pending_nba es) -> upd_ok L u.

Lemma stmt_ok_skip L n : stmt_okf L n SSkip = true. Proof. destruct n; reflexivity. Qed.

Lemma select_ok0 L n s v arms : forall d, stmt_okf L n d = true -> forallb (fun a => stmt_okf L n (snd a)) arms = true ->
  stmt_okf L n (select_case_stmt s v arms d) = true.
Proof.
  induction arms as [|[k body] rest IH]; intros d Hd H; cbn [select_case_stmt]; [exact Hd|].
  cbn [forallb snd] in H. apply andb_prop in H as [H1 H2].
  destruct k as [key|]; [destruct (Z.eqb v (eval_expr s key)); [exact H1|apply IH; assumption]|apply IH; assumption].
Qed.
Lemma select_ok L n s v arms : forallb (fun a => stmt_okf L n (snd a)) arms = true ->
  stmt_okf L n (select_case_stmt s v arms SSkip) = true.
Proof. intro H. apply select_ok0; [apply stmt_ok_skip|exact H]. Qed.

Lemma fold_exec_inv L n (IH : forall st f es, stmt_okf L n st = true -> EInv L es -> EInv L (exec_stmt f st es)) f :
  forall l es, forallb (stmt_okf L n) l = true -> EInv L es ->
  EInv L (fold_left (fun es' st' => exec_stmt f st' es') l es).
Proof.
  induction l as [|a rest IHl]; intros es Hl Hi; cbn [fold_left]; [exact Hi|].
  cbn [forallb] in Hl. apply andb_prop in Hl as [H1 H2]. apply IHl; [exact H2|]. apply IH; assumption.
Qed.

Lemma exec_inv L n : forall st f es, stmt_okf L n st = true -> EInv L es -> EInv L (exec_stmt f st es).
Proof.
  induction n as [|n IH]; intros st f es Hs Hi.
  - destruct st; cbn in Hs; try discriminate. destruct f; exact Hi.
  - destruct f as [|f]; [exact Hi|].
    destruct st as [|nba rhs lhs|l|g y no|sc arms]; cbn [stmt_okf] in Hs.
    + exact Hi.
    + destruct Hi as [Hb Hp]. cbn [exec_stmt].
      pose proof (assign_upd_ok L (blocking_state es) rhs lhs Hb Hs) as Uok.
      destruct nba.
      * cbn. split; [exact Hb|]. intros u Hu. apply in_app_or in Hu as [Hu|Hu]; [apply Hp; exact Hu|].
        destruct Hu as [Hu|[]]. subst u. exact Uok.
      * cbn. split; [apply apply_update_hold; assumption|exact Hp].
    + cbn [exec_stmt]. exact (fold_exec_inv L n IH f l es Hs Hi).
    + apply andb_prop in Hs as [H1 H2]. cbn [exec_stmt]. destruct (Z.eqb (eval_expr (blocking_state es) g) 0).
      * apply IH; assumption.
      * apply IH; assumption.
    + cbn [exec_stmt]. apply IH; [|exact Hi]. apply select_ok. exact Hs.
Qed.

Theorem run_process_hold p L n proc s : stmt_okf L n (process_body proc) = true -> HHold s L -> HHold (run_process p s proc) L.
Proof.
  intros Hs H. unfold run_process.
  pose proof (exec_inv L n (process_body proc) (statement_fuel p)
    {| blocking_state := s; pending_nba := []; emitted_updates := [] |} Hs (conj H (fun u (Hu : In u (@nil Update)) => False_ind _ Hu))) as [Hb Hp].
  apply apply_nba_hold; assumption.
Qed.

Definition comb_ok (p : Program) (L : list HCl) (n : nat) : bool :=
  forallb (fun proc => stmt_okf L n (process_body proc)) (filter is_comb (processes p)).

Lemma fold_round_hold p L n : forall l s, forallb (fun proc => stmt_okf L n (process_body proc)) l = true -> HHold s L ->
  HHold (fold_left (run_process p) l s) L.
Proof.
  induction l as [|a rest IH]; intros s Hl H; cbn [fold_left]; [exact H|].
  cbn [forallb] in Hl. apply andb_prop in Hl as [H1 H2]. apply IH; [exact H2|]. apply run_process_hold with (n := n); assumption.
Qed.

Theorem hold_round p L n s : comb_ok p L n = true -> HHold s L -> HHold (comb_round p s) L.
Proof. intros Hc H. unfold comb_round. apply fold_round_hold with (n := n); [exact Hc|exact H]. Qed.

Theorem hold_iter p L n k s : comb_ok p L n = true -> HHold s L -> HHold (comb_iter p k s) L.
Proof.
  intros Hc. revert s. induction k as [|k IH]; intros s H; cbn [comb_iter]; [exact H|].
  apply IH. apply hold_round with (n := n); assumption.
Qed.

Theorem hold_lfp p L n seed fixed : comb_ok p L n = true -> HHold seed L -> CombLFP p seed fixed -> HHold fixed L.
Proof. intros Hc H Hl. inversion Hl as [k fx Hk Hr]. subst. apply hold_iter with (n := n); assumption. Qed.

Lemma hhold_write_other s L x v : (forall c, In c L -> fst (fst c) <> x) -> HHold s L -> HHold (write_signal s x v) L.
Proof. intros Hx H c Hc. rewrite read_signal_write_other by (apply not_eq_sym, Hx; exact Hc). apply H. exact Hc. Qed.

Theorem hold_driven p L n ev pre : comb_ok p L n = true -> (forall c, In c L -> fst (fst c) <> changed_signal ev) ->
  HHold pre L -> HHold (phase_driven_state p ev pre) L.
Proof.
  intros Hc Hx H. unfold phase_driven_state, lfp_candidate.
  apply hold_iter with (n := n); [exact Hc|]. apply hhold_write_other; assumption.
Qed.


(** ---- ordered establishment: facts that a whole-root assignment of the round makes true ----
    [chain_ok n A T ps]: walking the comb processes in order, a process whose whole body is a whole-root assignment of a target fact
    [t in T] (right-hand side derived from the facts established so far) moves [t] into the assumed facts; every process must keep
    the assumed facts.  Then one comb round from a state satisfying [A] satisfies [A ++ T]. *)
Definition cl_eqb (a b : HCl) : bool := Nat.eqb (fst (fst a)) (fst (fst b)) && Nat.eqb (snd (fst a)) (snd (fst b)) && Z.eqb (snd a) (snd b).
Lemma cl_eqb_true a b : cl_eqb a b = true -> a = b.
Proof.
  destruct a as [[r w] c], b as [[r' w'] c']; unfold cl_eqb; cbn. intro H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.

Definition est_one (A : list HCl) (rhs : Expr) (w r : nat) (t : HCl) : bool :=
  Nat.eqb (fst (fst t)) r && Nat.eqb (snd (fst t)) w &&
  match xeval4 (F_of A) rhs with Some z => Z.eqb (norm w z) (snd t) | None => false end.
Definition est_find (A T : list HCl) (st : Stmt) : option HCl :=
  match st with
  | SAssign _ rhs (LVar w r) => find (est_one A rhs w r) T
  | _ => None
  end.

Fixpoint chain_ok (n : nat) (A T : list HCl) (ps : list Process) : bool :=
  match ps with
  | [] => match T with [] => true | _ => false end
  | pr :: rest =>
      match est_find A T (process_body pr) with
      | Some t => stmt_okf A n (process_body pr) && chain_ok n (A ++ [t]) (filter (fun c => negb (cl_eqb c t)) T) rest
      | None => stmt_okf A n (process_body pr) && chain_ok n A T rest
      end
  end.

Lemma ws0 old w val : 0 <= val < 2 ^ Z.of_nat w -> Z.land (write_slice old 0 (Z.of_nat w) val) (Z.ones (Z.of_nat w)) = val.
Proof.
  intros Hv. assert (Hw : 0 <= Z.of_nat w) by lia.
  assert (Hval : Z.land val (Z.ones (Z.of_nat w)) = val) by (rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  apply Z.bits_inj'. intros n Hn.
  assert (Hb : Z.testbit val n = andb (Z.testbit val n) (n <? Z.of_nat w)).
  { pose proof (f_equal (fun x => Z.testbit x n) Hval) as Hb. cbn in Hb. rewrite Z.land_spec, ones_tb in Hb by lia. symmetry. exact Hb. }
  unfold write_slice. rewrite Z.shiftl_0_r.
  replace (2 ^ Z.of_nat w - 1) with (Z.ones (Z.of_nat w)) by (rewrite Z.ones_equiv; lia).
  rewrite Z.shiftl_0_r. rewrite Z.land_spec, Z.lor_spec, !Z.land_spec, Z.lnot_spec by lia.
  rewrite ones_tb by lia.
  destruct (Z.ltb_spec n (Z.of_nat w)); cbn in Hb |- *; destruct (Z.testbit old n); destruct (Z.testbit val n); cbn in Hb |- *;
    first [reflexivity | discriminate Hb].
Qed.

Lemma est_hold p A T pr t s : statement_fuel p <> 0%nat -> est_find A T (process_body pr) = Some t -> HHold s A ->
  HHold (run_process p s pr) [t].
Proof.
  intros Hf0 Hf H. unfold est_find in Hf. destruct (process_body pr) as [|nba rhs lhs| | |] eqn:Eb; try discriminate.
  destruct lhs as [w r|]; try discriminate.
  apply find_some in Hf as [Hin Ho]. unfold est_one in Ho. apply andb_prop in Ho as [Ho Hz]. apply andb_prop in Ho as [Hr Hw].
  apply Nat.eqb_eq in Hr. apply Nat.eqb_eq in Hw.
  destruct (xeval4 (F_of A) rhs) as [z|] eqn:Ex; [|discriminate]. apply Z.eqb_eq in Hz.
  pose proof (xeval4_sound _ _ (hhold_facts s A H) _ _ Ex) as Hev.
  intros c Hc. destruct Hc as [Hc|[]]. subst c. cbn [fst snd]. rewrite Hr, Hw.
  unfold run_process. rewrite Eb.
  assert (Hrange : 0 <= norm w z < 2 ^ Z.of_nat w).
  { rewrite norm_ones. rewrite Z.land_ones by lia. split; [apply Z.mod_pos_bound|apply Z.mod_pos_bound]; apply Z.pow_pos_nonneg; lia. }
  assert (Hfin : forall s', s' = apply_update s {| update_signal := r; update_offset := 0; update_width := w; update_value := norm w z |} ->
            norm w (read_signal s' r) = snd t).
  { intros s' ->. unfold apply_update. cbn [update_signal update_offset update_width update_value]. rewrite read_signal_write_same.
    rewrite norm_ones. rewrite (ws0 _ w _ Hrange). exact Hz. }
  destruct (statement_fuel p) as [|f]; [exfalso; apply Hf0; reflexivity|].
  destruct nba; cbn [exec_stmt blocking_state pending_nba]; unfold resolve_update; cbn [resolve_lvalue]; rewrite Hev; cbn [apply_nba blocking_state pending_nba]; apply Hfin; reflexivity.
Qed.

Lemma hhold_sub L L' s : (forall c, In c L -> In c L') -> HHold s L' -> HHold s L.
Proof. intros Hs H c Hc. apply H, Hs; exact Hc. Qed.

Theorem chain_round p n : statement_fuel p <> 0%nat -> forall ps A T s, chain_ok n A T ps = true -> HHold s A ->
  HHold (fold_left (run_process p) ps s) (A ++ T).
Proof.
  intro Hf0. induction ps as [|pr rest IH]; intros A T s Hc H; cbn [chain_ok] in Hc.
  - destruct T; [|discriminate]. cbn [fold_left]. rewrite app_nil_r. exact H.
  - cbn [fold_left].
    destruct (est_find A T (process_body pr)) as [t|] eqn:Ee.
    + apply andb_prop in Hc as [H1 H2].
      pose proof (run_process_hold p A n pr s H1 H) as Hs1.
      pose proof (est_hold p A T pr t s Hf0 Ee H) as Ht.
      assert (Hs2 : HHold (run_process p s pr) (A ++ [t])).
      { intros c Hc'. apply in_app_or in Hc' as [Hc'|Hc']; [apply Hs1; exact Hc'|apply Ht; exact Hc']. }
      pose proof (IH _ _ _ H2 Hs2) as Hr.
      apply (hhold_sub (A ++ T) ((A ++ [t]) ++ filter (fun c => negb (cl_eqb c t)) T) _ ) in Hr; [exact Hr|].
      intros c Hc'. apply in_app_or in Hc' as [Hc'|Hc'].
      * apply in_or_app. left. apply in_or_app. left. exact Hc'.
      * destruct (cl_eqb c t) eqn:Eq.
        -- apply in_or_app. left. apply in_or_app. right. left. symmetry. apply cl_eqb_true. exact Eq.
        -- apply in_or_app. right. apply filter_In. split; [exact Hc'|]. rewrite Eq. reflexivity.
    + apply andb_prop in Hc as [H1 H2].
      pose proof (run_process_hold p A n pr s H1 H) as Hs1.
      exact (IH _ _ _ H2 Hs1).
Qed.

Definition chain_round_ok (p : Program) (n : nat) (A T : list HCl) : bool := chain_ok n A T (filter is_comb (processes p)).
Theorem chain_comb_round p n A T s : statement_fuel p <> 0%nat -> chain_round_ok p n A T = true -> HHold s A -> HHold (comb_round p s) (A ++ T).
Proof. intros Hf Hc H. unfold comb_round. exact (chain_round p n Hf _ A T s Hc H). Qed.

Theorem chain_lfp p n A T seed fixed : statement_fuel p <> 0%nat -> chain_round_ok p n A T = true -> CombLFP p seed fixed -> HHold fixed A -> HHold fixed (A ++ T).
Proof.
  intros Hf Hc Hl H. inversion Hl as [k fx Hk Hr]. subst fx.
  pose proof (chain_comb_round p n A T _ Hf Hc H) as H2. rewrite Hr in H2. exact H2.
Qed.

End ExtendedSVHoldInv.
Print Assumptions ExtendedSVHoldInv.hold_lfp.
Print Assumptions ExtendedSVHoldInv.hold_driven.
Print Assumptions ExtendedSVHoldInv.chain_lfp.
