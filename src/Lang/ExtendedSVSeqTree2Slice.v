(** Slice-aware next-state value for two-level trees (template route, 2026-11-04; additive on ExtendedSVSeqTree2, nothing existing changed).
    `lastws` folds the executed non-blocking updates of ONE root exactly as `apply_updates_root_value` does (full-width writes AND part-select
    writes, in order, last write of a bit wins), so no well-formedness condition on the writers is needed; `seq_tree2s_value` is the exact
    register value after the edge.  `lastbit` gives bit j of the result when every write of the root is a 1-bit constant-lsb part select
    (the packed flag registers of angelo5fix process 8).  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
 Lang.ExtendedSVAssignment Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVWordInvariant Lang.ExtendedSVSeqStep Lang.ExtendedSVSeqTree Lang.ExtendedSVSeqTree2.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVAssignment ExtendedSVWordInvariant ExtendedSVSeqStep ExtendedSVSeqTree ExtendedSVSeqTree2.
Local Open Scope Z_scope.
Module ExtendedSVSeqTree2Slice.

Definition step_s (s : State) (r : signal) (acc : Z) (st : Stmt) : Z :=
 match st with SAssign _ e lhs => apply_update_root_value r acc (resolve_update s lhs (eval_expr s e)) | _ => acc end.
Definition lastws (s : State) (r : signal) (sts : list Stmt) (acc : Z) : Z := fold_left (step_s s r) sts acc.

Lemma apply_lastws : forall s r sts cur, apply_updates_root_value r cur (nba_updates s sts) = lastws s r sts cur.
Proof.
 intros s r sts. induction sts as [|st rest IH]; intro cur; [reflexivity|].
 destruct st as [|nb e lhs| | |]; cbn [nba_updates lastws fold_left step_s apply_updates_root_value]; try exact (IH cur).
 apply IH.
Qed.

Theorem seq_tree2s_value : forall p ev pre r P t T kf,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [t]] -> Rel2 kf t T -> (kf + 2 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 read_signal (PhaseSemantics p ev pre) r =
 lastws (phase_driven_state p ev pre) r (tleaf2 (phase_driven_state p ev pre) T) (read_signal (phase_driven_state p ev pre) r).
Proof.
 intros p ev pre r P t T kf HU HE HB HR HF HW.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain, selected_on_transition.
 rewrite process_slice_sound.
 rewrite filter_swap, HW. cbn [flat_map]. rewrite app_nil_r.
 rewrite (process_updates_tree2 p _ P kf t T HB HR HF).
 rewrite apply_lastws. rewrite (driven_unchanged p ev pre r HU HE). reflexivity.
Qed.

(** ---- bit view ---- *)
Lemma testbit_write_slice1 : forall old k v j, 0 <= k -> 0 <= j ->
 Z.testbit (write_slice old k 1 (norm 1 v)) j = if Z.eqb j k then Z.testbit v 0 else Z.testbit old j.
Proof.
 intros old k v j Hk Hj. unfold write_slice, norm, mask.
 replace (2 ^ Z.of_nat 1 - 1) with 1 by reflexivity.
 replace (2 ^ 1 - 1) with 1 by reflexivity.
 rewrite Z.lor_spec, !Z.land_spec by assumption.
 rewrite Z.lnot_spec by assumption.
 rewrite !Z.shiftl_spec by assumption.
 destruct (Z.eqb_spec j k) as [->|Hne].
 - rewrite Z.sub_diag.
   assert (E1 : Z.testbit (Z.land v 1) 0 = Z.testbit v 0) by (rewrite Z.land_spec; cbn; apply andb_true_r).
   rewrite E1. replace (Z.testbit 1 0) with true by reflexivity.
   destruct (Z.testbit old k), (Z.testbit v 0); reflexivity.
 - assert (Hb : Z.testbit 1 (j - k) = false).
   { destruct (Z.lt_ge_cases j k) as [Hl|Hg].
     - apply Z.testbit_neg_r. lia.
     - assert (0 < j - k) by lia. destruct (j - k) eqn:E; try lia. cbn. reflexivity. }
   rewrite Hb. destruct (Z.testbit old j), (Z.testbit (Z.land v 1) (j - k)); reflexivity.
Qed.

Definition step_b (s : State) (r : signal) (j : Z) (acc : bool) (st : Stmt) : bool :=
 match st with
 | SAssign _ e (LSel 1 (LVar _ r') (EConst n k)) => if Nat.eqb r' r && Z.eqb (norm n k) j then Z.testbit (eval_expr s e) 0 else acc
 | _ => acc end.
Definition lastbit (s : State) (r : signal) (j : Z) (sts : list Stmt) (acc : bool) : bool := fold_left (step_b s r j) sts acc.

(** every write of r in sts is a 1-bit part select with constant non-negative lsb *)
Definition slice1_all (r : signal) (sts : list Stmt) : Prop :=
 forall st, In st sts -> writes_stmtb r st = true ->
 exists nb e W n k, st = SAssign nb e (LSel 1 (LVar W r) (EConst n k)).

Lemma resolve_root0 : forall s lhs, fst (fst (resolve_lvalue s lhs)) = lvalue_root lhs.
Proof.
 intros s lhs. induction lhs as [w x|w base IH lsb]; cbn; [reflexivity|].
 destruct (resolve_lvalue s base) as [[a b] c]. cbn in *. exact IH.
Qed.
Lemma resolve_root : forall s lhs id off wd, resolve_lvalue s lhs = (id, off, wd) -> id = lvalue_root lhs.
Proof. intros s lhs id off wd E. rewrite <- (resolve_root0 s lhs), E. reflexivity. Qed.

Lemma lastbit_correct : forall s r j sts acc, 0 <= j -> slice1_all r sts ->
 Z.testbit (lastws s r sts acc) j = lastbit s r j sts (Z.testbit acc j).
Proof.
 intros s r j sts. induction sts as [|st rest IH]; intros acc Hj HA; [reflexivity|].
 assert (HA' : slice1_all r rest) by (intros st' Hin Hw; apply HA; [right; exact Hin|exact Hw]).
 cbn [lastws lastbit fold_left]. 
 destruct (writes_stmtb r st) eqn:Hw.
 - destruct (HA st (or_introl eq_refl) Hw) as [nb [e [W [n [k ->]]]]].
   assert (Hk : 0 <= norm n k) by (unfold norm, mask; apply Z.land_nonneg; right; assert (0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia); lia).
   cbn [step_s step_b]. unfold apply_update_root_value, resolve_update. cbn [resolve_lvalue update_signal update_offset update_width update_value].
   rewrite Nat.eqb_refl. cbn [Nat.eqb andb].
   rewrite Z.add_0_l.
   change (fold_left (step_s s r) rest _) with (lastws s r rest (write_slice acc (norm n k) (Z.of_nat 1) (norm 1 (eval_expr s e)))).
   rewrite (IH _ Hj HA'). f_equal.
   cbn [Z.of_nat]. rewrite (testbit_write_slice1 acc (norm n k) _ j Hk Hj).
   rewrite (Z.eqb_sym j (norm n k)). reflexivity.
 - fold (lastws s r rest (step_s s r acc st)). 
   assert (Hs : step_s s r acc st = acc).
   { destruct st; try reflexivity. cbn in Hw. unfold step_s, apply_update_root_value, resolve_update.
     destruct (resolve_lvalue s lhs) as [[id off] wd] eqn:E. cbn.
     rewrite (resolve_root s lhs _ _ _ E), Hw. reflexivity. }
   rewrite Hs. 
   assert (Hb : step_b s r j (Z.testbit acc j) st = Z.testbit acc j).
   { destruct st; try reflexivity. cbn [step_b]. destruct lhs as [|w' base lsb]; try reflexivity.
     destruct w' as [|[|w'']]; try reflexivity. destruct base as [W r'|]; try reflexivity. destruct lsb; try reflexivity.
     cbn in Hw. destruct (Nat.eqb r' r) eqn:Er; [|reflexivity]. discriminate Hw. }
   rewrite Hb. exact (IH acc Hj HA').
Qed.

(** state independent over-approximation of the statements a tree can execute, and a boolean check of slice1_all on it *)
Fixpoint tstmts (T : Tree) : list Stmt := match T with TLeaf l => l | TIf _ y n => tstmts y ++ tstmts n end.
Fixpoint tstmts2 (T : Tree2) : list Stmt :=
 match T with T2Cat Ts => flat_map tstmts Ts | T2If _ y n => tstmts2 y ++ tstmts2 n end.

Lemma tleaf_sub : forall s T st, In st (tleaf s T) -> In st (tstmts T).
Proof.
 intros s T. induction T as [l|g y IHy n IHn]; cbn [tleaf tstmts]; intros st H; [exact H|].
 apply in_or_app. destruct (Z.eqb (eval_expr s g) 0); [right; exact (IHn _ H)|left; exact (IHy _ H)].
Qed.
Lemma tleaf2_sub : forall s T st, In st (tleaf2 s T) -> In st (tstmts2 T).
Proof.
 intros s T. induction T as [Ts|g y IHy n IHn]; cbn [tleaf2 tstmts2]; intros st H.
 - apply in_flat_map in H as [T0 [H1 H2]]. apply in_flat_map. exists T0. split; [exact H1|exact (tleaf_sub s T0 st H2)].
 - apply in_or_app. destruct (Z.eqb (eval_expr s g) 0); [right; exact (IHn _ H)|left; exact (IHy _ H)].
Qed.

Definition slice1b (r : signal) (st : Stmt) : bool :=
 match st with SAssign _ _ (LSel 1 (LVar _ r') (EConst _ _)) => true | _ => negb (writes_stmtb r st) end.

Lemma slice1b_ok : forall r l, forallb (slice1b r) l = true -> slice1_all r l.
Proof.
 intros r l H st Hin Hw. rewrite forallb_forall in H. specialize (H st Hin). unfold slice1b in H.
 destruct st as [|nb e lhs| | |]; try (cbn in Hw; discriminate Hw).
 destruct lhs as [|w base lsb]; [cbn in H, Hw; rewrite Hw in H; discriminate|].
 destruct w as [|[|w]]; try (cbn in H, Hw; rewrite Hw in H; discriminate).
 destruct base as [W r'|]; try (cbn in H, Hw; rewrite Hw in H; discriminate).
 destruct lsb; try (cbn in H, Hw; rewrite Hw in H; discriminate).
 cbn in Hw. apply Nat.eqb_eq in Hw. subst r'. eexists _, _, _, _, _. reflexivity.
Qed.

Theorem slice1_tree2 : forall r T, forallb (slice1b r) (tstmts2 T) = true -> forall s, slice1_all r (tleaf2 s T).
Proof.
 intros r T H s st Hin Hw. apply (slice1b_ok r _ H); [exact (tleaf2_sub s T st Hin)|exact Hw].
Qed.

End ExtendedSVSeqTree2Slice.


Print Assumptions ExtendedSVSeqTree2Slice.seq_tree2s_value.
Print Assumptions ExtendedSVSeqTree2Slice.lastbit_correct.
Print Assumptions ExtendedSVSeqTree2Slice.slice1_tree2.
