(** Two-level variant of ExtendedSVSeqTree (template route, 2026-11-04; additive, nothing existing is changed).
    A sequential process body may be a decision tree whose LEAVES are SEQUENCES of independent decision trees of ExtendedSVSeqTree
    (reset test on top; below it several `if (ce) ...` statements writing disjoint registers, plus plain non-blocking assignments).
    The executed non-blocking updates are the concatenation of the item leaves; the next value of a register is the value of the unique item
    that writes it.  Generic, design independent.  Generated-shape conversion `conv2` is boolean; the theorem `seq_tree2_value` mirrors
    `ExtendedSVSeqTree.seq_tree_value`.  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
 Lang.ExtendedSVAssignment Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVWordInvariant Lang.ExtendedSVSeqStep Lang.ExtendedSVSeqTree.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVAssignment ExtendedSVWordInvariant ExtendedSVSeqStep ExtendedSVSeqTree.
Local Open Scope Z_scope.
Module ExtendedSVSeqTree2.

Inductive Tree2 : Type := T2Cat (Ts : list Tree) | T2If (g : Expr) (y n : Tree2).

Fixpoint tleaf2 (s : State) (T : Tree2) : list Stmt :=
 match T with
 | T2Cat Ts => flat_map (tleaf s) Ts
 | T2If g y n => if Z.eqb (eval_expr s g) 0 then tleaf2 s n else tleaf2 s y
 end.

Inductive RelItems : nat -> list Stmt -> list Tree -> Prop :=
 | RINil : RelItems 0%nat [] []
 | RICons : forall k st T m l Ts, Rel k st T -> RelItems m l Ts -> RelItems (Nat.max k m) (st :: l) (T :: Ts).

Inductive Rel2 : nat -> Stmt -> Tree2 -> Prop :=
 | R2Cat : forall m l Ts, RelItems m l Ts -> Rel2 (S m) (SSeq l) (T2Cat Ts)
 | R2Skip : Rel2 1%nat SSkip (T2Cat [])
 | R2Assign : forall e lhs, Rel2 1%nat (SAssign true e lhs) (T2Cat [TLeaf [SAssign true e lhs]])
 | R2If : forall g y n ky kn Ty Tn, Rel2 ky y Ty -> Rel2 kn n Tn -> Rel2 (S (Nat.max ky kn)) (SIf g y n) (T2If g Ty Tn).

Lemma exec_items : forall m l Ts, RelItems m l Ts -> forall f s pn em, (m <= f)%nat ->
 fold_left (fun es' st' => exec_stmt f st' es') l {| blocking_state := s; pending_nba := pn; emitted_updates := em |} =
 {| blocking_state := s; pending_nba := pn ++ nba_updates s (flat_map (tleaf s) Ts); emitted_updates := em ++ nba_updates s (flat_map (tleaf s) Ts) |}.
Proof.
 intros m l Ts HR. induction HR as [|k st T m l Ts Hk HR IH]; intros f s pn em HF.
 - cbn. now rewrite !app_nil_r.
 - cbn [fold_left]. rewrite (exec_rel k st T Hk f _) by lia. cbn [blocking_state pending_nba emitted_updates].
   rewrite (IH f s (pn ++ nba_updates s (tleaf s T)) (em ++ nba_updates s (tleaf s T))) by lia.
   cbn [flat_map]. rewrite nba_updates_app, !app_assoc. reflexivity.
Qed.

Lemma exec_rel2 : forall k t T, Rel2 k t T -> forall f es, (k <= f)%nat ->
 exec_stmt f t es =
 {| blocking_state := blocking_state es;
    pending_nba := pending_nba es ++ nba_updates (blocking_state es) (tleaf2 (blocking_state es) T);
    emitted_updates := emitted_updates es ++ nba_updates (blocking_state es) (tleaf2 (blocking_state es) T) |}.
Proof.
 intros k t T HR. induction HR as [m l Ts HI| |e lhs|g y n ky kn Ty Tn Hy IHy Hn IHn]; intros f es HD.
 - destruct f as [|f]; [lia|]. rewrite exec_seq. destruct es as [s pn em]. cbn [blocking_state pending_nba emitted_updates tleaf2].
   exact (exec_items _ _ _ HI f s pn em (ltac:(lia))).
 - destruct f as [|f]; [lia|]. cbn [exec_stmt tleaf2 flat_map nba_updates]. destruct es; cbn; rewrite !app_nil_r; reflexivity.
 - destruct f as [|f]; [lia|]. destruct es as [s pn em]. rewrite exec_assign_nba.
   cbn [tleaf2 flat_map tleaf nba_updates blocking_state pending_nba emitted_updates]. rewrite ?app_nil_r. reflexivity.
 - destruct f as [|f]; [lia|].
   cbn [exec_stmt tleaf2]. destruct (Z.eqb (eval_expr (blocking_state es) g) 0).
   + apply IHn. lia.
   + apply IHy. lia.
Qed.

Lemma process_updates_tree2 : forall p s proc k t T,
 process_body proc = SSeq [SSeq [t]] -> Rel2 k t T -> (k + 2 <= statement_fuel p)%nat ->
 process_updates p s proc = nba_updates s (tleaf2 s T).
Proof.
 intros p s proc k t T HB HR HF. unfold process_updates. rewrite HB.
 destruct (statement_fuel p) as [|[|f]]; try lia.
 rewrite exec_seq. cbn [fold_left]. rewrite exec_seq. cbn [fold_left].
 rewrite (exec_rel2 k t T HR f _) by lia. cbn [emitted_updates blocking_state]. reflexivity.
Qed.

(** boolean conversion *)
Fixpoint conv_items (fuel : nat) (l : list Stmt) : option (nat * list Tree) :=
 match l with
 | [] => Some (0%nat, [])
 | st :: rest =>
   match conv fuel st, conv_items fuel rest with
   | Some (k, T), Some (m, Ts) => Some (Nat.max k m, T :: Ts)
   | _, _ => None
   end
 end.

Lemma conv_items_sound : forall fuel l m Ts, conv_items fuel l = Some (m, Ts) -> RelItems m l Ts.
Proof.
 intros fuel l. induction l as [|st rest IH]; intros m Ts H; cbn [conv_items] in H.
 - inversion H; subst. constructor.
 - destruct (conv fuel st) as [[k T]|] eqn:Hc; [|discriminate].
   destruct (conv_items fuel rest) as [[m' Ts']|] eqn:Hi; [|discriminate]. inversion H; subst; clear H.
   constructor; [exact (conv_sound _ _ _ _ Hc)|exact (IH m' Ts' eq_refl)].
Qed.

Fixpoint conv2 (fuel : nat) (t : Stmt) : option (nat * Tree2) :=
 match fuel with
 | O => None
 | S k =>
   match t with
   | SIf g y n =>
       match conv2 k y, conv2 k n with
       | Some (dy, Ty), Some (dn, Tn) => Some (S (Nat.max dy dn), T2If g Ty Tn)
       | _, _ => None
       end
   | SSeq l => match conv_items k l with Some (m, Ts) => Some (S m, T2Cat Ts) | None => None end
   | SSkip => Some (1%nat, T2Cat [])
   | SAssign true e lhs => Some (1%nat, T2Cat [TLeaf [SAssign true e lhs]])
   | _ => None
   end
 end.

Lemma conv2_sound : forall fuel t d T, conv2 fuel t = Some (d, T) -> Rel2 d t T.
Proof.
 induction fuel as [|k IH]; intros t d T H; [discriminate|].
 destruct t as [|b e lhs|l|g y n|sc arms]; cbn [conv2] in H; try discriminate.
 - inversion H; subst; clear H. constructor.
 - destruct b; try discriminate. inversion H; subst; clear H. constructor.
 - destruct (conv_items k l) as [[m Ts]|] eqn:Hc; [|discriminate]. inversion H; subst; clear H.
   constructor. exact (conv_items_sound _ _ _ _ Hc).
 - destruct (conv2 k y) as [[dy Ty]|] eqn:Hy; [|discriminate]. destruct (conv2 k n) as [[dn Tn]|] eqn:Hn; [|discriminate].
   inversion H; subst; clear H. constructor; eapply IH; eassumption.
Qed.

(** ---- value form ---- *)
Fixpoint tw (r : signal) (T : Tree) : bool :=
 match T with
 | TLeaf l => existsb (writes_stmtb r) l
 | TIf _ y n => tw r y || tw r n
 end.

Lemma existsb_false_filter : forall (A : Type) (f : A -> bool) (l : list A), existsb f l = false -> filter f l = [].
Proof.
 intros A f l. induction l as [|a l IH]; intro H; [reflexivity|]. cbn in H. apply orb_false_iff in H as [H1 H2].
 cbn [filter]. rewrite H1. exact (IH H2).
Qed.

Lemma tw_false : forall r T s, tw r T = false -> existsb (writes_stmtb r) (tleaf s T) = false.
Proof.
 intros r T s. induction T as [l|g y IHy n IHn]; cbn [tw tleaf]; intro H; [exact H|].
 apply orb_false_iff in H as [Hy Hn]. destruct (Z.eqb (eval_expr s g) 0); [exact (IHn Hn)|exact (IHy Hy)].
Qed.

Definition titems_expr (w : nat) (r : signal) (Ts : list Tree) : Expr :=
 match filter (tw r) Ts with [T] => texpr w r T | _ => EVar w r end.
Definition titems_wf (w : nat) (r : signal) (Ts : list Tree) : bool :=
 match filter (tw r) Ts with [] => true | [T] => twf w r T | _ => false end.

Fixpoint texpr2 (w : nat) (r : signal) (T : Tree2) : Expr :=
 match T with
 | T2Cat Ts => titems_expr w r Ts
 | T2If g y n => ECond w g (texpr2 w r y) (texpr2 w r n)
 end.
Fixpoint twf2 (w : nat) (r : signal) (T : Tree2) : bool :=
 match T with
 | T2Cat Ts => titems_wf w r Ts
 | T2If _ y n => twf2 w r y && twf2 w r n
 end.

Lemma filter_items : forall r s Ts, filter (writes_stmtb r) (flat_map (tleaf s) Ts) =
 flat_map (fun T => filter (writes_stmtb r) (tleaf s T)) (filter (tw r) Ts).
Proof.
 intros r s Ts. induction Ts as [|T rest IH]; [reflexivity|].
 cbn [flat_map]. rewrite filter_app, IH. cbn [filter]. destruct (tw r T) eqn:Ht.
 - cbn [flat_map]. reflexivity.
 - rewrite (existsb_false_filter _ _ _ (tw_false r T s Ht)). reflexivity.
Qed.

Lemma items_leaf : forall w r s Ts, titems_wf w r Ts = true ->
 norm w (eval_expr s (titems_expr w r Ts)) = norm w (eval_expr s (leaf_expr w r (flat_map (tleaf s) Ts))) /\ leaf_wf w r (flat_map (tleaf s) Ts) = true.
Proof.
 intros w r s Ts H. unfold titems_wf in H. unfold titems_expr, leaf_expr, leaf_wf. rewrite filter_items.
 destruct (filter (tw r) Ts) as [|T0 [|T1 rest]] eqn:Hf; cbn [flat_map]; try discriminate.
 - split; reflexivity.
 - rewrite app_nil_r. split.
   + pose proof (texpr_leaf w r s T0) as E. unfold leaf_expr in E. exact E.
   + pose proof (twf_leaf w r s T0 H) as E. unfold leaf_wf in E. exact E.
Qed.

Lemma texpr2_leaf : forall w r s T, twf2 w r T = true ->
 norm w (eval_expr s (texpr2 w r T)) = norm w (eval_expr s (leaf_expr w r (tleaf2 s T))) /\ leaf_wf w r (tleaf2 s T) = true.
Proof.
 intros w r s T. induction T as [Ts|g y IHy n IHn]; cbn [twf2 texpr2 tleaf2]; intro H; [exact (items_leaf w r s Ts H)|].
 apply andb_true_iff in H as [Hy Hn]. cbn [eval_expr]. rewrite norm_idempotent.
 destruct (Z.eqb (eval_expr s g) 0); [exact (IHn Hn)|exact (IHy Hy)].
Qed.

(** value of a register whose process updates are a given non-blocking list *)
Theorem seq_upd_value : forall p ev pre r P sts w,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 process_updates p (phase_driven_state p ev pre) P = nba_updates (phase_driven_state p ev pre) sts ->
 leaf_wf w r sts = true ->
 norm w (read_signal (PhaseSemantics p ev pre) r) = norm w (eval_expr (phase_driven_state p ev pre) (leaf_expr w r sts)).
Proof.
 intros p ev pre r P sts w HU HE HW HPU HWF.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain, selected_on_transition.
 set (driven := phase_driven_state p ev pre) in *.
 rewrite process_slice_sound.
 rewrite filter_swap, HW. cbn [flat_map]. rewrite app_nil_r.
 rewrite HPU.
 destruct (leaf_wf_cases w r _ HWF) as [Ef|[e Ef]].
 - unfold leaf_expr. rewrite Ef.
   rewrite apply_root_avoids by (apply nba_updates_avoid; exact (filter_nil_existsb _ _ _ Ef)).
   cbn [eval_expr]. unfold driven. rewrite (driven_unchanged p ev pre r HU HE). rewrite norm_idempotent. reflexivity.
 - unfold leaf_expr. rewrite Ef.
   destruct (filter_single_split _ _ _ _ Ef) as [k [HK [HP HQ]]].
   pose proof (nth_error_split sts k HK) as [l1 [l2 [Hsplit Hlen]]].
   assert (Hl1 : firstn k sts = l1).
   { rewrite Hsplit, firstn_app. rewrite firstn_all2 by lia. replace (k - length l1)%nat with 0%nat by lia. cbn. now rewrite app_nil_r. }
   assert (Hl2 : skipn (S k) sts = l2).
   { rewrite Hsplit, skipn_app. rewrite skipn_all2 by lia. replace (S k - length l1)%nat with 1%nat by lia. reflexivity. }
   rewrite Hl1 in HP. rewrite Hl2 in HQ.
   rewrite Hsplit, nba_updates_app. cbn [nba_updates].
   rewrite !apply_root_app.
   rewrite (apply_root_avoids r (nba_updates driven l1) _ (nba_updates_avoid driven r l1 HP)).
   cbn [apply_updates_root_value].
   rewrite (apply_root_avoids r (nba_updates driven l2) _ (nba_updates_avoid driven r l2 HQ)).
   unfold apply_update_root_value, resolve_update. cbn [resolve_lvalue update_signal update_offset update_width update_value].
   rewrite Nat.eqb_refl. rewrite norm_full_low_write. apply norm_idempotent.
Qed.

Theorem seq_tree2_value : forall p ev pre r P t T kf w,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [t]] -> Rel2 kf t T -> (kf + 2 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 twf2 w r T = true ->
 norm w (read_signal (PhaseSemantics p ev pre) r) = norm w (eval_expr (phase_driven_state p ev pre) (texpr2 w r T)).
Proof.
 intros p ev pre r P t T kf w HU HE HB HR HF HW HWF.
 destruct (texpr2_leaf w r (phase_driven_state p ev pre) T HWF) as [H1 H2].
 rewrite H1.
 exact (seq_upd_value p ev pre r P _ w HU HE HW (process_updates_tree2 p _ P kf t T HB HR HF) H2).
Qed.


(** ---- ordered multi-writer form: several items of a leaf sequence may write the same register (the last firing item wins) ---- *)
Definition step_w (s : State) (r : signal) (acc : Z) (st : Stmt) : Z :=
 match st with SAssign _ e lhs => if Nat.eqb (lvalue_root lhs) r then eval_expr s e else acc | _ => acc end.
Definition lastw (s : State) (r : signal) (sts : list Stmt) (acc : Z) : Z := fold_left (step_w s r) sts acc.

Lemma lastw_cong : forall s r w sts a b, norm w a = norm w b -> norm w (lastw s r sts a) = norm w (lastw s r sts b).
Proof.
 intros s r w sts. induction sts as [|st rest IH]; intros a b H; cbn [lastw fold_left]; [exact H|].
 apply IH. unfold step_w. destruct st; try exact H. destruct (Nat.eqb (lvalue_root lhs) r); [reflexivity|exact H].
Qed.

Lemma lastw_none : forall s r sts acc, existsb (writes_stmtb r) sts = false -> lastw s r sts acc = acc.
Proof.
 intros s r sts. induction sts as [|st rest IH]; intros acc H; [reflexivity|].
 cbn in H. apply orb_false_iff in H as [H1 H2]. cbn [lastw fold_left]. unfold step_w.
 destruct st; try exact (IH _ H2). cbn in H1. rewrite H1. exact (IH _ H2).
Qed.

Definition allw (w : nat) (r : signal) (sts : list Stmt) : Prop :=
 forall st, In st sts -> writes_stmtb r st = true -> exists e, st = SAssign true e (LVar w r).

Lemma apply_lastw : forall s w r sts cur, allw w r sts ->
 norm w (apply_updates_root_value r cur (nba_updates s sts)) = norm w (lastw s r sts cur).
Proof.
 intros s w r sts. induction sts as [|st rest IH]; intros cur HA; [reflexivity|].
 assert (HA' : allw w r rest) by (intros st' Hin Hw; apply HA; [right; exact Hin|exact Hw]).
 destruct st as [|nb e lhs| | |]; cbn [nba_updates lastw fold_left step_w].
 - exact (IH cur HA').
 - cbn [apply_updates_root_value]. unfold apply_update_root_value. rewrite resolve_update_root.
   destruct (Nat.eqb (lvalue_root lhs) r) eqn:Hr.
   + apply Nat.eqb_eq in Hr.
     assert (Hw : writes_stmtb r (SAssign nb e lhs) = true) by (cbn; apply Nat.eqb_eq; exact Hr).
     destruct (HA _ (or_introl eq_refl) Hw) as [e' Heq]. injection Heq as H1 H2 H3. subst nb e'.
     rewrite H3. cbn [resolve_update resolve_lvalue update_signal update_offset update_width update_value].
     rewrite (IH _ HA').
     apply lastw_cong. rewrite norm_full_low_write. rewrite norm_idempotent. reflexivity.
   + rewrite (IH _ HA'). reflexivity.
 - exact (IH cur HA').
 - exact (IH cur HA').
 - exact (IH cur HA').
Qed.

Definition texprd (w : nat) (r : signal) (d : Expr) : Tree -> Expr :=
 fix F (T : Tree) : Expr :=
 match T with
 | TLeaf l => match filter (writes_stmtb r) l with [SAssign _ e _] => e | _ => d end
 | TIf g y n => ECond w g (F y) (F n)
 end.

Lemma lastw_single : forall s r sts acc b e lhs, filter (writes_stmtb r) sts = [SAssign b e lhs] -> lastw s r sts acc = eval_expr s e.
Proof.
 intros s r sts. induction sts as [|st rest IH]; intros acc b e lhs H; cbn [filter] in H; [discriminate|].
 cbn [lastw fold_left]. destruct (writes_stmtb r st) eqn:Hw.
 - injection H as H1 H2. subst st. unfold step_w. cbn in Hw. rewrite Hw.
   fold (lastw s r rest (eval_expr s e)). exact (lastw_none s r rest _ (filter_nil_existsb _ _ _ H2)).
 - unfold step_w at 1. destruct st; cbn in Hw; first [ (rewrite Hw; exact (IH _ _ _ _ H)) | exact (IH _ _ _ _ H) ].
Qed.

Lemma texprd_lastw : forall w r d s T, twf w r T = true ->
 norm w (eval_expr s (texprd w r d T)) = norm w (lastw s r (tleaf s T) (eval_expr s d)).
Proof.
 intros w r d s T. induction T as [l|g y IHy n IHn]; cbn [twf texprd tleaf]; intro H.
 - destruct (leaf_wf_cases w r l H) as [Ef|[e Ef]].
   + rewrite Ef. rewrite (lastw_none s r l _ (filter_nil_existsb _ _ _ Ef)). reflexivity.
   + rewrite Ef. rewrite (lastw_single s r l _ _ _ _ Ef). reflexivity.
 - apply andb_true_iff in H as [Hy Hn]. cbn [eval_expr]. rewrite norm_idempotent.
   destruct (Z.eqb (eval_expr s g) 0); [exact (IHn Hn)|exact (IHy Hy)].
Qed.

Definition items_exprm (w : nat) (r : signal) (Ts : list Tree) : Expr :=
 fold_left (fun d T => if tw r T then texprd w r d T else d) Ts (EVar w r).

Lemma lastw_app : forall s r a b acc, lastw s r (a ++ b) acc = lastw s r b (lastw s r a acc).
Proof. intros. unfold lastw. apply fold_left_app. Qed.

Lemma items_lastw : forall w r s Ts d, forallb (twf w r) Ts = true ->
 norm w (eval_expr s (fold_left (fun d T => if tw r T then texprd w r d T else d) Ts d)) =
 norm w (lastw s r (flat_map (tleaf s) Ts) (eval_expr s d)).
Proof.
 intros w r s Ts. induction Ts as [|T rest IH]; intros d H; cbn [fold_left flat_map forallb] in *; [reflexivity|].
 apply andb_true_iff in H as [Ht Hr].
 rewrite (IH _ Hr). rewrite lastw_app.
 apply lastw_cong. destruct (tw r T) eqn:Htw.
 - exact (texprd_lastw w r d s T Ht).
 - rewrite (lastw_none s r _ _ (tw_false r T s Htw)). reflexivity.
Qed.

Lemma allw_leaf : forall w r l, leaf_wf w r l = true -> allw w r l.
Proof.
 intros w r l H st Hin Hw. destruct (leaf_wf_cases w r l H) as [Ef|[e Ef]].
 - exfalso. assert (In st (filter (writes_stmtb r) l)) by (apply filter_In; split; assumption). rewrite Ef in H0. contradiction.
 - exists e. assert (In st (filter (writes_stmtb r) l)) by (apply filter_In; split; assumption). rewrite Ef in H0.
   destruct H0 as [H0|[]]. symmetry. exact H0.
Qed.

Lemma allw_flat : forall w r s Ts, forallb (twf w r) Ts = true -> allw w r (flat_map (tleaf s) Ts).
Proof.
 intros w r s Ts. induction Ts as [|T rest IH]; intro H; cbn [flat_map forallb] in *.
 - intros st Hin. contradiction.
 - apply andb_true_iff in H as [Ht Hr]. intros st Hin Hw. apply in_app_or in Hin as [Hin|Hin].
   + exact (allw_leaf w r _ (twf_leaf w r s T Ht) st Hin Hw).
   + exact (IH Hr st Hin Hw).
Qed.

Fixpoint texpr2m (w : nat) (r : signal) (T : Tree2) : Expr :=
 match T with
 | T2Cat Ts => items_exprm w r Ts
 | T2If g y n => ECond w g (texpr2m w r y) (texpr2m w r n)
 end.
Fixpoint twf2m (w : nat) (r : signal) (T : Tree2) : bool :=
 match T with
 | T2Cat Ts => forallb (twf w r) Ts
 | T2If _ y n => twf2m w r y && twf2m w r n
 end.

Lemma texpr2m_lastw : forall w r s T, twf2m w r T = true ->
 norm w (eval_expr s (texpr2m w r T)) = norm w (lastw s r (tleaf2 s T) (eval_expr s (EVar w r))) /\ allw w r (tleaf2 s T).
Proof.
 intros w r s T. induction T as [Ts|g y IHy n IHn]; cbn [twf2m texpr2m tleaf2]; intro H.
 - split; [exact (items_lastw w r s Ts (EVar w r) H)|exact (allw_flat w r s Ts H)].
 - apply andb_true_iff in H as [Hy Hn]. cbn [eval_expr]. rewrite norm_idempotent.
   destruct (Z.eqb (eval_expr s g) 0); [exact (IHn Hn)|exact (IHy Hy)].
Qed.

Theorem seq_upd_valuem : forall p ev pre r P sts w,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 process_updates p (phase_driven_state p ev pre) P = nba_updates (phase_driven_state p ev pre) sts ->
 allw w r sts ->
 norm w (read_signal (PhaseSemantics p ev pre) r) = norm w (lastw (phase_driven_state p ev pre) r sts (read_signal (phase_driven_state p ev pre) r)).
Proof.
 intros p ev pre r P sts w HU HE HW HPU HA.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain, selected_on_transition.
 rewrite process_slice_sound.
 rewrite filter_swap, HW. cbn [flat_map]. rewrite app_nil_r.
 rewrite HPU. rewrite (apply_lastw _ w r sts _ HA).
 apply lastw_cong. rewrite (driven_unchanged p ev pre r HU HE). reflexivity.
Qed.

Theorem seq_tree2m_value : forall p ev pre r P t T kf w,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [t]] -> Rel2 kf t T -> (kf + 2 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 twf2m w r T = true ->
 norm w (read_signal (PhaseSemantics p ev pre) r) = norm w (eval_expr (phase_driven_state p ev pre) (texpr2m w r T)).
Proof.
 intros p ev pre r P t T kf w HU HE HB HR HF HW HWF.
 destruct (texpr2m_lastw w r (phase_driven_state p ev pre) T HWF) as [H1 H2].
 rewrite H1.
 rewrite (seq_upd_valuem p ev pre r P _ w HU HE HW (process_updates_tree2 p _ P kf t T HB HR HF) H2).
 apply lastw_cong. cbn [eval_expr]. rewrite norm_idempotent. reflexivity.
Qed.

End ExtendedSVSeqTree2.
