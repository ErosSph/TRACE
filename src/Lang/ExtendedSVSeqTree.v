(** Design-independent: register value after a clock phase when exactly one selected sequential process writes it and the
    process body is a decision tree (nested SIf, leaves = blocks of non-blocking assignments, a single non-blocking
    assignment, or skip). Generalises ExtendedSVSeqStep.seq_root_step (single block) to reset/flush/enable trees.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
 Lang.ExtendedSVAssignment Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVWordInvariant Lang.ExtendedSVSeqStep.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVAssignment ExtendedSVWordInvariant ExtendedSVSeqStep.
Local Open Scope Z_scope.
Module ExtendedSVSeqTree.

Inductive Tree : Type := TLeaf (l : list Stmt) | TIf (g : Expr) (y n : Tree).

Fixpoint tleaf (s : State) (T : Tree) : list Stmt :=
 match T with
 | TLeaf l => l
 | TIf g y n => if Z.eqb (eval_expr s g) 0 then tleaf s n else tleaf s y
 end.

(** Rel k t T: statement t is the decision tree T, and executing t needs fuel k. *)
Inductive Rel : nat -> Stmt -> Tree -> Prop :=
 | RSkip : Rel 1 SSkip (TLeaf [])
 | RAssign : forall e lhs, Rel 1 (SAssign true e lhs) (TLeaf [SAssign true e lhs])
 | RBlock : forall l, nba_blockb l = true -> Rel 2 (SSeq l) (TLeaf l)
 | RIf : forall g y n ky kn Ty Tn, Rel ky y Ty -> Rel kn n Tn -> Rel (S (Nat.max ky kn)) (SIf g y n) (TIf g Ty Tn)
 | RWrap : forall g y n k T, Rel k (SIf g y n) T -> Rel (S k) (SSeq [SIf g y n]) T.

Lemma exec_rel : forall k t T, Rel k t T -> forall f es, (k <= f)%nat ->
 exec_stmt f t es =
 {| blocking_state := blocking_state es;
    pending_nba := pending_nba es ++ nba_updates (blocking_state es) (tleaf (blocking_state es) T);
    emitted_updates := emitted_updates es ++ nba_updates (blocking_state es) (tleaf (blocking_state es) T) |}.
Proof.
 intros k t T HR. induction HR as [|e lhs|l HB|g y n ky kn Ty Tn Hy IHy Hn IHn|g y n k T Hi IHi]; intros f es HD.
 - destruct f as [|f]; [lia|]. cbn [exec_stmt tleaf nba_updates]. destruct es; cbn; rewrite !app_nil_r; reflexivity.
 - destruct f as [|f]; [lia|]. destruct es as [s pn em]. rewrite exec_assign_nba.
   cbn [tleaf nba_updates blocking_state pending_nba emitted_updates]. rewrite ?app_nil_r. reflexivity.
 - destruct f as [|f]; [lia|]. cbn [tleaf]. rewrite exec_seq. destruct es as [s pn em]. cbn [blocking_state pending_nba emitted_updates].
   rewrite exec_nba_fold by (try lia; exact HB). reflexivity.
 - destruct f as [|f]; [lia|].
   cbn [exec_stmt tleaf]. destruct (Z.eqb (eval_expr (blocking_state es) g) 0).
   + apply IHn. lia.
   + apply IHy. lia.
 - destruct f as [|f]; [lia|]. rewrite exec_seq. cbn [fold_left]. apply IHi. lia.
Qed.

Lemma process_updates_tree : forall p s proc k t T,
 process_body proc = SSeq [SSeq [t]] -> Rel k t T -> (k + 2 <= statement_fuel p)%nat ->
 process_updates p s proc = nba_updates s (tleaf s T).
Proof.
 intros p s proc k t T HB HR HF. unfold process_updates. rewrite HB.
 destruct (statement_fuel p) as [|[|f]]; try lia.
 rewrite exec_seq. cbn [fold_left]. rewrite exec_seq. cbn [fold_left].
 rewrite (exec_rel k t T HR f _) by lia. cbn [emitted_updates blocking_state]. reflexivity.
Qed.

(** boolean conversion of a body to a tree, with fuel *)
Definition single_if (l : list Stmt) : option Stmt :=
 match l with
 | [x] => match x with SIf _ _ _ => Some x | _ => None end
 | _ => None
 end.

Lemma single_if_some : forall l x, single_if l = Some x -> exists g y n, l = [SIf g y n] /\ x = SIf g y n.
Proof.
 intros l x H. destruct l as [|a [|b r]]; cbn in H; try discriminate.
 destruct a as [|?|?|g0 y0 n0|? ?]; try discriminate. inversion H; subst. exists g0, y0, n0. split; reflexivity.
Qed.

Fixpoint conv (fuel : nat) (t : Stmt) : option (nat * Tree) :=
 match fuel with
 | O => None
 | S k =>
   match t with
   | SSkip => Some (1%nat, TLeaf [])
   | SAssign true e lhs => Some (1%nat, TLeaf [SAssign true e lhs])
   | SSeq l =>
       match single_if l with
       | Some x => match conv k x with Some (d, T) => Some (S d, T) | None => None end
       | None => if nba_blockb l then Some (2%nat, TLeaf l) else None
       end
   | SIf g y n =>
       match conv k y, conv k n with
       | Some (dy, Ty), Some (dn, Tn) => Some (S (Nat.max dy dn), TIf g Ty Tn)
       | _, _ => None
       end
   | _ => None
   end
 end.

Lemma conv_sound : forall fuel t d T, conv fuel t = Some (d, T) -> Rel d t T.
Proof.
 induction fuel as [|k IH]; intros t d T H; [discriminate|].
 destruct t as [|b e lhs|l|g y n|sc arms]; cbn [conv] in H; try discriminate.
 - inversion H; subst; clear H. constructor.
 - destruct b; try discriminate. inversion H; subst; clear H. constructor.
 - destruct (single_if l) as [x|] eqn:Hs.
   + destruct (single_if_some l x Hs) as [g [y [n [-> ->]]]].
     destruct (conv k (SIf g y n)) as [[d' T']|] eqn:Hc; [|discriminate]. inversion H; subst; clear H.
     constructor. exact (IH _ _ _ Hc).
   + destruct (nba_blockb l) eqn:Hb; [|discriminate]. inversion H; subst; clear H. constructor. exact Hb.
 - destruct (conv k y) as [[dy Ty]|] eqn:Hy; [|discriminate]. destruct (conv k n) as [[dn Tn]|] eqn:Hn; [|discriminate].
   inversion H; subst; clear H. constructor; eapply IH; eassumption.
Qed.

Theorem seq_tree_step : forall p ev pre r P t T kf k e w,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [t]] -> Rel kf t T -> (kf + 2 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 nth_error (tleaf (phase_driven_state p ev pre) T) k = Some (SAssign true e (LVar w r)) ->
 existsb (writes_stmtb r) (firstn k (tleaf (phase_driven_state p ev pre) T)) = false ->
 existsb (writes_stmtb r) (skipn (S k) (tleaf (phase_driven_state p ev pre) T)) = false ->
 norm w (read_signal (PhaseSemantics p ev pre) r) = norm w (eval_expr (phase_driven_state p ev pre) e).
Proof.
 intros p ev pre r P t T kf k e w HU HE HB HR HF HW HK HP HQ.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain, selected_on_transition.
 set (driven := phase_driven_state p ev pre) in *.
 rewrite process_slice_sound.
 rewrite filter_swap, HW. cbn [flat_map]. rewrite app_nil_r.
 rewrite (process_updates_tree p driven P kf t T HB HR HF).
 set (sts := tleaf driven T) in *.
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

(** hold: the selected leaf does not write r, so the root keeps its previous value *)
Theorem seq_tree_hold : forall p ev pre r P t T kf,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [t]] -> Rel kf t T -> (kf + 2 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 existsb (writes_stmtb r) (tleaf (phase_driven_state p ev pre) T) = false ->
 read_signal (PhaseSemantics p ev pre) r = read_signal pre r.
Proof.
 intros p ev pre r P t T kf HU HE HB HR HF HW HX.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain, selected_on_transition.
 set (driven := phase_driven_state p ev pre) in *.
 rewrite process_slice_sound.
 rewrite filter_swap, HW. cbn [flat_map]. rewrite app_nil_r.
 rewrite (process_updates_tree p driven P kf t T HB HR HF).
 rewrite apply_root_avoids by (apply nba_updates_avoid; exact HX).
 reflexivity.
Qed.

Lemma driven_unchanged : forall p ev pre r, comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 read_signal (phase_driven_state p ev pre) r = read_signal pre r.
Proof.
 intros p ev pre r HU HE. unfold phase_driven_state. rewrite lfp_candidate_preserves_unwritten_root by exact HU.
 apply read_signal_write_other. congruence.
Qed.

(** ---- value form: the register's next value as one expression over the driven state ---- *)
Definition leaf_expr (w : nat) (r : signal) (l : list Stmt) : Expr :=
 match filter (writes_stmtb r) l with
 | [SAssign _ e _] => e
 | _ => EVar w r
 end.

Fixpoint texpr (w : nat) (r : signal) (T : Tree) : Expr :=
 match T with
 | TLeaf l => leaf_expr w r l
 | TIf g y n => ECond w g (texpr w r y) (texpr w r n)
 end.

Definition leaf_wf (w : nat) (r : signal) (l : list Stmt) : bool :=
 match filter (writes_stmtb r) l with
 | [] => true
 | [SAssign true _ (LVar w' r')] => Nat.eqb w' w && Nat.eqb r' r
 | _ => false
 end.

Fixpoint twf (w : nat) (r : signal) (T : Tree) : bool :=
 match T with
 | TLeaf l => leaf_wf w r l
 | TIf _ y n => twf w r y && twf w r n
 end.

Lemma texpr_leaf : forall w r s T, norm w (eval_expr s (texpr w r T)) = norm w (eval_expr s (leaf_expr w r (tleaf s T))).
Proof.
 intros w r s T. induction T as [l|g y IHy n IHn]; cbn [texpr tleaf]; [reflexivity|].
 cbn [eval_expr]. rewrite norm_idempotent. destruct (Z.eqb (eval_expr s g) 0); [exact IHn|exact IHy].
Qed.

Lemma twf_leaf : forall w r s T, twf w r T = true -> leaf_wf w r (tleaf s T) = true.
Proof.
 intros w r s T. induction T as [l|g y IHy n IHn]; cbn [twf tleaf]; intro H; [exact H|].
 apply andb_true_iff in H as [Hy Hn]. destruct (Z.eqb (eval_expr s g) 0); [exact (IHn Hn)|exact (IHy Hy)].
Qed.

Lemma filter_nil_existsb : forall (A : Type) (f : A -> bool) (l : list A), filter f l = [] -> existsb f l = false.
Proof.
 intros A f l. induction l as [|a l IH]; intro H; [reflexivity|]. cbn [filter] in H. cbn [existsb].
 destruct (f a); [discriminate|]. exact (IH H).
Qed.

Lemma filter_single_split : forall (A : Type) (f : A -> bool) (l : list A) (x : A), filter f l = [x] ->
 exists k, nth_error l k = Some x /\ existsb f (firstn k l) = false /\ existsb f (skipn (S k) l) = false.
Proof.
 intros A f l. induction l as [|a l IH]; intros x H; cbn [filter] in H; [discriminate|].
 destruct (f a) eqn:Fa.
 - injection H as H1 H2. subst a. exists 0%nat. cbn. repeat split. exact (filter_nil_existsb A f l H2).
 - destruct (IH x H) as [k [H1 [H2 H3]]]. exists (S k). cbn. rewrite Fa. cbn. repeat split; assumption.
Qed.

Lemma leaf_wf_cases : forall w r l, leaf_wf w r l = true ->
 filter (writes_stmtb r) l = [] \/ exists e, filter (writes_stmtb r) l = [SAssign true e (LVar w r)].
Proof.
 intros w r l H. unfold leaf_wf in H.
 destruct (filter (writes_stmtb r) l) as [|st rest] eqn:Ef; [left; reflexivity|].
 destruct st as [|nb e lhs| |  |]; try (cbn in H; discriminate).
 destruct nb; try (cbn in H; discriminate).
 destruct lhs as [w' r'|? ? ?]; try (cbn in H; discriminate).
 destruct rest; [|cbn in H; discriminate].
 cbn in H. apply andb_true_iff in H as [Hw Hr]. apply Nat.eqb_eq in Hw. apply Nat.eqb_eq in Hr. subst w' r'.
 right. exists e. reflexivity.
Qed.

Theorem seq_tree_value : forall p ev pre r P t T kf w,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq [t]] -> Rel kf t T -> (kf + 2 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 twf w r T = true ->
 norm w (read_signal (PhaseSemantics p ev pre) r) = norm w (eval_expr (phase_driven_state p ev pre) (texpr w r T)).
Proof.
 intros p ev pre r P t T kf w HU HE HB HR HF HW HWF.
 rewrite texpr_leaf.
 destruct (leaf_wf_cases w r _ (twf_leaf w r (phase_driven_state p ev pre) T HWF)) as [Ef|[e Ef]].
 - unfold leaf_expr. rewrite Ef.
   rewrite (seq_tree_hold p ev pre r P t T kf HU HE HB HR HF HW (filter_nil_existsb _ _ _ Ef)).
   cbn [eval_expr]. rewrite (driven_unchanged p ev pre r HU HE). try rewrite norm_idempotent; try reflexivity.
 - unfold leaf_expr. rewrite Ef.
   destruct (filter_single_split _ _ _ _ Ef) as [k [Hk [Hp Hq]]].
   exact (seq_tree_step p ev pre r P t T kf k e w HU HE HB HR HF HW Hk Hp Hq).
Qed.

(** frame: no selected process writes r *)
Theorem seq_frame : forall p ev pre r,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [] ->
 read_signal (PhaseSemantics p ev pre) r = read_signal pre r.
Proof.
 intros p ev pre r HU HE HW.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain, selected_on_transition.
 set (driven := phase_driven_state p ev pre) in *.
 rewrite process_slice_sound.
 rewrite filter_swap, HW. reflexivity.
Qed.
End ExtendedSVSeqTree.
Print Assumptions ExtendedSVSeqTree.driven_unchanged.
Print Assumptions ExtendedSVSeqTree.conv_sound.
Print Assumptions ExtendedSVSeqTree.seq_tree_step.
Print Assumptions ExtendedSVSeqTree.seq_tree_hold.
Print Assumptions ExtendedSVSeqTree.seq_tree_value.
Print Assumptions ExtendedSVSeqTree.seq_frame.
