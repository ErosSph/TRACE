(** Extension of ExtendedSVSeqStep to blocks whose other statements are non-blocking assignments or conditionals of
    non-blocking assignments (e.g. an `if (a^b) x <= y` next to the assignment of interest).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
 Lang.ExtendedSVAssignment Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVWordInvariant Lang.ExtendedSVSeqStep.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVAssignment ExtendedSVWordInvariant ExtendedSVSeqStep.
Local Open Scope Z_scope.
Module ExtendedSVSeqStepIf.

Fixpoint nba_shapeb (st : Stmt) : bool :=
 match st with
 | SSkip => true
 | SAssign true _ _ => true
 | SIf _ y n => nba_shapeb y && nba_shapeb n
 | SSeq l => forallb nba_shapeb l
 | _ => false
 end.

Fixpoint depth (st : Stmt) : nat :=
 match st with
 | SSeq l => S (fold_right (fun x m => Nat.max (depth x) m) 0%nat l)
 | SIf _ y n => S (Nat.max (depth y) (depth n))
 | _ => 1%nat
 end.

Fixpoint stmt_ups (s : State) (st : Stmt) : list Update :=
 match st with
 | SAssign _ e lhs => [resolve_update s lhs (eval_expr s e)]
 | SIf g y n => stmt_ups s (if Z.eqb (eval_expr s g) 0 then n else y)
 | SSeq l => (fix go l := match l with [] => [] | x :: r => stmt_ups s x ++ go r end) l
 | _ => []
 end.

Definition block_ups (s : State) (l : list Stmt) : list Update := flat_map (stmt_ups s) l.

Lemma stmt_ups_seq : forall s l, stmt_ups s (SSeq l) = block_ups s l.
Proof. intros s l. unfold block_ups. induction l as [|x r IH]; [reflexivity|cbn; f_equal; exact IH]. Qed.

Lemma depth_le_seq : forall l x, In x l -> (depth x < depth (SSeq l))%nat.
Proof. intros l. induction l as [|y r IH]; intros x H.
 - contradiction.
 - destruct H as [<-|H].
   + cbn. lia.
   + specialize (IH x H). cbn [depth fold_right] in *. lia. Qed.

Lemma exec_shape : forall fuel st es, nba_shapeb st = true -> (depth st <= fuel)%nat ->
 exec_stmt fuel st es = {| blocking_state := blocking_state es;
   pending_nba := pending_nba es ++ stmt_ups (blocking_state es) st;
   emitted_updates := emitted_updates es ++ stmt_ups (blocking_state es) st |}.
Proof.
 induction fuel as [|fuel IH]; intros st es HS HD.
 - destruct st; cbn in HD; lia.
 - destruct st as [|nba e lhs|l|g y n|sc arms]; cbn in HS; try discriminate.
   + cbn. destruct es. cbn. now rewrite !app_nil_r.
   + destruct nba; try discriminate. cbn [exec_stmt stmt_ups]. destruct es; cbn. reflexivity.
   + cbn [exec_stmt]. 
     assert (Hf : forall l0 pn em, (forall x, In x l0 -> nba_shapeb x = true /\ (depth x <= fuel)%nat) ->
       fold_left (fun es' st' => exec_stmt fuel st' es') l0
        {| blocking_state := blocking_state es; pending_nba := pn; emitted_updates := em |} =
       {| blocking_state := blocking_state es; pending_nba := pn ++ block_ups (blocking_state es) l0;
          emitted_updates := em ++ block_ups (blocking_state es) l0 |}).
     { induction l0 as [|x r IHl]; intros pn em Hx; cbn.
       - unfold block_ups; cbn. now rewrite !app_nil_r.
       - destruct (Hx x (or_introl eq_refl)) as [H1 H2].
         rewrite (IH x _ H1 H2). cbn [blocking_state pending_nba emitted_updates].
         rewrite (IHl (pn ++ stmt_ups (blocking_state es) x) (em ++ stmt_ups (blocking_state es) x)
           (fun y Hy => Hx y (or_intror Hy))).
         unfold block_ups. cbn [flat_map]. now rewrite <- !app_assoc. }
     assert (HA : forall x, In x l -> nba_shapeb x = true /\ (depth x <= fuel)%nat).
     { intros x Hx. split; [apply (proj1 (forallb_forall _ _) HS x Hx)|].
       pose proof (depth_le_seq l x Hx). lia. }
     destruct es as [b pn em]. cbn [blocking_state pending_nba emitted_updates] in *.
     rewrite (Hf l pn em HA). cbn [blocking_state]. rewrite stmt_ups_seq. reflexivity.
   + apply andb_true_iff in HS as [H1 H2]. cbn [exec_stmt stmt_ups].
     assert (Hd : forall st', (st' = y \/ st' = n) -> nba_shapeb st' = true -> (depth st' <= fuel)%nat).
     { intros st' [H|H] _; subst st'; cbn in HD; lia. }
     destruct (Z.eqb (eval_expr (blocking_state es) g) 0) eqn:EG.
     * rewrite (IH n es H2 (Hd n (or_intror eq_refl) H2)). reflexivity.
     * rewrite (IH y es H1 (Hd y (or_introl eq_refl) H1)). reflexivity.
Qed.

Lemma process_updates_shape : forall p s proc sts, process_body proc = SSeq sts -> nba_shapeb (SSeq sts) = true ->
 (depth (SSeq sts) <= statement_fuel p)%nat -> process_updates p s proc = block_ups s sts.
Proof.
 intros p s proc sts HB HS HD. unfold process_updates. rewrite HB.
 rewrite (exec_shape _ _ _ HS HD). cbn [emitted_updates blocking_state]. rewrite stmt_ups_seq. reflexivity.
Qed.

Lemma process_updates_shape2 : forall p s proc sts, process_body proc = SSeq [SSeq sts] -> nba_shapeb (SSeq sts) = true ->
 (depth (SSeq [SSeq sts]) <= statement_fuel p)%nat -> process_updates p s proc = block_ups s sts.
Proof.
 intros p s proc sts HB HS HD. unfold process_updates. rewrite HB.
 assert (HS2 : nba_shapeb (SSeq [SSeq sts]) = true) by (cbn in HS |- *; rewrite HS; reflexivity).
 rewrite (exec_shape _ _ _ HS2 HD). cbn [emitted_updates blocking_state]. rewrite stmt_ups_seq.
 unfold block_ups at 1. cbn [flat_map]. rewrite app_nil_r. rewrite stmt_ups_seq. reflexivity.
Qed.

Definition writes_inb (r : signal) (st : Stmt) : bool := existsb (Nat.eqb r) (stmt_writers st).

Lemma stmt_ups_signals : forall st s u, In u (stmt_ups s st) -> In (update_signal u) (stmt_writers st).
Proof.
 fix IH 1. intros st s u H. destruct st as [|nba e lhs|l|g y n|sc arms]; cbn in H.
 - contradiction.
 - destruct H as [<-|[]]. rewrite resolve_update_root. cbn. now left.
 - cbn [stmt_writers]. revert H. induction l as [|x r IHl]; cbn; intro H; [contradiction|].
   apply in_app_or in H as [H|H]; apply in_or_app; [left; exact (IH x s u H)|right; exact (IHl H)].
 - cbn [stmt_writers]. apply in_or_app. destruct (Z.eqb (eval_expr s g) 0).
   + right. exact (IH n s u H).
   + left. exact (IH y s u H).
 - contradiction.
Qed.

Lemma block_ups_avoid : forall s r sts, existsb (writes_inb r) sts = false -> updates_avoid r (block_ups s sts).
Proof.
 intros s r sts. induction sts as [|x rest IH]; intros H u Hin; cbn in *; [contradiction|].
 apply orb_false_iff in H as [H1 H2]. unfold block_ups in Hin. cbn [flat_map] in Hin.
 apply in_app_or in Hin as [Hin|Hin].
 - intro E. pose proof (stmt_ups_signals x s u Hin) as Hw. unfold writes_inb in H1.
   assert (existsb (Nat.eqb r) (stmt_writers x) = true) by (apply existsb_exists; exists (update_signal u); split; [exact Hw|rewrite E; apply Nat.eqb_refl]).
   congruence.
 - exact (IH H2 u Hin).
Qed.

Theorem seq_root_step_if : forall p ev pre r P sts k e w,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq sts] -> nba_shapeb (SSeq sts) = true -> (depth (SSeq [SSeq sts]) <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 nth_error sts k = Some (SAssign true e (LVar w r)) ->
 existsb (writes_inb r) (firstn k sts) = false -> existsb (writes_inb r) (skipn (S k) sts) = false ->
 norm w (read_signal (PhaseSemantics p ev pre) r) = norm w (eval_expr (phase_driven_state p ev pre) e).
Proof.
 intros p ev pre r P sts k e w HU HE HB HS HD HW HK HP HQ.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain, selected_on_transition.
 set (driven := phase_driven_state p ev pre) in *.
 rewrite process_slice_sound. rewrite filter_swap, HW. cbn [flat_map]. rewrite app_nil_r.
 rewrite (process_updates_shape2 p driven P sts HB HS HD).
 pose proof (nth_error_split sts k HK) as [l1 [l2 [Hsplit Hlen]]].
 assert (Hl1 : firstn k sts = l1).
 { rewrite Hsplit, firstn_app. rewrite firstn_all2 by lia. replace (k - length l1)%nat with 0%nat by lia. cbn. now rewrite app_nil_r. }
 assert (Hl2 : skipn (S k) sts = l2).
 { rewrite Hsplit, skipn_app. rewrite skipn_all2 by lia. replace (S k - length l1)%nat with 1%nat by lia. reflexivity. }
 rewrite Hl1 in HP. rewrite Hl2 in HQ.
 rewrite Hsplit. unfold block_ups. rewrite flat_map_app. cbn [flat_map stmt_ups]. 
 rewrite !apply_root_app.
 rewrite (apply_root_avoids r (flat_map (stmt_ups driven) l1) _ (block_ups_avoid driven r l1 HP)).
 cbn [apply_updates_root_value].
 rewrite (apply_root_avoids r (flat_map (stmt_ups driven) l2) _ (block_ups_avoid driven r l2 HQ)).
 unfold apply_update_root_value, resolve_update. cbn [resolve_lvalue update_signal update_offset update_width update_value].
 rewrite Nat.eqb_refl. rewrite norm_full_low_write. apply norm_idempotent.
Qed.
End ExtendedSVSeqStepIf.
Print Assumptions ExtendedSVSeqStepIf.seq_root_step_if.
