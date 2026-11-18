(** Design-independent: value of a register after a clock phase when exactly one selected sequential process
    writes it, by one non-blocking full-width assignment inside a block of non-blocking assignments.
    Used by the template route to turn a process right-hand side into the register's next value.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
 Lang.ExtendedSVAssignment Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVWordInvariant.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVAssignment ExtendedSVWordInvariant.
Local Open Scope Z_scope.
Module ExtendedSVSeqStep.

Definition nba_blockb (sts : list Stmt) : bool :=
 forallb (fun st => match st with SAssign true _ _ => true | _ => false end) sts.

Fixpoint nba_updates (s : State) (sts : list Stmt) : list Update :=
 match sts with
 | [] => []
 | SAssign _ e lhs :: r => resolve_update s lhs (eval_expr s e) :: nba_updates s r
 | _ :: r => nba_updates s r
 end.

Lemma exec_assign_nba : forall f e lhs es,
 exec_stmt (S f) (SAssign true e lhs) es =
 {| blocking_state := blocking_state es;
    pending_nba := pending_nba es ++ [resolve_update (blocking_state es) lhs (eval_expr (blocking_state es) e)];
    emitted_updates := emitted_updates es ++ [resolve_update (blocking_state es) lhs (eval_expr (blocking_state es) e)] |}.
Proof. reflexivity. Qed.

Lemma exec_seq : forall f l es, exec_stmt (S f) (SSeq l) es = fold_left (fun es' st' => exec_stmt f st' es') l es.
Proof. reflexivity. Qed.

Lemma exec_nba_fold : forall sts fuel s pn em, (1 <= fuel)%nat -> nba_blockb sts = true ->
 fold_left (fun es' st' => exec_stmt fuel st' es') sts
  {| blocking_state := s; pending_nba := pn; emitted_updates := em |} =
 {| blocking_state := s; pending_nba := pn ++ nba_updates s sts; emitted_updates := em ++ nba_updates s sts |}.
Proof.
 induction sts as [|st rest IH]; intros fuel s pn em HF HB.
 - cbn. now rewrite !app_nil_r.
 - cbn in HB. apply andb_true_iff in HB as [Hst Hrest].
   destruct st; try discriminate. destruct nonblocking; try discriminate.
   destruct fuel as [|f]; [lia|].
   cbn [fold_left nba_updates]. rewrite exec_assign_nba. cbn [blocking_state pending_nba emitted_updates].
   rewrite IH by (try lia; exact Hrest). now rewrite <- !app_assoc.
Qed.

Lemma process_updates_nba : forall p s proc sts,
 process_body proc = SSeq [SSeq sts] -> nba_blockb sts = true -> (3 <= statement_fuel p)%nat ->
 process_updates p s proc = nba_updates s sts.
Proof.
 intros p s proc sts HB HN HF. unfold process_updates. rewrite HB.
 destruct (statement_fuel p) as [|[|[|f]]]; try lia.
 rewrite exec_seq. cbn [fold_left]. rewrite exec_seq. rewrite exec_nba_fold by (try lia; exact HN).
 cbn [emitted_updates]. reflexivity.
Qed.

Definition writes_stmtb (r : signal) (st : Stmt) : bool :=
 match st with SAssign _ _ lhs => Nat.eqb (lvalue_root lhs) r | _ => false end.

Lemma nba_updates_app : forall s a b, nba_updates s (a ++ b) = nba_updates s a ++ nba_updates s b.
Proof. intros s a. induction a as [|st rest IH]; intros b; cbn; [reflexivity|].
 destruct st; cbn; rewrite ?IH; reflexivity. Qed.

Lemma nba_updates_avoid : forall s r sts, existsb (writes_stmtb r) sts = false ->
 updates_avoid r (nba_updates s sts).
Proof.
 intros s r sts. induction sts as [|st rest IH]; intros H u Hin; cbn in *; [contradiction|].
 apply orb_false_iff in H as [Hst Hrest].
 destruct st; try (eapply IH; eassumption).
 destruct Hin as [<-|Hin].
 - rewrite resolve_update_root. cbn in Hst. intro E. rewrite E in Hst. rewrite Nat.eqb_refl in Hst. discriminate.
 - eapply IH; eassumption.
Qed.

Theorem seq_root_step : forall p ev pre r P sts k e w,
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 process_body P = SSeq [SSeq sts] -> nba_blockb sts = true -> (3 <= statement_fuel p)%nat ->
 filter (process_matches_states pre (phase_driven_state p ev pre)) (filter (writes_rootb r) (processes p)) = [P] ->
 nth_error sts k = Some (SAssign true e (LVar w r)) ->
 existsb (writes_stmtb r) (firstn k sts) = false ->
 existsb (writes_stmtb r) (skipn (S k) sts) = false ->
 norm w (read_signal (PhaseSemantics p ev pre) r) = norm w (eval_expr (phase_driven_state p ev pre) e).
Proof.
 intros p ev pre r P sts k e w HU HE HB HN HF HW HK HP HQ.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain, selected_on_transition.
 set (driven := phase_driven_state p ev pre) in *.
 rewrite process_slice_sound.
 rewrite filter_swap, HW. cbn [flat_map]. rewrite app_nil_r.
 rewrite (process_updates_nba p driven P sts HB HN HF).
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

(** Phases without a clock posedge leave every combinationally unwritten root untouched. *)
Definition posedge_onlyb (p : Program) (clk : signal) : bool :=
 forallb (fun Q => match process_kind Q with
   | Sequential => forallb (fun e => Nat.eqb (event_signal e) clk &&
       match event_edge e with Posedge => true | _ => false end) (process_events Q)
   | _ => true end) (processes p).

Lemma matches_false_no_edge : forall p clk pre driven Q, posedge_onlyb p clk = true -> In Q (processes p) ->
 (Z.eqb (read_signal pre clk) 0 = false \/ Z.eqb (read_signal driven clk) 0 = true) ->
 process_matches_states pre driven Q = false.
Proof.
 intros p clk pre driven Q HP HI HC. unfold posedge_onlyb in HP.
 rewrite forallb_forall in HP. specialize (HP Q HI).
 unfold process_matches_states. destruct (process_kind Q); try reflexivity.
 destruct (existsb (event_spec_matches_states pre driven) (process_events Q)) eqn:E; [|reflexivity].
 apply existsb_exists in E as [e [Hin Hf]].
 rewrite forallb_forall in HP. specialize (HP e Hin). apply andb_true_iff in HP as [Hs He].
 apply Nat.eqb_eq in Hs. destruct (event_edge e) eqn:Ed; try discriminate.
 unfold event_spec_matches_states in Hf. rewrite Ed, Hs in Hf. cbn [edge_fires] in Hf.
 apply andb_true_iff in Hf as [H1 H2]. rewrite negb_true_iff in H2.
 destruct HC as [HC|HC]; congruence.
Qed.

Lemma filter_nil_all : forall (l : list Process) f, (forall x, In x l -> f x = false) -> filter f l = [].
Proof. induction l as [|x r IH]; intros f H; cbn; [reflexivity|].
 rewrite (H x (or_introl eq_refl)). apply IH. intros y Hy. apply H. now right. Qed.

Lemma selected_none : forall p clk pre driven, posedge_onlyb p clk = true ->
 (Z.eqb (read_signal pre clk) 0 = false \/ Z.eqb (read_signal driven clk) 0 = true) ->
 selected_on_transition p pre driven = [].
Proof.
 intros p clk pre driven HP HC. unfold selected_on_transition.
 apply filter_nil_all. intros Q HQ. exact (matches_false_no_edge p clk pre driven Q HP HQ HC).
Qed.

Theorem frame_no_edge : forall p clk ev pre r, posedge_onlyb p clk = true -> comb_root_unwrittenb p clk = true ->
 comb_root_unwrittenb p r = true -> changed_signal ev <> r ->
 (Z.eqb (read_signal pre clk) 0 = false \/
  Z.eqb (read_signal (write_signal pre (changed_signal ev) (new_value ev)) clk) 0 = true) ->
 read_signal (PhaseSemantics p ev pre) r = read_signal pre r.
Proof.
 intros p clk ev pre r HP HCU HRU HE HC.
 rewrite phase_root_projection by assumption.
 unfold phase_update_chain. rewrite (selected_none p clk pre (phase_driven_state p ev pre) HP).
 - reflexivity.
 - destruct HC as [HC|HC]; [now left|right]. unfold phase_driven_state.
   rewrite lfp_candidate_preserves_unwritten_root by exact HCU. exact HC.
Qed.

(** The driven value of the event signal itself (a combinationally unwritten input). *)
Theorem event_signal_value : forall p clk ev pre, posedge_onlyb p clk = true -> comb_root_unwrittenb p clk = true ->
 comb_root_unwrittenb p (changed_signal ev) = true ->
 (Z.eqb (read_signal pre clk) 0 = false \/
  Z.eqb (read_signal (write_signal pre (changed_signal ev) (new_value ev)) clk) 0 = true) ->
 read_signal (PhaseSemantics p ev pre) (changed_signal ev) = new_value ev.
Proof.
 intros p clk ev pre HP HCU HEU HC.
 unfold PhaseSemantics, phase_execute_order, execute_process_order.
 rewrite (selected_none p clk pre (phase_driven_state p ev pre) HP).
 - cbn [flat_map apply_updates]. rewrite lfp_candidate_preserves_unwritten_root by exact HEU.
   unfold phase_driven_state. rewrite lfp_candidate_preserves_unwritten_root by exact HEU.
   apply read_signal_write_same.
 - destruct HC as [HC|HC]; [now left|right]. unfold phase_driven_state.
   rewrite lfp_candidate_preserves_unwritten_root by exact HCU. exact HC.
Qed.

Lemma matches_rise : forall Q pre driven clk, process_kind Q = Sequential ->
 process_events Q = [{| event_edge := Posedge; event_signal := clk |}] ->
 read_signal pre clk = 0 -> read_signal driven clk = 1 -> process_matches_states pre driven Q = true.
Proof.
 intros Q pre driven clk HK HE H0 H1. unfold process_matches_states. rewrite HK, HE.
 cbn [existsb event_spec_matches_states event_signal event_edge edge_fires]. rewrite H0, H1. reflexivity.
Qed.
End ExtendedSVSeqStep.
Print Assumptions ExtendedSVSeqStep.seq_root_step.
