(** Structural root-projection theorems for the executable ExtendedSV
    semantics.

    These results avoid evaluating a full CPU state.  A Boolean writer-set
    check is reflected once into a theorem saying that a signal root is
    preserved by every combinational process and therefore by the complete
    LFP computation. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV.
Import ListNotations.
Import ExtendedSV.

Module ExtendedSVRootProjection.

  Definition updates_avoid (root : signal) (updates : list Update) : Prop :=
    forall update, In update updates -> update_signal update <> root.

  Lemma resolve_lvalue_root : forall s lv,
      let '(id, _, _) := resolve_lvalue s lv in id = lvalue_root lv.
  Proof.
    intros s lv. induction lv; cbn; auto.
    destruct (resolve_lvalue s lv) as [[id offset] resolved_width] eqn:E.
    cbn in *. exact IHlv.
  Qed.

  Lemma resolve_update_root : forall s lv value,
      update_signal (resolve_update s lv value) = lvalue_root lv.
  Proof.
    intros. unfold resolve_update.
    pose proof (resolve_lvalue_root s lv) as H.
    destruct (resolve_lvalue s lv) as [[id offset] resolved_width].
    cbn in *. exact H.
  Qed.

  Lemma read_signal_apply_update_other : forall s update root,
      update_signal update <> root ->
      read_signal (apply_update s update) root = read_signal s root.
  Proof.
    intros s [id offset width value] root Hneq. cbn in Hneq.
    unfold apply_update. cbn.
    apply read_signal_write_other. exact Hneq.
  Qed.

  Lemma apply_nba_preserves_root : forall updates s root,
      updates_avoid root updates ->
      read_signal (apply_nba s updates) root = read_signal s root.
  Proof.
    induction updates as [|u us IH]; intros s root Havoid; cbn; auto.
    rewrite IH.
    - apply read_signal_apply_update_other. apply Havoid. left. reflexivity.
    - intros v Hv. apply Havoid. right. exact Hv.
  Qed.

  Definition ExecRootExtension (root : signal)
      (before after : ExecState) : Prop :=
    read_signal after.(blocking_state) root =
      read_signal before.(blocking_state) root /\
    forall update, In update after.(pending_nba) ->
      In update before.(pending_nba) \/ update_signal update <> root.

  Lemma exec_root_extension_refl : forall root es,
      ExecRootExtension root es es.
  Proof. intros root es. split; auto. Qed.

  Lemma exec_root_extension_trans : forall root first middle last,
      ExecRootExtension root first middle ->
      ExecRootExtension root middle last ->
      ExecRootExtension root first last.
  Proof.
    intros root first middle last [Hfm Pm] [Hml Pl]. split.
    - now rewrite Hml, Hfm.
    - intros update Hin. destruct (Pl update Hin) as [Hmid|Hother].
      + destruct (Pm update Hmid) as [Hfirst|Hother']; auto.
      + right. exact Hother.
  Qed.

  Lemma select_case_writers : forall s value arms default root,
      In root (stmt_writers (select_case_stmt s value arms default)) ->
      In root (stmt_writers default ++
        flat_map (fun arm => stmt_writers (snd arm)) arms).
  Proof.
    intros s value arms. induction arms as [|[key body] rest IH];
      intros default root Hin; cbn in *.
    - now apply in_or_app; left.
    - destruct key as [key|].
      + destruct (Z.eqb value (eval_expr s key)) eqn:E.
        * apply in_or_app. right. apply in_or_app. left. exact Hin.
        * apply IH in Hin. apply in_app_or in Hin as [Hdefault|Hrest].
          -- apply in_or_app. left. exact Hdefault.
          -- apply in_or_app. right. apply in_or_app. right. exact Hrest.
      + apply IH in Hin. apply in_app_or in Hin as [Hbody|Hrest].
        * apply in_or_app. right. apply in_or_app. left. exact Hbody.
        * apply in_or_app. right. apply in_or_app. right. exact Hrest.
  Qed.

  Lemma exec_stmt_preserves_unwritten_root : forall fuel st root es,
      ~ In root (stmt_writers st) ->
      ExecRootExtension root es (exec_stmt fuel st es).
  Proof.
    induction fuel as [|fuel IH]; intros st root es Hnone; cbn.
    - apply exec_root_extension_refl.
    - destruct st as [|nba rhs lhs|statements|guard yes no|scrutinee arms].
      + apply exec_root_extension_refl.
      + cbn in Hnone.
        assert (Hroot : lvalue_root lhs <> root)
          by (intro E; apply Hnone; now left).
        destruct nba.
        * split; [reflexivity|].
          intros update Hin. apply in_app_or in Hin as [Hin|Hin]; auto.
          cbn in Hin. destruct Hin as [<-|[]]. right.
          rewrite resolve_update_root. exact Hroot.
        * split.
          -- apply read_signal_apply_update_other.
             rewrite resolve_update_root. exact Hroot.
          -- auto.
      + cbn in Hnone.
        assert (Hall : forall statement, In statement statements ->
            ~ In root (stmt_writers statement)).
        { intros statement Hin Hwriter. apply Hnone.
          apply in_flat_map. exists statement. auto. }
        clear Hnone.
        induction statements as [|statement rest IHr] in es, Hall |- *; cbn.
        * apply exec_root_extension_refl.
        * eapply exec_root_extension_trans.
          -- apply IH. apply Hall. left. reflexivity.
          -- apply IHr. intros st Hin. apply Hall. right. exact Hin.
      + cbn in Hnone.
        destruct (Z.eqb (eval_expr (blocking_state es) guard) 0) eqn:E.
        * apply IH. intro Hin. apply Hnone. apply in_or_app. right. exact Hin.
        * apply IH. intro Hin. apply Hnone. apply in_or_app. left. exact Hin.
      + cbn in Hnone.
        apply IH. intro Hin. apply Hnone.
        apply (select_case_writers _ _ _ _ _ Hin).
  Qed.

  Lemma run_process_preserves_unwritten_root : forall p proc root s,
      ~ In root (process_writers proc) ->
      read_signal (run_process p s proc) root = read_signal s root.
  Proof.
    intros p proc root s Hnone.
    unfold run_process.
    pose proof (exec_stmt_preserves_unwritten_root
      (statement_fuel p) (process_body proc) root
      {| blocking_state := s; pending_nba := []; emitted_updates := [] |}
      Hnone) as [Hblocking Hpending].
    rewrite apply_nba_preserves_root.
    - exact Hblocking.
    - intros update Hin. destruct (Hpending update Hin) as [Hnil|Hother].
      + contradiction.
      + exact Hother.
  Qed.

  Definition comb_root_unwrittenb (p : Program) (root : signal) : bool :=
    forallb (fun proc =>
      negb (existsb (Nat.eqb root) (process_writers proc)))
      (filter is_comb p.(processes)).

  Lemma comb_root_unwrittenb_sound : forall p root,
      comb_root_unwrittenb p root = true ->
      forall proc, In proc (filter is_comb p.(processes)) ->
        ~ In root (process_writers proc).
  Proof.
    intros p root H proc Hin Hwriter.
    unfold comb_root_unwrittenb in H.
    apply forallb_forall with (x := proc) in H; auto.
    apply Bool.negb_true_iff in H.
    assert (Hexists : existsb (Nat.eqb root) (process_writers proc) = true).
    { apply existsb_exists. exists root. split; [exact Hwriter|].
      apply Nat.eqb_refl. }
    now rewrite H in Hexists.
  Qed.

  Lemma fold_run_process_preserves_root : forall p processes root s,
      (forall proc, In proc processes -> ~ In root (process_writers proc)) ->
      read_signal (fold_left (run_process p) processes s) root =
        read_signal s root.
  Proof.
    intros p processes. induction processes as [|proc rest IH];
      intros root s Hall; cbn; auto.
    rewrite IH.
    - apply run_process_preserves_unwritten_root. apply Hall. left. reflexivity.
    - intros next Hin. apply Hall. right. exact Hin.
  Qed.

  Theorem comb_round_preserves_unwritten_root : forall p root,
      comb_root_unwrittenb p root = true -> forall s,
      read_signal (comb_round p s) root = read_signal s root.
  Proof.
    intros p root H s. unfold comb_round.
    apply fold_run_process_preserves_root.
    now apply comb_root_unwrittenb_sound.
  Qed.

  Lemma comb_iter_preserves_unwritten_root : forall p root,
      comb_root_unwrittenb p root = true -> forall fuel s,
      read_signal (comb_iter p fuel s) root = read_signal s root.
  Proof.
    intros p root H fuel. induction fuel as [|fuel IH]; intros s; cbn; auto.
    rewrite IH. now apply comb_round_preserves_unwritten_root.
  Qed.

  Theorem lfp_candidate_preserves_unwritten_root : forall p root,
      comb_root_unwrittenb p root = true -> forall s,
      read_signal (lfp_candidate p s) root = read_signal s root.
  Proof.
    intros p root H s. unfold lfp_candidate.
    now apply comb_iter_preserves_unwritten_root.
  Qed.

  (** Execute an update chain directly on one root value.  Updates to other
      roots disappear definitionally, while updates to the selected root
      retain their exact slice offset, width and value. *)
  Definition apply_update_root_value (root : signal) (current : Z)
      (update : Update) : Z :=
    if Nat.eqb update.(update_signal) root
    then write_slice current update.(update_offset)
           (Z.of_nat update.(update_width)) update.(update_value)
    else current.

  Fixpoint apply_updates_root_value (root : signal) (current : Z)
      (updates : list Update) : Z :=
    match updates with
    | [] => current
    | update :: rest =>
        apply_updates_root_value root
          (apply_update_root_value root current update) rest
    end.

  Lemma read_signal_apply_update : forall s update root,
      read_signal (apply_update s update) root =
        apply_update_root_value root (read_signal s root) update.
  Proof.
    intros s [id offset width value] root.
    unfold apply_update_root_value, apply_update. cbn.
    destruct (Nat.eqb id root) eqn:Heq.
    - apply Nat.eqb_eq in Heq. subst id.
      now rewrite read_signal_write_same.
    - apply Nat.eqb_neq in Heq.
      now rewrite read_signal_write_other by exact Heq.
  Qed.

  Theorem read_signal_apply_updates : forall updates s root,
      read_signal (apply_updates s updates) root =
        apply_updates_root_value root (read_signal s root) updates.
  Proof.
    induction updates as [|update rest IH]; intros s root; cbn; auto.
    rewrite IH, read_signal_apply_update. reflexivity.
  Qed.

  Definition phase_update_chain (p : Program) (ev : Event) (pre : State)
      : list Update :=
    let driven := phase_driven_state p ev pre in
    flat_map (process_updates p driven)
      (selected_on_transition p pre driven).

  (** Projection-specific phase semantics.  Once the static writer check says
      combinational logic cannot write [root], the complete post-LFP is
      replaced by the exact sequential update chain for that root.  This is
      the generic bridge used by CPU-specific pipeline invariants. *)
  Theorem phase_root_projection : forall p ev pre root,
      comb_root_unwrittenb p root = true ->
      ev.(changed_signal) <> root ->
      read_signal (PhaseSemantics p ev pre) root =
        apply_updates_root_value root (read_signal pre root)
          (phase_update_chain p ev pre).
  Proof.
    intros p ev pre root Hunwritten Hevent.
    unfold PhaseSemantics, phase_execute_order, execute_process_order,
      phase_update_chain.
    set (driven := phase_driven_state p ev pre).
    rewrite lfp_candidate_preserves_unwritten_root by exact Hunwritten.
    rewrite read_signal_apply_updates.
    f_equal.
    unfold driven, phase_driven_state.
    rewrite lfp_candidate_preserves_unwritten_root by exact Hunwritten.
    now rewrite read_signal_write_other by exact Hevent.
  Qed.

  (** A shareable item-level certificate for one physical phase.  The driven
      LFP, selected update chain, sequential state and post LFP are each
      bound once.  Projection clients inspect [phase_context_updates] rather
      than re-running [PhaseSemantics] for every field. *)
  Record PhaseExecutionContext : Type := {
    phase_context_driven : State;
    phase_context_updates : list Update;
    phase_context_sequential : State;
    phase_context_post : State
  }.

  Definition build_phase_execution_context
      (p : Program) (ev : Event) (pre : State) : PhaseExecutionContext :=
    let driven := phase_driven_state p ev pre in
    let updates := flat_map (process_updates p driven)
      (selected_on_transition p pre driven) in
    let sequential := apply_updates driven updates in
    let post := lfp_candidate p sequential in
    {| phase_context_driven := driven;
       phase_context_updates := updates;
       phase_context_sequential := sequential;
       phase_context_post := post |}.

  Definition phase_execution_root_value (root : signal)
      (context : PhaseExecutionContext) : Z :=
    apply_updates_root_value root
      (read_signal context.(phase_context_driven) root)
      context.(phase_context_updates).

  Lemma built_phase_context_post : forall p ev pre,
      phase_context_post (build_phase_execution_context p ev pre) =
        PhaseSemantics p ev pre.
  Proof.
    intros. unfold build_phase_execution_context, PhaseSemantics,
      phase_execute_order, execute_process_order. reflexivity.
  Qed.

  Theorem built_phase_context_root_projection : forall p ev pre root,
      comb_root_unwrittenb p root = true ->
      read_signal
        (phase_context_post (build_phase_execution_context p ev pre)) root =
      phase_execution_root_value root
        (build_phase_execution_context p ev pre).
  Proof.
    intros p ev pre root Hunwritten.
    unfold build_phase_execution_context, phase_execution_root_value.
    cbn [phase_context_post phase_context_driven phase_context_updates].
    rewrite lfp_candidate_preserves_unwritten_root by exact Hunwritten.
    now rewrite read_signal_apply_updates.
  Qed.

End ExtendedSVRootProjection.
