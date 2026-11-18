(** Req40: projection-specific execution of the real CV32E40P scheduler.

    The full 1,800-signal post-state is never materialised.  Static writer
    certificates reduce each physical cycle to the exact rising/falling
    update chains for the stateful RF and PC roots. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection.
Require Import Ex.Generated.CV32E40PExtendedAST.
Require Import Ex.External.CV32E40PReq39Trace.
Import ListNotations.
Import ExtendedSV ExtendedSVRootProjection CV32E40PExtendedAST.
Import CV32E40PReq39Trace.
Local Open Scope Z_scope.

Module CV32E40PReq40RootProjection.

  Definition rf_root : signal := 902%nat.
  Definition stateful_pc_root : signal := architectural_pc_signal.

  Theorem rf_comb_unwritten :
      comb_root_unwrittenb cv32e40p_program rf_root = true.
  Proof. vm_compute. reflexivity. Qed.

  Theorem stateful_pc_comb_unwritten :
      comb_root_unwrittenb cv32e40p_program stateful_pc_root = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma drive_preserves_root : forall writes s root,
      Forall (fun xv => fst xv <> root) writes ->
      read_signal (drive s writes) root = read_signal s root.
  Proof.
    induction writes as [|[x v] rest IH]; intros s root Hall; cbn; auto.
    inversion Hall as [|? ? Hx Hrest]; subst.
    change (read_signal (drive (write_signal s x v) rest) root =
      read_signal s root).
    rewrite IH by exact Hrest.
    apply read_signal_write_other. exact Hx.
  Qed.

  Definition full_cycle_root_value (root : signal)
      (image : InstructionImage) (s : TraceState) : Z :=
    let environment := environment_state_image image s in
    let rising := rising_state_image image s in
    apply_updates_root_value root
      (apply_updates_root_value root (read_signal environment root)
        (phase_update_chain cv32e40p_program clk_rise environment))
      (phase_update_chain cv32e40p_program clk_fall rising).

  Record CyclePhaseContext : Type := {
    context_environment : State;
    context_rising : State
  }.

  Definition build_cycle_phase_context (image : InstructionImage)
      (s : TraceState) : CyclePhaseContext :=
    let environment := environment_state_image image s in
    let rising := PhaseSemantics cv32e40p_program clk_rise environment in
    {| context_environment := environment;
       context_rising := rising |}.

  Lemma built_context_environment : forall image s,
      context_environment (build_cycle_phase_context image s) =
        environment_state_image image s.
  Proof.
    intros. unfold build_cycle_phase_context. reflexivity.
  Qed.

  Definition context_root_value (root : signal)
      (context : CyclePhaseContext) : Z :=
    apply_updates_root_value root
      (apply_updates_root_value root
        (read_signal context.(context_environment) root)
        (phase_update_chain cv32e40p_program clk_rise
          context.(context_environment)))
      (phase_update_chain cv32e40p_program clk_fall
        context.(context_rising)).

  Lemma built_context_root_value : forall root image s,
      context_root_value root (build_cycle_phase_context image s) =
        full_cycle_root_value root image s.
  Proof.
    intros. unfold context_root_value, build_cycle_phase_context,
      full_cycle_root_value, rising_state_image. reflexivity.
  Qed.

  (** Materialise a successor only when a later cycle genuinely needs its
      microstate.  The already evaluated environment/rising prefix is reused
      rather than executed again. *)
  Definition successor_from_context (image : InstructionImage)
      (s : TraceState) (context : CyclePhaseContext) : TraceState :=
    let environment := context.(context_environment) in
    let rising := context.(context_rising) in
    let falling := PhaseSemantics cv32e40p_program clk_fall rising in
    let settled := lfp_candidate cv32e40p_program falling in
    let accepted_data := capture_data_request environment in
    {| trace_rtl := settled;
       trace_instruction_pending :=
         if Z.eqb (read_signal environment 16%nat) 0 then None
         else Some (read_signal environment 19%nat);
       trace_data_pending := accepted_data;
       trace_memory_word :=
         match accepted_data with
         | Some request => memory_store_word s.(trace_memory_word) request
         | None => s.(trace_memory_word)
         end |}.

  Lemma built_context_successor : forall image s,
      successor_from_context image s (build_cycle_phase_context image s) =
        full_cycle_image image s.
  Proof.
    intros. unfold successor_from_context, build_cycle_phase_context,
      full_cycle_image, settled_state_image, falling_state_image,
      rising_state_image. reflexivity.
  Qed.

  (** Fully shared scheduler context.  Unlike [CyclePhaseContext], this also
      exposes the internal driven state and item update list produced by each
      phase, so projection evaluation never calls [phase_update_chain] a
      second time. *)
  Record SharedCycleContext : Type := {
    shared_environment : State;
    shared_rise_context : PhaseExecutionContext;
    shared_fall_context : PhaseExecutionContext;
    shared_settled : State
  }.

  Definition build_shared_cycle_context (image : InstructionImage)
      (s : TraceState) : SharedCycleContext :=
    let environment := environment_state_image image s in
    let rise_context :=
      build_phase_execution_context cv32e40p_program clk_rise environment in
    let rising := phase_context_post rise_context in
    let fall_context :=
      build_phase_execution_context cv32e40p_program clk_fall rising in
    let falling := phase_context_post fall_context in
    let settled := lfp_candidate cv32e40p_program falling in
    {| shared_environment := environment;
       shared_rise_context := rise_context;
       shared_fall_context := fall_context;
       shared_settled := settled |}.

  Definition shared_context_root_value (root : signal)
      (context : SharedCycleContext) : Z :=
    phase_execution_root_value root context.(shared_fall_context).

  Definition successor_from_shared_context (image : InstructionImage)
      (s : TraceState) (context : SharedCycleContext) : TraceState :=
    let environment := context.(shared_environment) in
    let accepted_data := capture_data_request environment in
    {| trace_rtl := context.(shared_settled);
       trace_instruction_pending :=
         if Z.eqb (read_signal environment 16%nat) 0 then None
         else Some (read_signal environment 19%nat);
       trace_data_pending := accepted_data;
       trace_memory_word :=
         match accepted_data with
         | Some request => memory_store_word s.(trace_memory_word) request
         | None => s.(trace_memory_word)
         end |}.

  Lemma built_shared_context_environment : forall image s,
      shared_environment (build_shared_cycle_context image s) =
        environment_state_image image s.
  Proof.
    intros. unfold build_shared_cycle_context. reflexivity.
  Qed.

  Lemma built_shared_context_successor : forall image s,
      successor_from_shared_context image s
        (build_shared_cycle_context image s) = full_cycle_image image s.
  Proof.
    intros. unfold successor_from_shared_context, build_shared_cycle_context,
      build_phase_execution_context, full_cycle_image, settled_state_image,
      falling_state_image, rising_state_image, PhaseSemantics,
      phase_execute_order, execute_process_order. reflexivity.
  Qed.

  Theorem built_shared_context_root_projection : forall root image s,
      comb_root_unwrittenb cv32e40p_program root = true ->
      read_signal (trace_rtl (full_cycle_image image s)) root =
        shared_context_root_value root
          (build_shared_cycle_context image s).
  Proof.
    intros root image s Hunwritten.
    rewrite <- built_shared_context_successor.
    unfold successor_from_shared_context, shared_context_root_value.
    unfold build_shared_cycle_context.
    cbn [trace_rtl shared_settled shared_fall_context].
    rewrite lfp_candidate_preserves_unwritten_root by exact Hunwritten.
    apply built_phase_context_root_projection. exact Hunwritten.
  Qed.

  Theorem full_cycle_root_projection : forall root image s,
      comb_root_unwrittenb cv32e40p_program root = true ->
      root <> 7%nat ->
      read_signal (trace_rtl (full_cycle_image image s)) root =
        full_cycle_root_value root image s.
  Proof.
    intros root image s Hunwritten Hroot.
    unfold full_cycle_root_value.
    unfold full_cycle_image. cbn [trace_rtl].
    unfold settled_state_image.
    rewrite lfp_candidate_preserves_unwritten_root by exact Hunwritten.
    unfold falling_state_image.
    rewrite phase_root_projection by (try exact Hunwritten; cbn; congruence).
    unfold rising_state_image.
    rewrite phase_root_projection by (try exact Hunwritten; cbn; congruence).
    reflexivity.
  Qed.

  Corollary full_cycle_rf_projection : forall image s,
      read_signal (trace_rtl (full_cycle_image image s)) rf_root =
        full_cycle_root_value rf_root image s.
  Proof.
    intros. apply full_cycle_root_projection;
      [exact rf_comb_unwritten|discriminate].
  Qed.

  Corollary full_cycle_stateful_pc_projection : forall image s,
      read_signal (trace_rtl (full_cycle_image image s)) stateful_pc_root =
        full_cycle_root_value stateful_pc_root image s.
  Proof.
    intros. apply full_cycle_root_projection;
      [exact stateful_pc_comb_unwritten|discriminate].
  Qed.

End CV32E40PReq40RootProjection.
