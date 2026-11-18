(**
    Three-phase, event-aware hierarchy for the repaired Bzeeno RV32I core.

    [Semantics.v] remains the paper artifact's synchronous semantics.  This
    file is an opt-in scheduler layered at module boundaries.  It selects a
    child MTrs for each physical event: asynchronous reset assertion,
    rising top-level clock, or falling top-level clock.  The closed [cpu]
    hierarchy is then rebuilt through that selected registry, so an inactive
    sequential child cannot update merely because its parent is evaluated.
 *)
Require Import Coq.Lists.List.
Require Import Lib.Lib.
Require Import Lang.Lang.
Require Import Ex.External.BzeenoPipeline Ex.External.BzeenoControl.
Require Import Ex.External.BzeenoCore Ex.External.BzeenoFullCore.
Require Import Ex.External.BzeenoCPU Ex.External.BzeenoTopState.

#[local] Existing Instance bzeeno_vid_t_c.
#[local] Existing Instance bzeeno_vid_ops.
#[local] Existing Instance BzeenoTopState.inputs_structured.
#[local] Existing Instance BzeenoTopState.flops_structured.
#[local] Existing Instance BzeenoPipeline.DataMem.flops_structured.
#[local] Existing Instance BzeenoPipeline.InstructionMem.flops_structured.

Module BzeenoEventMTrs.
  (** The only three events that can change Bzeeno's sequential state.
      Reset deassertion is intentionally absent: it is not in any RTL
      sensitivity list. *)
  Inductive Phase := ResetFall | ClockRise | ClockFall.

  Section Scheduler.
    Context `{sz_ops} `{array_ops hmap}.

    (** A suspended clocked child retains its current flop state.  Its
        ordinary transfer is still evaluated for its output projection; this
        preserves the current registered output while discarding the proposed
        state update.  The Bzeeno sequential blocks use nonblocking updates,
        so this is the required inactive-process behavior. *)
    Definition suspended_mtrs (m : MTrs) : MTrs :=
      {| mtrs_input_vids := m.(mtrs_input_vids);
         mtrs_output_vids := m.(mtrs_output_vids);
         mtrs_func := fun ins flops =>
           (HMapEmpty, snd (m.(mtrs_func) ins flops)) |}.

    Definition async_pipeline_mtrs (p : Phase) (m : MTrs) : MTrs :=
      match p with
      | ResetFall | ClockRise => m
      | ClockFall => suspended_mtrs m
      end.

    (** The source connects the register-file clock to [~i_clk].  Therefore
        its local positive edge is the top-level falling edge.  It also has
        an asynchronous active-low reset. *)
    Definition regfile_mtrs (p : Phase) (m : MTrs) : MTrs :=
      match p with
      | ResetFall | ClockFall => m
      | ClockRise => suspended_mtrs m
      end.

    (** The byte-addressed data memory is a rising-edge-only process and has
        no reset branch in the RTL. *)
    Definition dmem_mtrs (p : Phase) (m : MTrs) : MTrs :=
      match p with
      | ClockRise => m
      | ResetFall | ClockFall => suspended_mtrs m
      end.

    (** The fundamental phase invariant: a child that is not sensitive to
        the current event cannot change its local state. *)
    Lemma suspended_mtrs_keeps_state (m : MTrs) ins flops :
      trsT (suspended_mtrs m).(mtrs_func) ins flops =
      (flops, snd (m.(mtrs_func) ins flops)).
    Proof.
      unfold suspended_mtrs, trsT, trsNext. simpl.
      rewrite hupds_empty. reflexivity.
    Qed.

    Lemma pipeline_keeps_state_at_fall (m : MTrs) ins flops :
      trsT (async_pipeline_mtrs ClockFall m).(mtrs_func) ins flops =
      (flops, snd (m.(mtrs_func) ins flops)).
    Proof. apply suspended_mtrs_keeps_state. Qed.

    Lemma regfile_keeps_state_at_rise (m : MTrs) ins flops :
      trsT (regfile_mtrs ClockRise m).(mtrs_func) ins flops =
      (flops, snd (m.(mtrs_func) ins flops)).
    Proof. apply suspended_mtrs_keeps_state. Qed.

    Lemma dmem_keeps_state_at_reset_or_fall (p : Phase) (m : MTrs) ins flops :
      (p = ResetFall \/ p = ClockFall) ->
      trsT (dmem_mtrs p m).(mtrs_func) ins flops =
      (flops, snd (m.(mtrs_func) ins flops)).
    Proof.
      intros [-> | ->]; apply suspended_mtrs_keeps_state.
    Qed.

    (** Complete child registry for [core.v].  Combinational children remain
        active in every phase; all stateful children are selected above. *)
    Definition core_etrs (p : Phase) (eid : bzeeno_vid) : trsOk MTrs :=
      match eid with
      | pc_o_pc => Sret (async_pipeline_mtrs p (BzeenoPipeline.PCReg.mtrs : MTrs))
      | ifid_o_id_instr => Sret (async_pipeline_mtrs p (BzeenoPipeline.IFIDReg.mtrs : MTrs))
      | idexe_o_p4 => Sret (async_pipeline_mtrs p (BzeenoPipeline.IDEXEReg.mtrs : MTrs))
      | exemem_o_data => Sret (async_pipeline_mtrs p (BzeenoPipeline.EXEMEMReg.mtrs : MTrs))
      | memwb_o_data => Sret (async_pipeline_mtrs p (BzeenoPipeline.MEMWBReg.mtrs : MTrs))
      | rf_array => Sret (regfile_mtrs p (BzeenoPipeline.RegFile.mtrs : MTrs))
      | dmem_ram => Sret (dmem_mtrs p (BzeenoPipeline.DataMem.mtrs : MTrs))
      | store_o_data => Sret (BzeenoPipeline.StoreModifier.mtrs : MTrs)
      | load_o_data => Sret (BzeenoPipeline.LoadModifier.mtrs : MTrs)
      | imm_o_value => Sret (BzeenoPipeline.ImmDecode.mtrs : MTrs)
      | cmp_o_lt => Sret (BzeenoPipeline.Comparator.mtrs : MTrs)
      | alu_o_result => Sret (BzeenoPipeline.ALU.mtrs : MTrs)
      | mux3_o_data => Sret (BzeenoPipeline.Mux3.mtrs : MTrs)
      | mux4_o_data => Sret (BzeenoPipeline.Mux4.mtrs : MTrs)
      | cla_o_sum => Sret (BzeenoPipeline.CLA32.mtrs : MTrs)
      | ctl_o_aluc => Sret (BzeenoControl.mtrs : MTrs)
      | imem_rom => Sret (BzeenoPipeline.InstructionMem.mtrs : MTrs)
      | _ => Fail TrsUndeclared
      end.

    Example pipeline_runs_at_rise :
      core_etrs ClockRise pc_o_pc = Sret (BzeenoPipeline.PCReg.mtrs : MTrs).
    Proof. reflexivity. Qed.

    Example pipeline_is_suspended_at_fall :
      core_etrs ClockFall pc_o_pc =
      Sret (suspended_mtrs (BzeenoPipeline.PCReg.mtrs : MTrs)).
    Proof. reflexivity. Qed.

    Example regfile_runs_at_fall :
      core_etrs ClockFall rf_array = Sret (BzeenoPipeline.RegFile.mtrs : MTrs).
    Proof. reflexivity. Qed.

    Example dmem_is_suspended_at_reset :
      core_etrs ResetFall dmem_ram =
      Sret (suspended_mtrs (BzeenoPipeline.DataMem.mtrs : MTrs)).
    Proof. reflexivity. Qed.

    (** This conjunction is the checked Bzeeno scheduling contract used by
        the later simulation invariant: reset↓ updates every async-reset
        pipeline/RF block but not RAM; clk↑ updates the pipeline and RAM;
        clk↓ updates only the inverted-clock RF among stateful children. *)
    Example phase_registry_contract :
      core_etrs ResetFall pc_o_pc = Sret (BzeenoPipeline.PCReg.mtrs : MTrs) /\
      core_etrs ResetFall rf_array = Sret (BzeenoPipeline.RegFile.mtrs : MTrs) /\
      core_etrs ResetFall dmem_ram = Sret (suspended_mtrs (BzeenoPipeline.DataMem.mtrs : MTrs)) /\
      core_etrs ClockRise dmem_ram = Sret (BzeenoPipeline.DataMem.mtrs : MTrs) /\
      core_etrs ClockFall rf_array = Sret (BzeenoPipeline.RegFile.mtrs : MTrs) /\
      core_etrs ClockFall memwb_o_data =
        Sret (suspended_mtrs (BzeenoPipeline.MEMWBReg.mtrs : MTrs)).
    Proof. repeat split; reflexivity. Qed.
  End Scheduler.

  (** Keep the finite phase registry opaque while certifying the surrounding
      fixed point.  Its lookup equations above remain available, whereas Coq
      avoids eagerly unfolding every imported child proof term. *)
  Opaque core_etrs.

  Section Hierarchy.
    Context `{sz_ops} `{array_ops hmap}.

    (** [core.v] has no local procedural block; the phase-sensitive behavior
        comes entirely from its child registry.  This is nevertheless a
        genuine hierarchical MTrs: the fixed point unfolds all direct
        instances through [core_etrs]. *)
    Definition fullcore_mtrs (p : Phase) : MTrs :=
      {| mtrs_input_vids := fst (getIOIds BzeenoFullCore.M.m);
         mtrs_output_vids := snd (getIOIds BzeenoFullCore.M.m);
         mtrs_func := MTrs_rep_n BzeenoFullCore.M.m fmapEmpty (core_etrs p) 4%nat |}.

    (** Closed CPU registry: the phase-aware [core] is connected to the
        rising-edge data RAM and the read-only instruction ROM. *)
    Definition cpu_etrs (p : Phase) (eid : bzeeno_vid) : trsOk MTrs :=
      match eid with
      | bcore_top => Sret (fullcore_mtrs p)
      | dmem_ram => Sret (dmem_mtrs p (BzeenoPipeline.DataMem.mtrs : MTrs))
      | imem_rom => Sret (BzeenoPipeline.InstructionMem.mtrs : MTrs)
      | _ => Fail TrsUndeclared
      end.

    Definition cpu_mtrs (p : Phase) : MTrs :=
      {| mtrs_input_vids := fst (getIOIds BzeenoCPU.M.m);
         mtrs_output_vids := snd (getIOIds BzeenoCPU.M.m);
         mtrs_func := MTrs_rep_n BzeenoCPU.M.m fmapEmpty (cpu_etrs p) 4%nat |}.

    Definition transition (p : Phase) : State -> State -> State * State :=
      trsT (cpu_mtrs p).(mtrs_func).

    Example cpu_registry_is_closed_at_rise :
      cpu_etrs ClockRise bcore_top = Sret (fullcore_mtrs ClockRise).
    Proof. reflexivity. Qed.
  End Hierarchy.
End BzeenoEventMTrs.
