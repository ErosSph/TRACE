(** Structural state for the complete repaired five-stage [core.v].

    This is the state shape required by the eventual top-level transition:
    combinational units are absent, while all six stateful instances are kept
    at their instance paths.  The external instruction and data memories are
    modelled as inputs at this layer, exactly as in [Core/core.v]. *)
Require Import Coq.ZArith.BinInt Coq.Lists.List.
Require Import Lib.Lib. Import SZNotations.
Require Import Lang.Lang.
Require Import Ex.External.BzeenoPipeline.

#[local] Existing Instance bzeeno_vid_t_c.
#[local] Existing Instance bzeeno_vid_ops.
#[local] Existing Instance BzeenoPipeline.PCReg.flops_structured.
#[local] Existing Instance BzeenoPipeline.IFIDReg.flops_structured.
#[local] Existing Instance BzeenoPipeline.IDEXEReg.flops_structured.
#[local] Existing Instance BzeenoPipeline.EXEMEMReg.flops_structured.
#[local] Existing Instance BzeenoPipeline.MEMWBReg.flops_structured.
#[local] Existing Instance BzeenoPipeline.RegFile.flops_structured.

Module BzeenoTopState.
  Record Inputs := { resetn_v : SZ; instr_v : SZ; dmem_v : SZ }.
  Record Flops := {
    pc_v : BzeenoPipeline.PCReg.Flops;
    ifid_v : BzeenoPipeline.IFIDReg.Flops;
    idexe_v : BzeenoPipeline.IDEXEReg.Flops;
    exemem_v : BzeenoPipeline.EXEMEMReg.Flops;
    memwb_v : BzeenoPipeline.MEMWBReg.Flops;
    rf_v : BzeenoPipeline.RegFile.Flops;
  }.

  (** Architectural observation point for the derived RTL.  This deliberately
      reads the MEM/WB instance, not [pc_v]: the latter is the current IF
      fetch address and can lead the retiring instruction by several cycles.
      Once the complete [core.v] AST is connected, these are the values wired
      to [o_commit_vld] and [o_commit_pc]. *)
  Definition commit_vld (f : Flops) : SZ :=
    BzeenoPipeline.MEMWBReg.valid_v (memwb_v f).

  Definition commit_pc (f : Flops) : SZ :=
    BzeenoPipeline.MEMWBReg.pc_v (memwb_v f).

  Definition CommitAt (f : Flops) (pc : Z) : Prop :=
    commit_vld f = #{1,1,false} /\ commit_pc f = #{pc,32,false}.

  Lemma commit_observation_is_memwb (f : Flops) :
    (commit_vld f, commit_pc f) =
      (BzeenoPipeline.MEMWBReg.valid_v (memwb_v f),
       BzeenoPipeline.MEMWBReg.pc_v (memwb_v f)).
  Proof. reflexivity. Qed.

  Section Structure.
    Context {SZ_OPS : sz_ops} {ARRAY_OPS : array_ops hmap}.
    Import ListNotations. Import HMapNotations.

    #[export] Instance inputs_structured : StructuredState Inputs := {
      from_state := fun s =>
        r <- @sfind SZ_OPS bzeeno_vid_t_c bzeeno_vid_ops ARRAY_OPS bcore_resetn s;
        i <- @sfind SZ_OPS bzeeno_vid_t_c bzeeno_vid_ops ARRAY_OPS bcore_instr s;
        d <- @sfind SZ_OPS bzeeno_vid_t_c bzeeno_vid_ops ARRAY_OPS bcore_dmem s;
        Sret {| resetn_v := hbits r; instr_v := hbits i; dmem_v := hbits d |};
      to_state := fun i => match i with
        | {| resetn_v := r; instr_v := ins; dmem_v := dm |} =>
            HMapStr [(bcore_resetn,HMapBits r);(bcore_instr,HMapBits ins);(bcore_dmem,HMapBits dm)]
        end;
    }.

    #[export] Instance flops_structured : StructuredState Flops := {
      from_state := fun s =>
        p <- @sfind SZ_OPS bzeeno_vid_t_c bzeeno_vid_ops ARRAY_OPS bcore_pc_pipeline_reg s;
        f_pc <- from_state (A := BzeenoPipeline.PCReg.Flops) p;
        q <- @sfind SZ_OPS bzeeno_vid_t_c bzeeno_vid_ops ARRAY_OPS bcore_if_id_pipeline_reg s;
        f_ifid <- from_state (A := BzeenoPipeline.IFIDReg.Flops) q;
        r <- @sfind SZ_OPS bzeeno_vid_t_c bzeeno_vid_ops ARRAY_OPS bcore_id_exe_pipeline_reg s;
        f_idexe <- from_state (A := BzeenoPipeline.IDEXEReg.Flops) r;
        x <- @sfind SZ_OPS bzeeno_vid_t_c bzeeno_vid_ops ARRAY_OPS bcore_exe_mem_pipeline_reg s;
        f_exemem <- from_state (A := BzeenoPipeline.EXEMEMReg.Flops) x;
        y <- @sfind SZ_OPS bzeeno_vid_t_c bzeeno_vid_ops ARRAY_OPS bcore_mem_wb_pipeline_reg s;
        f_memwb <- from_state (A := BzeenoPipeline.MEMWBReg.Flops) y;
        z <- @sfind SZ_OPS bzeeno_vid_t_c bzeeno_vid_ops ARRAY_OPS bcore_register_file s;
        f_rf <- from_state (A := BzeenoPipeline.RegFile.Flops) z;
        Sret {| pc_v := f_pc; ifid_v := f_ifid; idexe_v := f_idexe;
                exemem_v := f_exemem; memwb_v := f_memwb; rf_v := f_rf |};
      to_state := fun f => match f with
        | {| pc_v := a; ifid_v := b; idexe_v := c; exemem_v := d; memwb_v := e; rf_v := g |} =>
            HMapStr [(bcore_pc_pipeline_reg,to_state a);(bcore_if_id_pipeline_reg,to_state b);
                     (bcore_id_exe_pipeline_reg,to_state c);(bcore_exe_mem_pipeline_reg,to_state d);
                     (bcore_mem_wb_pipeline_reg,to_state e);(bcore_register_file,to_state g);
                     (bcore_p4_adder,HMapEmpty);(bcore_next_pc_mux,HMapEmpty);
                     (bcore_controller,HMapEmpty);(bcore_compare_unit,HMapEmpty);
                     (bcore_immediate_decoder,HMapEmpty);(bcore_jal_pc_adder,HMapEmpty);
                     (bcore_br_jalr_adder,HMapEmpty);(bcore_fwda_mux,HMapEmpty);
                     (bcore_fwdb_mux,HMapEmpty);(bcore_alu_unit,HMapEmpty);
                     (bcore_exe_data_mux,HMapEmpty);(bcore_store_unit,HMapEmpty);
                     (bcore_load_unit,HMapEmpty)]
        end;
    }.
  End Structure.
End BzeenoTopState.
