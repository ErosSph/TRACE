(** Closed CPU hierarchy: [core] connected to its ROM and byte-addressed RAM.

    This reuses identifiers reserved by the earlier fetch-only import.  The
    identifiers are local names in this distinct AST; reusing them avoids
    enlarging the already very large global signal enumeration. *)
Require Import Coq.ZArith.BinInt Coq.Lists.List.
Require Import Lib.Lib. Import SZNotations.
Require Import Lang.Lang.
Require Import Lang.ModuleITree.
Require Import Ex.External.BzeenoPipeline Ex.External.BzeenoCore.
Require Import Ex.External.BzeenoFullCore Ex.External.BzeenoTopState.

#[local] Existing Instance bzeeno_vid_t_c.
#[local] Existing Instance bzeeno_vid_ops.
#[local] Existing Instance BzeenoTopState.inputs_structured.
#[local] Existing Instance BzeenoTopState.flops_structured.
#[local] Existing Instance BzeenoPipeline.DataMem.flops_structured.
#[local] Existing Instance BzeenoPipeline.InstructionMem.flops_structured.

Module BzeenoCPU.
  Module M.
    Notation "'cpu'" := corefs_top (in custom ce_top).
    Notation "'i_clk'" := corefs_clk (in custom ce_expr).
    Notation "'i_resetn'" := corefs_resetn (in custom ce_expr).
    Notation "'instr'" := corefs_if_instr (in custom ce_expr).
    Notation "'pc'" := corefs_if_pc (in custom ce_expr).
    Notation "'addr_out'" := corefs_if_p4 (in custom ce_expr).
    Notation "'mem_out'" := corefs_id_instr (in custom ce_expr).
    Notation "'commit_vld'" := corefs_id_p4 (in custom ce_expr).
    Notation "'commit_pc'" := corefs_id_pc (in custom ce_expr).
    Notation "'core_dmem_in'" := corefs_pc (in custom ce_expr).
    Notation "'core_dmem_out'" := corefs_nextpc (in custom ce_expr).
    Notation "'wmem'" := corefs_we (in custom ce_expr).
    Notation "'sb'" := corefs_id_valid (in custom ce_expr).
    Notation "'sh'" := corefs_o_id_p4 (in custom ce_expr).
    Notation "'core'" := bcore_top (in custom ce_expr).
    Notation "'data_mem'" := dmem_ram (in custom ce_expr).
    Notation "'instruction_mem'" := imem_rom (in custom ce_expr).
    Notation "'core1'" := corefs_o_pc (in custom ce_expr).
    Notation "'dmem'" := corefs_o_id_pc (in custom ce_expr).
    Notation "'imem'" := corefs_o_id_instr (in custom ce_expr).

    Notation "'bcore_clk'" := bcore_clk (in custom ce_portconnid).
    Notation "'bcore_resetn'" := bcore_resetn (in custom ce_portconnid).
    Notation "'bcore_instr'" := bcore_instr (in custom ce_portconnid).
    Notation "'bcore_dmem'" := bcore_dmem (in custom ce_portconnid).
    Notation "'bcore_o_pc'" := bcore_o_pc (in custom ce_portconnid).
    Notation "'bcore_o_addr'" := bcore_o_addr (in custom ce_portconnid).
    Notation "'bcore_o_dmem'" := bcore_o_dmem (in custom ce_portconnid).
    Notation "'bcore_o_wmem'" := bcore_o_wmem (in custom ce_portconnid).
    Notation "'bcore_o_sb'" := bcore_o_sb (in custom ce_portconnid).
    Notation "'bcore_o_sh'" := bcore_o_sh (in custom ce_portconnid).
    Notation "'bcore_o_commit_vld'" := bcore_o_commit_vld (in custom ce_portconnid).
    Notation "'bcore_o_commit_pc'" := bcore_o_commit_pc (in custom ce_portconnid).
    Notation "'dmem_i_clk'" := dmem_i_clk (in custom ce_portconnid).
    Notation "'dmem_i_we'" := dmem_i_we (in custom ce_portconnid).
    Notation "'dmem_i_sb'" := dmem_i_sb (in custom ce_portconnid).
    Notation "'dmem_i_sh'" := dmem_i_sh (in custom ce_portconnid).
    Notation "'dmem_i_data'" := dmem_i_data (in custom ce_portconnid).
    Notation "'dmem_i_addr'" := dmem_i_addr (in custom ce_portconnid).
    Notation "'dmem_o_data'" := dmem_o_data (in custom ce_portconnid).
    Notation "'imem_i_addr'" := imem_i_addr (in custom ce_portconnid).
    Notation "'imem_o_instr'" := imem_o_instr (in custom ce_portconnid).

    Definition m : @VModuleDecl bzeeno_vid := #[
module cpu
 (input logic i_clk, input logic i_resetn, output logic [31:0] instr,
  output logic [31:0] pc, output logic [31:0] addr_out,
  output logic [31:0] mem_out, output logic commit_vld,
  output logic [31:0] commit_pc);
logic [31:0] core_dmem_in; logic [31:0] core_dmem_out; logic wmem; logic sb; logic sh;
core core1(bcore_clk(i_clk), bcore_resetn(i_resetn), bcore_instr(instr), bcore_dmem(core_dmem_in), bcore_o_pc(pc), bcore_o_addr(addr_out), bcore_o_dmem(core_dmem_out), bcore_o_wmem(wmem), bcore_o_sb(sb), bcore_o_sh(sh), bcore_o_commit_vld(commit_vld), bcore_o_commit_pc(commit_pc));
data_mem dmem(dmem_i_clk(i_clk), dmem_i_we(wmem), dmem_i_sb(sb), dmem_i_sh(sh), dmem_i_data(core_dmem_out), dmem_i_addr(addr_out), dmem_o_data(core_dmem_in));
instruction_mem imem(imem_i_addr(pc), imem_o_instr(instr));
assign mem_out = core_dmem_in;
endmodule].
  End M.

  Section Registry.
    Context `{sz_ops} `{array_ops hmap}.
    Definition etrs (eid : bzeeno_vid) : trsOk MTrs :=
      match eid with
      | bcore_top => Sret (BzeenoFullCore.mtrs : MTrs)
      | dmem_ram => Sret (BzeenoPipeline.DataMem.mtrs : MTrs)
      | imem_rom => Sret (BzeenoPipeline.InstructionMem.mtrs : MTrs)
      | _ => Fail TrsUndeclared
      end.
  End Registry.

  Record Inputs := { resetn_v : SZ }.
  Record Flops := {
    core_v : BzeenoTopState.Flops;
    dmem_v : BzeenoPipeline.DataMem.Flops;
    imem_v : BzeenoPipeline.InstructionMem.Flops;
  }.

  Section Structure.
    Context `{sz_ops} `{array_ops hmap}.
    Import ListNotations HMapNotations.

    #[export] Instance inputs_structured : StructuredState Inputs := {
      from_state := fun s => r <- @sfind _ bzeeno_vid_t_c bzeeno_vid_ops _ corefs_resetn s;
        Sret {| resetn_v := hbits r |};
      to_state := fun i => match i with
        | {| resetn_v := r |} => HMapStr [(corefs_resetn, HMapBits r)]
        end;
    }.

    #[export] Instance flops_structured : StructuredState Flops := {
      from_state := fun s =>
        c <- @sfind _ bzeeno_vid_t_c bzeeno_vid_ops _ corefs_o_pc s;
        core_v <- from_state (A := BzeenoTopState.Flops) c;
        d <- @sfind _ bzeeno_vid_t_c bzeeno_vid_ops _ corefs_o_id_pc s;
        dmem_v <- from_state (A := BzeenoPipeline.DataMem.Flops) d;
        m <- @sfind _ bzeeno_vid_t_c bzeeno_vid_ops _ corefs_o_id_instr s;
        imem_v <- from_state (A := BzeenoPipeline.InstructionMem.Flops) m;
        Sret {| core_v := core_v; dmem_v := dmem_v; imem_v := imem_v |};
      to_state := fun f => match f with
        | {| core_v := c; dmem_v := d; imem_v := m |} =>
            HMapStr [(corefs_o_pc, to_state c);
                     (corefs_o_id_pc, to_state d);
                     (corefs_o_id_instr, to_state m)]
        end;
    }.

    Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Flops.
    Proof.
      unshelve epose (trs := _ : MTrs).
      { apply Build_MTrs. 1-2: shelve.
        intros inputs flops.
        destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
        destruct (from_state (A := Flops) flops) as [f_format|]; [| eapply (_, _)].
        destruct i_format, f_format. eapply (_, _). }
      apply mk_MTrsOf with (mtrsof_mtrs := trs).
      1-2: vm_compute; reflexivity.
      red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
      destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
        vm_compute in Htrs; injection Htrs as <- <-.
      2-4: eauto.
      eexists _. split; [split|].
      - eapply trsM_iff_rep_is_chain with (n := 4%nat). cbv. reflexivity.
      - vm_compute. reflexivity.
      - cbv. reflexivity.
    Defined.
  End Structure.

  (** The whole-CPU transition and its commit-filtered observable behavior.
      The reset input is fixed high after initialization; the ROM and RAM are
      part of [Flops], so this ITree has no unconstrained instruction/data
      input stream. *)
  Section Target.
    Context `{sz_ops} `{array_ops hmap}.
    Import ListNotations HMapNotations.
    Definition transition : ModuleITree.Transition := trsT mtrs.(mtrs_func).

    Definition commit_valid (o : State) : bool :=
      match @sfind _ bzeeno_vid_t_c bzeeno_vid_ops _ corefs_id_p4 o with
      | Sret v => negb (szIsZero (hbits v))
      | Fail _ => false
      end.

    Definition running_input : State :=
      HMapStr [(corefs_resetn, HMapBits #{1,1,false})].

    Definition commit_itree (initial_state : State) :=
      ModuleITree.filter_io running_input commit_valid
        (ModuleITree.module_itree transition initial_state).
  End Target.
End BzeenoCPU.
