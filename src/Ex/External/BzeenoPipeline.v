(**
    Checked import of two stateful blocks from the patched bzeeno-rv32i
    five-stage RV32I pipeline.  The derived design is based on upstream
    commit c190c1f83480b3dc8f1d161f047055be68b2fc4b.

    RTL sources:
    - derived/bzeeno-rv32i/CPU/Core/Pipeline_Registers/pc_reg.v
    - derived/bzeeno-rv32i/CPU/Core/Pipeline_Registers/if_id_reg.v

    The project supplies an AST and its semantics, not a Verilog parser.  The
    definitions below are consequently the reviewed translation boundary.

    Both RTL blocks use [@(posedge i_clk or negedge i_resetn)].  The current
    VerilRocq transfer function treats a process timing control as the body
    evaluated during one abstract transition.  Therefore the imported AST
    denotes the source behaviour at a sampled clock step: reset is sampled at
    every step, rather than modelling an independent asynchronous-reset event.
    This remains the certified synchronous [MTrsOf] interpretation.  The
    opt-in event-aware hierarchy is defined separately in
    [BzeenoEventMTrs.v], so it does not alter this paper-artifact contract.
 *)

Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Lib.Lib. Import SZNotations.
Require Import Lang.Lang.

Inductive bzeeno_vid :=
| pc_i_clk | pc_i_resetn | pc_i_we | pc_i_pc | pc_o_pc
| ifid_i_clk | ifid_i_resetn | ifid_i_we | ifid_i_flush
| ifid_i_if_p4 | ifid_i_if_pc | ifid_i_if_instr
| ifid_o_id_p4 | ifid_o_id_pc | ifid_o_id_instr | ifid_o_id_valid
| memwb_i_clk | memwb_i_resetn | memwb_i_mem2reg | memwb_i_wreg
| memwb_i_rd | memwb_i_data | memwb_i_rd_dmem | memwb_i_valid | memwb_i_pc
| memwb_o_mem2reg | memwb_o_wreg | memwb_o_rd | memwb_o_data | memwb_o_dmem
| memwb_o_valid | memwb_o_pc
| exemem_i_clk | exemem_i_resetn | exemem_i_mem2reg | exemem_i_wmem | exemem_i_wreg
| exemem_i_lsb | exemem_i_lsh | exemem_i_loadsignext | exemem_i_rd | exemem_i_data | exemem_i_dmem
| exemem_i_valid | exemem_i_pc
| exemem_o_mem2reg | exemem_o_wmem | exemem_o_wreg | exemem_o_lsb | exemem_o_lsh
| exemem_o_loadsignext | exemem_o_rd | exemem_o_data | exemem_o_dmem
| exemem_o_valid | exemem_o_pc
| idexe_i_clk | idexe_i_resetn
| idexe_i_mem2reg | idexe_i_wmem | idexe_i_aluimm | idexe_i_slt_instr
| idexe_i_wreg | idexe_i_auipc | idexe_i_lsb | idexe_i_lsh | idexe_i_loadsignext
| idexe_i_jal | idexe_i_aluc | idexe_i_lt | idexe_i_rd | idexe_i_pc
| idexe_i_regdata1 | idexe_i_regdata2 | idexe_i_imm | idexe_i_p4
| idexe_i_valid
| idexe_o_mem2reg | idexe_o_wmem | idexe_o_aluimm | idexe_o_slt_instr
| idexe_o_wreg | idexe_o_auipc | idexe_o_lsb | idexe_o_lsh | idexe_o_loadsignext
| idexe_o_jal | idexe_o_aluc | idexe_o_lt | idexe_o_rd | idexe_o_pc
| idexe_o_regdata1 | idexe_o_regdata2 | idexe_o_imm | idexe_o_p4
| idexe_o_valid
| store_i_sb | store_i_sh | store_i_data | store_o_data
| imm_i_instr | imm_i_opcode | imm_i_signext | imm_o_value
| cmp_i_a | cmp_i_b | cmp_i_unsigned | cmp_o_lt | cmp_o_eq
| alu_i_a | alu_i_b | alu_i_aluc | alu_o_result
| rf_clk | rf_resetn | rf_rs1 | rf_rs2 | rf_rd | rf_reg_write | rf_write_data
| rf_read_data1 | rf_read_data2 | rf_array
| dmem_i_clk | dmem_i_we | dmem_i_sb | dmem_i_sh | dmem_i_data | dmem_i_addr
| dmem_o_data | dmem_ram
| imem_i_addr | imem_o_instr | imem_rom
| ctl_i_resetn | ctl_i_opcode | ctl_i_funct3 | ctl_i_funct7 | ctl_i_rs1 | ctl_i_rs2
| ctl_i_cmp_lt | ctl_i_cmp_eq | ctl_i_mem_wreg | ctl_i_mem_mem2reg
| ctl_i_exe_wreg | ctl_i_exe_mem2reg | ctl_i_mem_rd | ctl_i_exe_rd
| ctl_o_not_stall | ctl_o_flush | ctl_o_aluc | ctl_o_pcsrc | ctl_o_fwda | ctl_o_fwdb
| ctl_o_wreg | ctl_o_wmem | ctl_o_mem2reg | ctl_o_aluimm | ctl_o_jal | ctl_o_jalr
| ctl_o_signext | ctl_o_auipc | ctl_o_lsb | ctl_o_lsh | ctl_o_load_signext
| ctl_o_slt_instr | ctl_o_compare_signed | ctl_o_compare_imm
| ctl_use_rs1 | ctl_use_rs2 | ctl_stall
| load_i_lb | load_i_lh | load_i_signext | load_i_offset | load_i_data | load_o_data
| mux3_i_a | mux3_i_b | mux3_i_c | mux3_i_select | mux3_o_data
| mux4_i_a | mux4_i_b | mux4_i_c | mux4_i_d | mux4_i_select | mux4_o_data
| cla_i_a | cla_i_b | cla_i_cin | cla_o_sum | cla_o_cout | cla_total
| corefs_top | corefs_clk | corefs_resetn | corefs_we | corefs_nextpc
| corefs_if_p4 | corefs_if_pc | corefs_if_instr | corefs_pc
| corefs_id_p4 | corefs_id_pc | corefs_id_instr | corefs_id_valid
| corefs_o_pc | corefs_o_id_p4 | corefs_o_id_pc | corefs_o_id_instr
| bcore_top | bcore_clk | bcore_resetn | bcore_instr | bcore_dmem
| bcore_o_pc | bcore_o_addr | bcore_o_dmem | bcore_o_wmem | bcore_o_sb | bcore_o_sh
| bcore_o_commit_vld | bcore_o_commit_pc
| bcore_pc_next | bcore_if_pc | bcore_if_p4
| bcore_id_instr | bcore_id_valid | bcore_imm_val | bcore_opcode | bcore_rd | bcore_rs1 | bcore_rs2
| bcore_funct3 | bcore_funct7 | bcore_id_pc | bcore_id_p4 | bcore_jalr_inputb | bcore_jal_pc
| bcore_jalr_pc_raw | bcore_jalr_pc | bcore_compare_inputb | bcore_fwda | bcore_fwdb | bcore_aluc
| bcore_id_regdata1 | bcore_id_regdata2 | bcore_pcsrc | bcore_mem2reg | bcore_wmem | bcore_aluimm
| bcore_wreg | bcore_jal | bcore_jalr | bcore_signext | bcore_auipc | bcore_lsb | bcore_lsh
| bcore_load_signext | bcore_not_stall | bcore_flush | bcore_slt_instr | bcore_compare_lt
| bcore_compare_eq | bcore_compare_signed | bcore_compare_imm | bcore_reg_wdata | bcore_reg_rdata1
| bcore_reg_rdata2 | bcore_mod_rd_dmem
| bcore_alu_r | bcore_alu_inputa | bcore_alu_inputb | bcore_exe_data | bcore_exe_p4
| bcore_exe_mem2reg | bcore_exe_wmem | bcore_exe_aluimm | bcore_exe_slt_instr | bcore_exe_wreg
| bcore_exe_auipc | bcore_exe_lsb | bcore_exe_lsh | bcore_exe_loadsignext | bcore_exe_jal
| bcore_exe_aluc | bcore_exe_lt | bcore_exe_valid | bcore_lt_32bit | bcore_exe_rd | bcore_exe_pc | bcore_exe_dmem
| bcore_exe_regdata1 | bcore_exe_regdata2 | bcore_exe_imm
| bcore_mem_mem2reg | bcore_mem_wmem | bcore_mem_wreg | bcore_mem_lsb | bcore_mem_lsh
| bcore_mem_loadsignext | bcore_mem_valid | bcore_mem_rd | bcore_mem_data | bcore_mem_dmem | bcore_mem_pc
| bcore_wb_data | bcore_wb_mem2reg | bcore_wb_wreg | bcore_wb_valid | bcore_wb_rd | bcore_wb_dmem | bcore_wb_pc
| bcore_pc_pipeline_reg | bcore_p4_adder | bcore_next_pc_mux | bcore_if_id_pipeline_reg
| bcore_controller | bcore_compare_unit | bcore_immediate_decoder | bcore_jal_pc_adder
| bcore_br_jalr_adder | bcore_fwda_mux | bcore_fwdb_mux | bcore_id_exe_pipeline_reg
| bcore_alu_unit | bcore_exe_data_mux | bcore_store_unit | bcore_exe_mem_pipeline_reg
| bcore_load_unit | bcore_mem_wb_pipeline_reg | bcore_register_file.

Definition bzeeno_vid_eq_dec : forall (x y : bzeeno_vid), {x = y} + {x <> y} :=
  ltac:(decide equality).

#[global] Instance bzeeno_vid_t_c : vid_t_c := {| vid_t := bzeeno_vid |}.
#[global] Instance bzeeno_vid_ops : vid_ops :=
  {| vid_eq_dec := bzeeno_vid_eq_dec |}.

Definition BzeenoExprId := @VExprId bzeeno_vid.
Coercion BzeenoExprId : bzeeno_vid >-> VExpr.

Module BzeenoPipeline.

  Module PCReg.
    Module M.
      Notation "'pc_reg'" := pc_o_pc (in custom ce_top).
      Notation "'i_clk'" := pc_i_clk (in custom ce_expr).
      Notation "'i_resetn'" := pc_i_resetn (in custom ce_expr).
      Notation "'i_we'" := pc_i_we (in custom ce_expr).
      Notation "'i_pc'" := pc_i_pc (in custom ce_expr).
      Notation "'o_pc'" := pc_o_pc (in custom ce_expr).

      (** [i_we] is the repaired fetch-enable: a false value holds the PC
          while the dependent instruction remains in the IF/ID register. *)
      Definition m : @VModuleDecl bzeeno_vid := #[
module pc_reg
  (input logic        i_clk,
   input logic        i_resetn,
   input logic        i_we,
   input logic [31:0] i_pc,
   output logic [31:0] o_pc);

always @(posedge i_clk or negedge i_resetn) begin
  if (!i_resetn) o_pc <= 'b0;
  else if (i_we) o_pc <= i_pc;
end

endmodule].
    End M.

    Record Inputs := {
      resetn_v : SZ;
      we_v : SZ;
      next_pc_v : SZ;
    }.

    Record Flops := { pc_v : SZ }.

    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations.
      Import HMapNotations.

      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state =>
          resetn_v <- sfind pc_i_resetn state;
          we_v <- sfind pc_i_we state;
          next_pc_v <- sfind pc_i_pc state;
          Sret {| resetn_v := hbits resetn_v;
                  we_v := hbits we_v;
                  next_pc_v := hbits next_pc_v |};
        to_state := fun i =>
          match i with
          | {| resetn_v := resetn_v; we_v := we_v; next_pc_v := next_pc_v |} =>
              HMapStr [(pc_i_resetn, HMapBits resetn_v);
                       (pc_i_we, HMapBits we_v);
                       (pc_i_pc, HMapBits next_pc_v)]
          end;
      }.

      #[export] Instance flops_structured : StructuredState Flops := {
        from_state := fun state =>
          pc_v <- sfind pc_o_pc state;
          Sret {| pc_v := hbits pc_v |};
        to_state := fun f =>
          match f with
          | {| pc_v := pc_v |} => HMapStr [(pc_o_pc, HMapBits pc_v)]
          end;
      }.

      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.

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
        - eapply trsM_iff_rep_is_chain with (n := 1%nat). cbv. reflexivity.
        - vm_compute. reflexivity.
        - cbv. reflexivity.
      Defined.
    End AbsOps.
  End PCReg.

  Module IFIDReg.
    Module M.
      Notation "'if_id_reg'" := ifid_o_id_instr (in custom ce_top).
      Notation "'i_clk'" := ifid_i_clk (in custom ce_expr).
      Notation "'i_resetn'" := ifid_i_resetn (in custom ce_expr).
      Notation "'i_we'" := ifid_i_we (in custom ce_expr).
      Notation "'i_flush'" := ifid_i_flush (in custom ce_expr).
      Notation "'i_if_p4'" := ifid_i_if_p4 (in custom ce_expr).
      Notation "'i_if_pc'" := ifid_i_if_pc (in custom ce_expr).
      Notation "'i_if_instr'" := ifid_i_if_instr (in custom ce_expr).
      Notation "'o_id_p4'" := ifid_o_id_p4 (in custom ce_expr).
      Notation "'o_id_pc'" := ifid_o_id_pc (in custom ce_expr).
      Notation "'o_id_instr'" := ifid_o_id_instr (in custom ce_expr).
      Notation "'o_id_valid'" := ifid_o_id_valid (in custom ce_expr).

      (** The unused, undriven [id_instr] declaration in the RTL is omitted:
          it has no observable contribution to the module transition. *)
      Definition m : @VModuleDecl bzeeno_vid := #[
module if_id_reg
  (input logic        i_clk,
   input logic        i_resetn,
   input logic        i_we,
   input logic        i_flush,
   input logic [31:0] i_if_p4,
   input logic [31:0] i_if_pc,
   input logic [31:0] i_if_instr,
   output logic [31:0] o_id_p4,
   output logic [31:0] o_id_pc,
   output logic [31:0] o_id_instr,
   output logic        o_id_valid);

always @(posedge i_clk or negedge i_resetn) begin
  if (!i_resetn) begin
    o_id_p4 <= 'b0;
    o_id_pc <= 'b0;
    o_id_instr <= 32'd28691;
    o_id_valid <= 1'b0;
  end
  else if (i_flush) begin
    o_id_p4 <= 'b0;
    o_id_pc <= 'b0;
    o_id_instr <= 32'd28691;
    o_id_valid <= 1'b0;
  end
  else begin
    if (i_we) begin
      o_id_p4 <= i_if_p4;
      o_id_pc <= i_if_pc;
      o_id_instr <= i_if_instr;
      o_id_valid <= 1'b1;
    end
  end
end

endmodule].
    End M.

    Record Inputs := {
      resetn_v : SZ;
      we_v : SZ;
      flush_v : SZ;
      if_p4_v : SZ;
      if_pc_v : SZ;
      if_instr_v : SZ;
    }.

    Record Flops := {
      id_p4_v : SZ;
      id_pc_v : SZ;
      id_instr_v : SZ;
      id_valid_v : SZ;
    }.

    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations.
      Import HMapNotations.

      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state =>
          resetn_v <- sfind ifid_i_resetn state;
          we_v <- sfind ifid_i_we state;
          flush_v <- sfind ifid_i_flush state;
          if_p4_v <- sfind ifid_i_if_p4 state;
          if_pc_v <- sfind ifid_i_if_pc state;
          if_instr_v <- sfind ifid_i_if_instr state;
          Sret {| resetn_v := hbits resetn_v; we_v := hbits we_v;
                  flush_v := hbits flush_v; if_p4_v := hbits if_p4_v;
                  if_pc_v := hbits if_pc_v; if_instr_v := hbits if_instr_v |};
        to_state := fun i =>
          match i with
          | {| resetn_v := resetn_v; we_v := we_v; flush_v := flush_v;
               if_p4_v := if_p4_v; if_pc_v := if_pc_v; if_instr_v := if_instr_v |} =>
              HMapStr [(ifid_i_resetn, HMapBits resetn_v);
                       (ifid_i_we, HMapBits we_v);
                       (ifid_i_flush, HMapBits flush_v);
                       (ifid_i_if_p4, HMapBits if_p4_v);
                       (ifid_i_if_pc, HMapBits if_pc_v);
                       (ifid_i_if_instr, HMapBits if_instr_v)]
          end;
      }.

      #[export] Instance flops_structured : StructuredState Flops := {
        from_state := fun state =>
          id_p4_v <- sfind ifid_o_id_p4 state;
          id_pc_v <- sfind ifid_o_id_pc state;
          id_instr_v <- sfind ifid_o_id_instr state;
          id_valid_v <- sfind ifid_o_id_valid state;
          Sret {| id_p4_v := hbits id_p4_v; id_pc_v := hbits id_pc_v;
                  id_instr_v := hbits id_instr_v; id_valid_v := hbits id_valid_v |};
        to_state := fun f =>
          match f with
          | {| id_p4_v := id_p4_v; id_pc_v := id_pc_v; id_instr_v := id_instr_v;
               id_valid_v := id_valid_v |} =>
              HMapStr [(ifid_o_id_p4, HMapBits id_p4_v);
                       (ifid_o_id_pc, HMapBits id_pc_v);
                       (ifid_o_id_instr, HMapBits id_instr_v);
                       (ifid_o_id_valid, HMapBits id_valid_v)]
          end;
      }.

      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.

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
        - eapply trsM_iff_rep_is_chain with (n := 1%nat). cbv. reflexivity.
        - vm_compute. reflexivity.
        - cbv. reflexivity.
      Defined.
    End AbsOps.
  End IFIDReg.

  (** WB-stage pipeline state from [Pipeline_Registers/mem_wb_reg.v]. *)
  Module MEMWBReg.
    Module M.
      Notation "'mem_wb_reg'" := memwb_o_data (in custom ce_top).
      Notation "'i_clk'" := memwb_i_clk (in custom ce_expr).
      Notation "'i_resetn'" := memwb_i_resetn (in custom ce_expr).
      Notation "'i_mem_mem2reg'" := memwb_i_mem2reg (in custom ce_expr).
      Notation "'i_mem_wreg'" := memwb_i_wreg (in custom ce_expr).
      Notation "'i_mem_rd'" := memwb_i_rd (in custom ce_expr).
      Notation "'i_mem_data'" := memwb_i_data (in custom ce_expr).
      Notation "'i_rd_dmem'" := memwb_i_rd_dmem (in custom ce_expr).
      Notation "'i_mem_valid'" := memwb_i_valid (in custom ce_expr).
      Notation "'i_mem_pc'" := memwb_i_pc (in custom ce_expr).
      Notation "'o_wb_mem2reg'" := memwb_o_mem2reg (in custom ce_expr).
      Notation "'o_wb_wreg'" := memwb_o_wreg (in custom ce_expr).
      Notation "'o_wb_rd'" := memwb_o_rd (in custom ce_expr).
      Notation "'o_wb_data'" := memwb_o_data (in custom ce_expr).
      Notation "'o_wb_dmem'" := memwb_o_dmem (in custom ce_expr).
      Notation "'o_wb_valid'" := memwb_o_valid (in custom ce_expr).
      Notation "'o_wb_pc'" := memwb_o_pc (in custom ce_expr).

      Definition m : @VModuleDecl bzeeno_vid := #[
module mem_wb_reg
  (input logic        i_clk,
   input logic        i_resetn,
   input logic        i_mem_mem2reg,
   input logic        i_mem_wreg,
   input logic [4:0]  i_mem_rd,
   input logic [31:0] i_mem_data,
   input logic [31:0] i_rd_dmem,
   input logic        i_mem_valid,
   input logic [31:0] i_mem_pc,
   output logic       o_wb_mem2reg,
   output logic       o_wb_wreg,
   output logic [4:0] o_wb_rd,
   output logic [31:0] o_wb_data,
   output logic [31:0] o_wb_dmem,
   output logic        o_wb_valid,
   output logic [31:0] o_wb_pc);

always @(posedge i_clk or negedge i_resetn) begin
  if (!i_resetn) begin
    o_wb_mem2reg <= 'b0;
    o_wb_wreg <= 'b0;
    o_wb_data <= 'b0;
    o_wb_rd <= 'b0;
    o_wb_dmem <= 'b0;
    o_wb_valid <= 'b0;
    o_wb_pc <= 'b0;
  end
  else begin
    o_wb_mem2reg <= i_mem_mem2reg;
    o_wb_wreg <= i_mem_wreg;
    o_wb_data <= i_mem_data;
    o_wb_rd <= i_mem_rd;
    o_wb_dmem <= i_rd_dmem;
    o_wb_valid <= i_mem_valid;
    o_wb_pc <= i_mem_pc;
  end
end

endmodule].
    End M.

    Record Inputs := {
      resetn_v : SZ; in_mem2reg_v : SZ; in_wreg_v : SZ; in_rd_v : SZ;
      in_data_v : SZ; in_dmem_v : SZ; in_valid_v : SZ; in_pc_v : SZ;
    }.
    Record Flops := {
      mem2reg_v : SZ; wreg_v : SZ; rd_v : SZ; data_v : SZ; dmem_v : SZ;
      valid_v : SZ; pc_v : SZ;
    }.

    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations. Import HMapNotations.
      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state =>
          resetn_v <- sfind memwb_i_resetn state;
          in_mem2reg_v <- sfind memwb_i_mem2reg state;
          in_wreg_v <- sfind memwb_i_wreg state;
          in_rd_v <- sfind memwb_i_rd state;
          in_data_v <- sfind memwb_i_data state;
          in_dmem_v <- sfind memwb_i_rd_dmem state;
          in_valid_v <- sfind memwb_i_valid state;
          in_pc_v <- sfind memwb_i_pc state;
          Sret {| resetn_v := hbits resetn_v; in_mem2reg_v := hbits in_mem2reg_v;
                  in_wreg_v := hbits in_wreg_v; in_rd_v := hbits in_rd_v;
                  in_data_v := hbits in_data_v; in_dmem_v := hbits in_dmem_v;
                  in_valid_v := hbits in_valid_v; in_pc_v := hbits in_pc_v |};
        to_state := fun i => match i with
          | {| resetn_v := resetn_v; in_mem2reg_v := in_mem2reg_v; in_wreg_v := in_wreg_v;
               in_rd_v := in_rd_v; in_data_v := in_data_v; in_dmem_v := in_dmem_v;
               in_valid_v := in_valid_v; in_pc_v := in_pc_v |} =>
              HMapStr [(memwb_i_resetn, HMapBits resetn_v);
                       (memwb_i_mem2reg, HMapBits in_mem2reg_v);
                       (memwb_i_wreg, HMapBits in_wreg_v);
                       (memwb_i_rd, HMapBits in_rd_v);
                       (memwb_i_data, HMapBits in_data_v);
                       (memwb_i_rd_dmem, HMapBits in_dmem_v);
                       (memwb_i_valid, HMapBits in_valid_v);
                       (memwb_i_pc, HMapBits in_pc_v)]
          end;
      }.
      #[export] Instance flops_structured : StructuredState Flops := {
        from_state := fun state =>
          mem2reg_v <- sfind memwb_o_mem2reg state;
          wreg_v <- sfind memwb_o_wreg state;
          rd_v <- sfind memwb_o_rd state;
          data_v <- sfind memwb_o_data state;
          dmem_v <- sfind memwb_o_dmem state;
          valid_v <- sfind memwb_o_valid state;
          pc_v <- sfind memwb_o_pc state;
          Sret {| mem2reg_v := hbits mem2reg_v; wreg_v := hbits wreg_v;
                  rd_v := hbits rd_v; data_v := hbits data_v; dmem_v := hbits dmem_v;
                  valid_v := hbits valid_v; pc_v := hbits pc_v |};
        to_state := fun f => match f with
          | {| mem2reg_v := mem2reg_v; wreg_v := wreg_v; rd_v := rd_v;
               data_v := data_v; dmem_v := dmem_v; valid_v := valid_v; pc_v := pc_v |} =>
              HMapStr [(memwb_o_mem2reg, HMapBits mem2reg_v);
                       (memwb_o_wreg, HMapBits wreg_v);
                       (memwb_o_rd, HMapBits rd_v);
                       (memwb_o_data, HMapBits data_v);
                       (memwb_o_dmem, HMapBits dmem_v);
                       (memwb_o_valid, HMapBits valid_v);
                       (memwb_o_pc, HMapBits pc_v)]
          end;
      }.
      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.
      Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Flops.
      Proof.
        unshelve epose (trs := _ : MTrs).
        { apply Build_MTrs. 1-2: shelve. intros inputs flops.
          destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
          destruct (from_state (A := Flops) flops) as [f_format|]; [| eapply (_, _)].
          destruct i_format, f_format. eapply (_, _). }
        apply mk_MTrsOf with (mtrsof_mtrs := trs). 1-2: vm_compute; reflexivity.
        red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
        destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
          vm_compute in Htrs; injection Htrs as <- <-.
        2-4: eauto. eexists _. split; [split|].
        - eapply trsM_iff_rep_is_chain with (n := 1%nat). cbv. reflexivity.
        - vm_compute. reflexivity.
        - cbv. reflexivity.
      Defined.
    End AbsOps.
  End MEMWBReg.

  (** MEM-stage pipeline state from [Pipeline_Registers/exe_mem_reg.v]. *)
  Module EXEMEMReg.
    Module M.
      Notation "'exe_mem_reg'" := exemem_o_data (in custom ce_top).
      Notation "'i_clk'" := exemem_i_clk (in custom ce_expr).
      Notation "'i_resetn'" := exemem_i_resetn (in custom ce_expr).
      Notation "'i_exe_mem2reg'" := exemem_i_mem2reg (in custom ce_expr).
      Notation "'i_exe_wmem'" := exemem_i_wmem (in custom ce_expr).
      Notation "'i_exe_wreg'" := exemem_i_wreg (in custom ce_expr).
      Notation "'i_exe_lsb'" := exemem_i_lsb (in custom ce_expr).
      Notation "'i_exe_lsh'" := exemem_i_lsh (in custom ce_expr).
      Notation "'i_exe_loadsignext'" := exemem_i_loadsignext (in custom ce_expr).
      Notation "'i_exe_rd'" := exemem_i_rd (in custom ce_expr).
      Notation "'i_exe_data'" := exemem_i_data (in custom ce_expr).
      Notation "'i_exe_dmem'" := exemem_i_dmem (in custom ce_expr).
      Notation "'i_exe_valid'" := exemem_i_valid (in custom ce_expr).
      Notation "'i_exe_pc'" := exemem_i_pc (in custom ce_expr).
      Notation "'o_mem_mem2reg'" := exemem_o_mem2reg (in custom ce_expr).
      Notation "'o_mem_wmem'" := exemem_o_wmem (in custom ce_expr).
      Notation "'o_mem_wreg'" := exemem_o_wreg (in custom ce_expr).
      Notation "'o_mem_lsb'" := exemem_o_lsb (in custom ce_expr).
      Notation "'o_mem_lsh'" := exemem_o_lsh (in custom ce_expr).
      Notation "'o_mem_loadsignext'" := exemem_o_loadsignext (in custom ce_expr).
      Notation "'o_mem_rd'" := exemem_o_rd (in custom ce_expr).
      Notation "'o_mem_data'" := exemem_o_data (in custom ce_expr).
      Notation "'o_mem_dmem'" := exemem_o_dmem (in custom ce_expr).
      Notation "'o_mem_valid'" := exemem_o_valid (in custom ce_expr).
      Notation "'o_mem_pc'" := exemem_o_pc (in custom ce_expr).

      Definition m : @VModuleDecl bzeeno_vid := #[
module exe_mem_reg
  (input logic i_clk, input logic i_resetn,
   input logic i_exe_mem2reg, input logic i_exe_wmem, input logic i_exe_wreg,
   input logic i_exe_lsb, input logic i_exe_lsh, input logic i_exe_loadsignext,
   input logic [4:0] i_exe_rd, input logic [31:0] i_exe_data,
   input logic [31:0] i_exe_dmem,
   input logic i_exe_valid, input logic [31:0] i_exe_pc,
   output logic o_mem_mem2reg, output logic o_mem_wmem, output logic o_mem_wreg,
   output logic o_mem_lsb, output logic o_mem_lsh, output logic o_mem_loadsignext,
   output logic [4:0] o_mem_rd, output logic [31:0] o_mem_data,
   output logic [31:0] o_mem_dmem, output logic o_mem_valid,
   output logic [31:0] o_mem_pc);
always @(posedge i_clk or negedge i_resetn) begin
  if (!i_resetn) begin
    o_mem_mem2reg <= 'b0; o_mem_wmem <= 'b0; o_mem_wreg <= 'b0;
    o_mem_lsb <= 'b0; o_mem_lsh <= 'b0; o_mem_loadsignext <= 'b0;
    o_mem_data <= 'b0; o_mem_rd <= 'b0; o_mem_dmem <= 'b0;
    o_mem_valid <= 'b0; o_mem_pc <= 'b0;
  end
  else begin
    o_mem_mem2reg <= i_exe_mem2reg; o_mem_wmem <= i_exe_wmem;
    o_mem_wreg <= i_exe_wreg; o_mem_lsb <= i_exe_lsb; o_mem_lsh <= i_exe_lsh;
    o_mem_loadsignext <= i_exe_loadsignext; o_mem_data <= i_exe_data;
    o_mem_rd <= i_exe_rd; o_mem_dmem <= i_exe_dmem;
    o_mem_valid <= i_exe_valid; o_mem_pc <= i_exe_pc;
  end
end
endmodule].
    End M.

    Record Inputs := {
      resetn_v : SZ; in_mem2reg_v : SZ; in_wmem_v : SZ; in_wreg_v : SZ;
      in_lsb_v : SZ; in_lsh_v : SZ; in_loadsignext_v : SZ; in_rd_v : SZ;
      in_data_v : SZ; in_dmem_v : SZ; in_valid_v : SZ; in_pc_v : SZ;
    }.
    Record Flops := {
      mem2reg_v : SZ; wmem_v : SZ; wreg_v : SZ; lsb_v : SZ; lsh_v : SZ;
      loadsignext_v : SZ; rd_v : SZ; data_v : SZ; dmem_v : SZ;
      valid_v : SZ; pc_v : SZ;
    }.

    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations. Import HMapNotations.
      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state =>
          resetn_v <- sfind exemem_i_resetn state;
          in_mem2reg_v <- sfind exemem_i_mem2reg state;
          in_wmem_v <- sfind exemem_i_wmem state;
          in_wreg_v <- sfind exemem_i_wreg state;
          in_lsb_v <- sfind exemem_i_lsb state;
          in_lsh_v <- sfind exemem_i_lsh state;
          in_loadsignext_v <- sfind exemem_i_loadsignext state;
          in_rd_v <- sfind exemem_i_rd state;
          in_data_v <- sfind exemem_i_data state;
          in_dmem_v <- sfind exemem_i_dmem state;
          in_valid_v <- sfind exemem_i_valid state;
          in_pc_v <- sfind exemem_i_pc state;
          Sret {| resetn_v := hbits resetn_v; in_mem2reg_v := hbits in_mem2reg_v;
                  in_wmem_v := hbits in_wmem_v; in_wreg_v := hbits in_wreg_v;
                  in_lsb_v := hbits in_lsb_v; in_lsh_v := hbits in_lsh_v;
                  in_loadsignext_v := hbits in_loadsignext_v; in_rd_v := hbits in_rd_v;
                  in_data_v := hbits in_data_v; in_dmem_v := hbits in_dmem_v;
                  in_valid_v := hbits in_valid_v; in_pc_v := hbits in_pc_v |};
        to_state := fun i => match i with
          | {| resetn_v := r; in_mem2reg_v := a; in_wmem_v := b; in_wreg_v := c;
               in_lsb_v := d; in_lsh_v := e; in_loadsignext_v := f; in_rd_v := g;
               in_data_v := h; in_dmem_v := j; in_valid_v := k; in_pc_v := l |} =>
              HMapStr [(exemem_i_resetn, HMapBits r); (exemem_i_mem2reg, HMapBits a);
                       (exemem_i_wmem, HMapBits b); (exemem_i_wreg, HMapBits c);
                       (exemem_i_lsb, HMapBits d); (exemem_i_lsh, HMapBits e);
                       (exemem_i_loadsignext, HMapBits f); (exemem_i_rd, HMapBits g);
                       (exemem_i_data, HMapBits h); (exemem_i_dmem, HMapBits j);
                       (exemem_i_valid, HMapBits k); (exemem_i_pc, HMapBits l)]
          end;
      }.
      #[export] Instance flops_structured : StructuredState Flops := {
        from_state := fun state =>
          mem2reg_v <- sfind exemem_o_mem2reg state; wmem_v <- sfind exemem_o_wmem state;
          wreg_v <- sfind exemem_o_wreg state; lsb_v <- sfind exemem_o_lsb state;
          lsh_v <- sfind exemem_o_lsh state; loadsignext_v <- sfind exemem_o_loadsignext state;
          rd_v <- sfind exemem_o_rd state; data_v <- sfind exemem_o_data state;
          dmem_v <- sfind exemem_o_dmem state;
          valid_v <- sfind exemem_o_valid state; pc_v <- sfind exemem_o_pc state;
          Sret {| mem2reg_v := hbits mem2reg_v; wmem_v := hbits wmem_v;
                  wreg_v := hbits wreg_v; lsb_v := hbits lsb_v; lsh_v := hbits lsh_v;
                  loadsignext_v := hbits loadsignext_v; rd_v := hbits rd_v;
                  data_v := hbits data_v; dmem_v := hbits dmem_v;
                  valid_v := hbits valid_v; pc_v := hbits pc_v |};
        to_state := fun f => match f with
          | {| mem2reg_v := a; wmem_v := b; wreg_v := c; lsb_v := d; lsh_v := e;
               loadsignext_v := g; rd_v := h; data_v := i; dmem_v := j;
               valid_v := k; pc_v := l |} =>
              HMapStr [(exemem_o_mem2reg, HMapBits a); (exemem_o_wmem, HMapBits b);
                       (exemem_o_wreg, HMapBits c); (exemem_o_lsb, HMapBits d);
                       (exemem_o_lsh, HMapBits e); (exemem_o_loadsignext, HMapBits g);
                       (exemem_o_rd, HMapBits h); (exemem_o_data, HMapBits i);
                       (exemem_o_dmem, HMapBits j); (exemem_o_valid, HMapBits k);
                       (exemem_o_pc, HMapBits l)]
          end;
      }.
      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.
      Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Flops.
      Proof.
        unshelve epose (trs := _ : MTrs).
        { apply Build_MTrs. 1-2: shelve. intros inputs flops.
          destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
          destruct (from_state (A := Flops) flops) as [f_format|]; [| eapply (_, _)].
          destruct i_format, f_format. eapply (_, _). }
        apply mk_MTrsOf with (mtrsof_mtrs := trs). 1-2: vm_compute; reflexivity.
        red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
        destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
          vm_compute in Htrs; injection Htrs as <- <-.
        2-4: eauto. eexists _. split; [split|].
        - eapply trsM_iff_rep_is_chain with (n := 1%nat). cbv. reflexivity.
        - vm_compute. reflexivity.
        - cbv. reflexivity.
      Defined.
    End AbsOps.
  End EXEMEMReg.

  (** EXE-stage pipeline state from [Pipeline_Registers/id_exe_reg.v].

      This is a literal port-level translation of the patched design's
      register.  As for the other pipeline registers, the source's sensitivity
      list is represented by a sampled-clock transition: [i_resetn] selects
      the reset values during an abstract step. *)
  Module IDEXEReg.
    Module M.
      Notation "'id_exe_reg'" := idexe_o_p4 (in custom ce_top).
      Notation "'i_clk'" := idexe_i_clk (in custom ce_expr).
      Notation "'i_resetn'" := idexe_i_resetn (in custom ce_expr).
      Notation "'i_id_mem2reg'" := idexe_i_mem2reg (in custom ce_expr).
      Notation "'i_id_wmem'" := idexe_i_wmem (in custom ce_expr).
      Notation "'i_id_aluimm'" := idexe_i_aluimm (in custom ce_expr).
      Notation "'i_id_slt_instr'" := idexe_i_slt_instr (in custom ce_expr).
      Notation "'i_id_wreg'" := idexe_i_wreg (in custom ce_expr).
      Notation "'i_id_auipc'" := idexe_i_auipc (in custom ce_expr).
      Notation "'i_id_lsb'" := idexe_i_lsb (in custom ce_expr).
      Notation "'i_id_lsh'" := idexe_i_lsh (in custom ce_expr).
      Notation "'i_id_loadsignext'" := idexe_i_loadsignext (in custom ce_expr).
      Notation "'i_id_jal'" := idexe_i_jal (in custom ce_expr).
      Notation "'i_id_aluc'" := idexe_i_aluc (in custom ce_expr).
      Notation "'i_id_lt'" := idexe_i_lt (in custom ce_expr).
      Notation "'i_id_rd'" := idexe_i_rd (in custom ce_expr).
      Notation "'i_id_pc'" := idexe_i_pc (in custom ce_expr).
      Notation "'i_id_regdata1'" := idexe_i_regdata1 (in custom ce_expr).
      Notation "'i_id_regdata2'" := idexe_i_regdata2 (in custom ce_expr).
      Notation "'i_id_imm'" := idexe_i_imm (in custom ce_expr).
      Notation "'i_id_p4'" := idexe_i_p4 (in custom ce_expr).
      Notation "'i_id_valid'" := idexe_i_valid (in custom ce_expr).
      Notation "'o_exe_mem2reg'" := idexe_o_mem2reg (in custom ce_expr).
      Notation "'o_exe_wmem'" := idexe_o_wmem (in custom ce_expr).
      Notation "'o_exe_aluimm'" := idexe_o_aluimm (in custom ce_expr).
      Notation "'o_exe_slt_instr'" := idexe_o_slt_instr (in custom ce_expr).
      Notation "'o_exe_wreg'" := idexe_o_wreg (in custom ce_expr).
      Notation "'o_exe_auipc'" := idexe_o_auipc (in custom ce_expr).
      Notation "'o_exe_lsb'" := idexe_o_lsb (in custom ce_expr).
      Notation "'o_exe_lsh'" := idexe_o_lsh (in custom ce_expr).
      Notation "'o_exe_loadsignext'" := idexe_o_loadsignext (in custom ce_expr).
      Notation "'o_exe_jal'" := idexe_o_jal (in custom ce_expr).
      Notation "'o_exe_aluc'" := idexe_o_aluc (in custom ce_expr).
      Notation "'o_exe_lt'" := idexe_o_lt (in custom ce_expr).
      Notation "'o_exe_rd'" := idexe_o_rd (in custom ce_expr).
      Notation "'o_exe_pc'" := idexe_o_pc (in custom ce_expr).
      Notation "'o_exe_regdata1'" := idexe_o_regdata1 (in custom ce_expr).
      Notation "'o_exe_regdata2'" := idexe_o_regdata2 (in custom ce_expr).
      Notation "'o_exe_imm'" := idexe_o_imm (in custom ce_expr).
      Notation "'o_exe_p4'" := idexe_o_p4 (in custom ce_expr).
      Notation "'o_exe_valid'" := idexe_o_valid (in custom ce_expr).

      Definition m : @VModuleDecl bzeeno_vid := #[
module id_exe_reg
  (input logic i_clk, input logic i_resetn,
   input logic i_id_mem2reg, input logic i_id_wmem, input logic i_id_aluimm,
   input logic i_id_slt_instr, input logic i_id_wreg, input logic i_id_auipc,
   input logic i_id_lsb, input logic i_id_lsh, input logic i_id_loadsignext,
   input logic i_id_jal, input logic [5:0] i_id_aluc, input logic i_id_lt,
   input logic [4:0] i_id_rd, input logic [31:0] i_id_pc,
   input logic [31:0] i_id_regdata1, input logic [31:0] i_id_regdata2,
   input logic [31:0] i_id_imm, input logic [31:0] i_id_p4,
   input logic i_id_valid,
   output logic o_exe_mem2reg, output logic o_exe_wmem, output logic o_exe_aluimm,
   output logic o_exe_slt_instr, output logic o_exe_wreg, output logic o_exe_auipc,
   output logic o_exe_lsb, output logic o_exe_lsh, output logic o_exe_loadsignext,
   output logic o_exe_jal, output logic [5:0] o_exe_aluc, output logic o_exe_lt,
   output logic [4:0] o_exe_rd, output logic [31:0] o_exe_pc,
   output logic [31:0] o_exe_regdata1, output logic [31:0] o_exe_regdata2,
   output logic [31:0] o_exe_imm, output logic [31:0] o_exe_p4,
   output logic o_exe_valid);
always @(posedge i_clk or negedge i_resetn) begin
  if (!i_resetn) begin
    o_exe_mem2reg <= 'b0; o_exe_wmem <= 'b0; o_exe_aluimm <= 'b0;
    o_exe_slt_instr <= 'b0; o_exe_wreg <= 'b0; o_exe_auipc <= 'b0;
    o_exe_lsb <= 'b0; o_exe_lsh <= 'b0; o_exe_loadsignext <= 'b0;
    o_exe_jal <= 'b0; o_exe_aluc <= 'b0; o_exe_lt <= 'b0; o_exe_rd <= 'b0;
    o_exe_pc <= 'b0; o_exe_regdata1 <= 'b0; o_exe_regdata2 <= 'b0;
    o_exe_imm <= 'b0; o_exe_p4 <= 'b0;
    o_exe_valid <= 'b0;
  end
  else begin
    o_exe_mem2reg <= i_id_mem2reg; o_exe_wmem <= i_id_wmem;
    o_exe_aluimm <= i_id_aluimm; o_exe_slt_instr <= i_id_slt_instr;
    o_exe_wreg <= i_id_wreg; o_exe_auipc <= i_id_auipc; o_exe_lsb <= i_id_lsb;
    o_exe_lsh <= i_id_lsh; o_exe_loadsignext <= i_id_loadsignext;
    o_exe_jal <= i_id_jal; o_exe_aluc <= i_id_aluc; o_exe_lt <= i_id_lt;
    o_exe_rd <= i_id_rd; o_exe_pc <= i_id_pc; o_exe_regdata1 <= i_id_regdata1;
    o_exe_regdata2 <= i_id_regdata2; o_exe_imm <= i_id_imm; o_exe_p4 <= i_id_p4;
    o_exe_valid <= i_id_valid;
  end
end
endmodule].
    End M.

    Record Inputs := {
      resetn_v : SZ; in_mem2reg_v : SZ; in_wmem_v : SZ; in_aluimm_v : SZ;
      in_slt_instr_v : SZ; in_wreg_v : SZ; in_auipc_v : SZ; in_lsb_v : SZ;
      in_lsh_v : SZ; in_loadsignext_v : SZ; in_jal_v : SZ; in_aluc_v : SZ;
      in_lt_v : SZ; in_rd_v : SZ; in_pc_v : SZ; in_regdata1_v : SZ;
      in_regdata2_v : SZ; in_imm_v : SZ; in_p4_v : SZ; in_valid_v : SZ;
    }.
    Record Flops := {
      mem2reg_v : SZ; wmem_v : SZ; aluimm_v : SZ; slt_instr_v : SZ;
      wreg_v : SZ; auipc_v : SZ; lsb_v : SZ; lsh_v : SZ; loadsignext_v : SZ;
      jal_v : SZ; aluc_v : SZ; lt_v : SZ; rd_v : SZ; pc_v : SZ;
      regdata1_v : SZ; regdata2_v : SZ; imm_v : SZ; p4_v : SZ; valid_v : SZ;
    }.

    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations. Import HMapNotations.
      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state =>
          resetn_v <- sfind idexe_i_resetn state;
          in_mem2reg_v <- sfind idexe_i_mem2reg state; in_wmem_v <- sfind idexe_i_wmem state;
          in_aluimm_v <- sfind idexe_i_aluimm state; in_slt_instr_v <- sfind idexe_i_slt_instr state;
          in_wreg_v <- sfind idexe_i_wreg state; in_auipc_v <- sfind idexe_i_auipc state;
          in_lsb_v <- sfind idexe_i_lsb state; in_lsh_v <- sfind idexe_i_lsh state;
          in_loadsignext_v <- sfind idexe_i_loadsignext state; in_jal_v <- sfind idexe_i_jal state;
          in_aluc_v <- sfind idexe_i_aluc state; in_lt_v <- sfind idexe_i_lt state;
          in_rd_v <- sfind idexe_i_rd state; in_pc_v <- sfind idexe_i_pc state;
          in_regdata1_v <- sfind idexe_i_regdata1 state; in_regdata2_v <- sfind idexe_i_regdata2 state;
          in_imm_v <- sfind idexe_i_imm state; in_p4_v <- sfind idexe_i_p4 state;
          in_valid_v <- sfind idexe_i_valid state;
          Sret {| resetn_v := hbits resetn_v; in_mem2reg_v := hbits in_mem2reg_v;
                  in_wmem_v := hbits in_wmem_v; in_aluimm_v := hbits in_aluimm_v;
                  in_slt_instr_v := hbits in_slt_instr_v; in_wreg_v := hbits in_wreg_v;
                  in_auipc_v := hbits in_auipc_v; in_lsb_v := hbits in_lsb_v;
                  in_lsh_v := hbits in_lsh_v; in_loadsignext_v := hbits in_loadsignext_v;
                  in_jal_v := hbits in_jal_v; in_aluc_v := hbits in_aluc_v; in_lt_v := hbits in_lt_v;
                  in_rd_v := hbits in_rd_v; in_pc_v := hbits in_pc_v;
                  in_regdata1_v := hbits in_regdata1_v; in_regdata2_v := hbits in_regdata2_v;
                  in_imm_v := hbits in_imm_v; in_p4_v := hbits in_p4_v;
                  in_valid_v := hbits in_valid_v |};
        to_state := fun i => match i with
          | {| resetn_v := r; in_mem2reg_v := a; in_wmem_v := b; in_aluimm_v := c;
               in_slt_instr_v := d; in_wreg_v := e; in_auipc_v := f; in_lsb_v := g;
               in_lsh_v := h; in_loadsignext_v := j; in_jal_v := k; in_aluc_v := l;
               in_lt_v := n; in_rd_v := o; in_pc_v := p; in_regdata1_v := q;
               in_regdata2_v := s; in_imm_v := t; in_p4_v := u; in_valid_v := v |} =>
              HMapStr [(idexe_i_resetn, HMapBits r); (idexe_i_mem2reg, HMapBits a);
                       (idexe_i_wmem, HMapBits b); (idexe_i_aluimm, HMapBits c);
                       (idexe_i_slt_instr, HMapBits d); (idexe_i_wreg, HMapBits e);
                       (idexe_i_auipc, HMapBits f); (idexe_i_lsb, HMapBits g);
                       (idexe_i_lsh, HMapBits h); (idexe_i_loadsignext, HMapBits j);
                       (idexe_i_jal, HMapBits k); (idexe_i_aluc, HMapBits l);
                       (idexe_i_lt, HMapBits n); (idexe_i_rd, HMapBits o); (idexe_i_pc, HMapBits p);
                       (idexe_i_regdata1, HMapBits q); (idexe_i_regdata2, HMapBits s);
                       (idexe_i_imm, HMapBits t); (idexe_i_p4, HMapBits u);
                       (idexe_i_valid, HMapBits v)]
          end;
      }.
      #[export] Instance flops_structured : StructuredState Flops := {
        from_state := fun state =>
          mem2reg_v <- sfind idexe_o_mem2reg state; wmem_v <- sfind idexe_o_wmem state;
          aluimm_v <- sfind idexe_o_aluimm state; slt_instr_v <- sfind idexe_o_slt_instr state;
          wreg_v <- sfind idexe_o_wreg state; auipc_v <- sfind idexe_o_auipc state;
          lsb_v <- sfind idexe_o_lsb state; lsh_v <- sfind idexe_o_lsh state;
          loadsignext_v <- sfind idexe_o_loadsignext state; jal_v <- sfind idexe_o_jal state;
          aluc_v <- sfind idexe_o_aluc state; lt_v <- sfind idexe_o_lt state;
          rd_v <- sfind idexe_o_rd state; pc_v <- sfind idexe_o_pc state;
          regdata1_v <- sfind idexe_o_regdata1 state; regdata2_v <- sfind idexe_o_regdata2 state;
          imm_v <- sfind idexe_o_imm state; p4_v <- sfind idexe_o_p4 state;
          valid_v <- sfind idexe_o_valid state;
          Sret {| mem2reg_v := hbits mem2reg_v; wmem_v := hbits wmem_v;
                  aluimm_v := hbits aluimm_v; slt_instr_v := hbits slt_instr_v;
                  wreg_v := hbits wreg_v; auipc_v := hbits auipc_v; lsb_v := hbits lsb_v;
                  lsh_v := hbits lsh_v; loadsignext_v := hbits loadsignext_v; jal_v := hbits jal_v;
                  aluc_v := hbits aluc_v; lt_v := hbits lt_v; rd_v := hbits rd_v; pc_v := hbits pc_v;
                  regdata1_v := hbits regdata1_v; regdata2_v := hbits regdata2_v;
                  imm_v := hbits imm_v; p4_v := hbits p4_v; valid_v := hbits valid_v |};
        to_state := fun f => match f with
          | {| mem2reg_v := a; wmem_v := b; aluimm_v := c; slt_instr_v := d;
               wreg_v := e; auipc_v := f; lsb_v := g; lsh_v := h; loadsignext_v := j;
               jal_v := k; aluc_v := l; lt_v := n; rd_v := o; pc_v := p;
               regdata1_v := q; regdata2_v := s; imm_v := t; p4_v := u; valid_v := v |} =>
              HMapStr [(idexe_o_mem2reg, HMapBits a); (idexe_o_wmem, HMapBits b);
                       (idexe_o_aluimm, HMapBits c); (idexe_o_slt_instr, HMapBits d);
                       (idexe_o_wreg, HMapBits e); (idexe_o_auipc, HMapBits f);
                       (idexe_o_lsb, HMapBits g); (idexe_o_lsh, HMapBits h);
                       (idexe_o_loadsignext, HMapBits j); (idexe_o_jal, HMapBits k);
                       (idexe_o_aluc, HMapBits l); (idexe_o_lt, HMapBits n);
                       (idexe_o_rd, HMapBits o); (idexe_o_pc, HMapBits p);
                       (idexe_o_regdata1, HMapBits q); (idexe_o_regdata2, HMapBits s);
                       (idexe_o_imm, HMapBits t); (idexe_o_p4, HMapBits u);
                       (idexe_o_valid, HMapBits v)]
          end;
      }.
      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.
      Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Flops.
      Proof.
        unshelve epose (trs := _ : MTrs).
        { apply Build_MTrs. 1-2: shelve. intros inputs flops.
          destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
          destruct (from_state (A := Flops) flops) as [f_format|]; [| eapply (_, _)].
          destruct i_format, f_format. eapply (_, _). }
        apply mk_MTrsOf with (mtrsof_mtrs := trs). 1-2: vm_compute; reflexivity.
        red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
        destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
          vm_compute in Htrs; injection Htrs as <- <-.
        2-4: eauto. eexists _. split; [split|].
        - eapply trsM_iff_rep_is_chain with (n := 1%nat). cbv. reflexivity.
        - vm_compute. reflexivity.
        - cbv. reflexivity.
      Defined.
    End AbsOps.
  End IDEXEReg.

  (** The repaired [store_modifier] deliberately preserves every data lane.
      Store width and byte address are interpreted by [data_mem], so the
      previous zero-extension behaviour is not part of the derived design. *)
  Module StoreModifier.
    Module M.
      Notation "'store_modifier'" := store_o_data (in custom ce_top).
      Notation "'sb'" := store_i_sb (in custom ce_expr).
      Notation "'sh'" := store_i_sh (in custom ce_expr).
      Notation "'data_in'" := store_i_data (in custom ce_expr).
      Notation "'data_out'" := store_o_data (in custom ce_expr).
      Definition m : @VModuleDecl bzeeno_vid := #[
module store_modifier
  (input logic sb, input logic sh, input logic [31:0] data_in,
   output logic [31:0] data_out);
always @* begin
  data_out = data_in;
end
endmodule].
    End M.
    Record Inputs := { sb_v : SZ; sh_v : SZ; data_v : SZ }.
    Record Outputs := { out_data_v : SZ }.
    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations. Import HMapNotations.
      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state =>
          sb_v <- sfind store_i_sb state; sh_v <- sfind store_i_sh state;
          data_v <- sfind store_i_data state;
          Sret {| sb_v := hbits sb_v; sh_v := hbits sh_v; data_v := hbits data_v |};
        to_state := fun i => match i with
          | {| sb_v := a; sh_v := b; data_v := c |} =>
              HMapStr [(store_i_sb, HMapBits a); (store_i_sh, HMapBits b);
                       (store_i_data, HMapBits c)]
          end;
      }.
      #[export] Instance outputs_structured : StructuredState Outputs := {
        from_state := fun state => out_data_v <- sfind store_o_data state;
          Sret {| out_data_v := hbits out_data_v |};
        to_state := fun o => match o with
          | {| out_data_v := a |} => HMapStr [(store_o_data, HMapBits a)]
          end;
      }.
      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.
      Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Outputs.
      Proof.
        unshelve epose (trs := _ : MTrs).
        { apply Build_MTrs. 1-2: shelve. intros inputs flops.
          destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
          destruct (from_state (A := Outputs) flops) as [f_format|]; [| eapply (_, _)].
          destruct i_format, f_format. eapply (_, _). }
        apply mk_MTrsOf with (mtrsof_mtrs := trs). 1-2: vm_compute; reflexivity.
        red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
        destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
          vm_compute in Htrs; injection Htrs as <- <-.
        2-4: eauto. eexists _. split; [split|].
        - eapply trsM_iff_rep_is_chain with (n := 1%nat). cbv. reflexivity.
        - vm_compute. reflexivity.
        - cbv. reflexivity.
      Defined.
    End AbsOps.
  End StoreModifier.

  (** Immediate decoder for the RV32I instruction formats used by the core.
      The [casex] source is retained: for concrete two-state opcode inputs it
      has the same cases as a conventional [case]. *)
  Module ImmDecode.
    Module M.
      Notation "'imm_decode'" := imm_o_value (in custom ce_top).
      Notation "'i_instr'" := imm_i_instr (in custom ce_expr).
      Notation "'i_opcode'" := imm_i_opcode (in custom ce_expr).
      Notation "'i_signext'" := imm_i_signext (in custom ce_expr).
      Notation "'o_imm_val'" := imm_o_value (in custom ce_expr).
      Definition m : @VModuleDecl bzeeno_vid := #[
module imm_decode
  (input logic [31:0] i_instr, input logic [6:0] i_opcode,
   input logic i_signext, output logic [31:0] o_imm_val);
always @*
casex (i_opcode)
  7'b0000011: o_imm_val <= {{20{i_instr[31] & i_signext}}, i_instr[31:20]};
  7'b0100011: o_imm_val <= {{20{i_instr[31] & i_signext}}, i_instr[31:25], i_instr[11:7]};
  7'b1101111: o_imm_val <= {{12{i_instr[31] & i_signext}}, i_instr[19:12], i_instr[20], i_instr[30:21], 1'b0};
  7'b1100111: o_imm_val <= {{20{i_instr[31] & i_signext}}, i_instr[31:20]};
  7'b1100011: o_imm_val <= {{20{i_instr[31] & i_signext}}, i_instr[7], i_instr[30:25], i_instr[11:8], {1{1'b0}}};
  7'b0110111: o_imm_val <= {i_instr[31:12], {12{1'b0}}};
  7'b0010011: begin
    if (i_instr[14:12] == 3'b001 | i_instr[14:12] == 3'b101)
      o_imm_val <= {{27{1'b0}}, i_instr[24:20]};
    else o_imm_val <= {{20{i_instr[31] & i_signext}}, i_instr[31:20]};
  end
  (** The source drives X for an unsupported opcode.  VerilRocq's value
      domain is two-state, so the imported RV32I-valid-input model uses zero
      there; the later ISA invariant excludes this branch. *)
  default: o_imm_val <= 'b0;
endcase
endmodule].
    End M.
    Record Inputs := { instr_v : SZ; opcode_v : SZ; signext_v : SZ }.
    Record Outputs := { value_v : SZ }.
    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations. Import HMapNotations.
      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state =>
          instr_v <- sfind imm_i_instr state; opcode_v <- sfind imm_i_opcode state;
          signext_v <- sfind imm_i_signext state;
          Sret {| instr_v := hbits instr_v; opcode_v := hbits opcode_v;
                  signext_v := hbits signext_v |};
        to_state := fun i => match i with
          | {| instr_v := a; opcode_v := b; signext_v := c |} =>
              HMapStr [(imm_i_instr, HMapBits a); (imm_i_opcode, HMapBits b);
                       (imm_i_signext, HMapBits c)]
          end;
      }.
      #[export] Instance outputs_structured : StructuredState Outputs := {
        from_state := fun state => value_v <- sfind imm_o_value state;
          Sret {| value_v := hbits value_v |};
        to_state := fun o => match o with
          | {| value_v := a |} => HMapStr [(imm_o_value, HMapBits a)]
          end;
      }.
      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.
      Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Outputs.
      Proof.
        unshelve epose (trs := _ : MTrs).
        { apply Build_MTrs. 1-2: shelve. intros inputs flops.
          destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
          destruct (from_state (A := Outputs) flops) as [f_format|]; [| eapply (_, _)].
          destruct i_format, f_format. eapply (_, _). }
        apply mk_MTrsOf with (mtrsof_mtrs := trs). 1-2: vm_compute; reflexivity.
        red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
        destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
          vm_compute in Htrs; injection Htrs as <- <-.
        2-4: eauto. eexists _. split; [split|].
        - eapply trsM_iff_rep_is_chain with (n := 1%nat). cbv. reflexivity.
        - vm_compute. reflexivity.
        - cbv. reflexivity.
      Defined.
    End AbsOps.
  End ImmDecode.

  (** A semantic lowering of [Comparator/comparator.v].  The source builds a
      32-bit ripple comparator from [comparator_1bit] generate instances, then
      implements signed comparison by sign/magnitude cases.  Generate loops
      are outside the executable AST subset, so this AST states the resulting
      two-state combinational function directly.  It is intentionally kept as
      a separate proof obligation to connect this lowering to the raw netlist. *)
  Module Comparator.
    Module M.
      Notation "'comparator'" := cmp_o_lt (in custom ce_top).
      Notation "'a'" := cmp_i_a (in custom ce_expr).
      Notation "'b'" := cmp_i_b (in custom ce_expr).
      Notation "'unsigned_op'" := cmp_i_unsigned (in custom ce_expr).
      Notation "'o_a_lt_b'" := cmp_o_lt (in custom ce_expr).
      Notation "'o_a_eq_b'" := cmp_o_eq (in custom ce_expr).
      Definition m : @VModuleDecl bzeeno_vid := #[
module comparator
  (input logic [31:0] a, input logic [31:0] b, input logic unsigned_op,
   output logic o_a_lt_b, output logic o_a_eq_b);
assign o_a_lt_b = unsigned_op ? (a < b) : ($signed(a) < $signed(b));
assign o_a_eq_b = (a == b);
endmodule].
    End M.
    Record Inputs := { a_v : SZ; b_v : SZ; unsigned_v : SZ }.
    Record Outputs := { lt_v : SZ; eq_v : SZ }.
    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations. Import HMapNotations.
      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state =>
          a_v <- sfind cmp_i_a state; b_v <- sfind cmp_i_b state;
          unsigned_v <- sfind cmp_i_unsigned state;
          Sret {| a_v := hbits a_v; b_v := hbits b_v; unsigned_v := hbits unsigned_v |};
        to_state := fun i => match i with
          | {| a_v := a; b_v := b; unsigned_v := u |} =>
              HMapStr [(cmp_i_a, HMapBits a); (cmp_i_b, HMapBits b);
                       (cmp_i_unsigned, HMapBits u)]
          end;
      }.
      #[export] Instance outputs_structured : StructuredState Outputs := {
        from_state := fun state =>
          lt_v <- sfind cmp_o_lt state; eq_v <- sfind cmp_o_eq state;
          Sret {| lt_v := hbits lt_v; eq_v := hbits eq_v |};
        to_state := fun o => match o with
          | {| lt_v := a; eq_v := b |} =>
              HMapStr [(cmp_o_lt, HMapBits a); (cmp_o_eq, HMapBits b)]
          end;
      }.
      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.
      Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Outputs.
      Proof.
        unshelve epose (trs := _ : MTrs).
        { apply Build_MTrs. 1-2: shelve. intros inputs flops.
          destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
          destruct (from_state (A := Outputs) flops) as [f_format|]; [| eapply (_, _)].
          destruct i_format, f_format. eapply (_, _). }
        apply mk_MTrsOf with (mtrsof_mtrs := trs). 1-2: vm_compute; reflexivity.
        red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
        destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
          vm_compute in Htrs; injection Htrs as <- <-.
        2-4: eauto. eexists _. split; [split|].
        - eapply trsM_iff_rep_is_chain with (n := 1%nat). cbv. reflexivity.
        - vm_compute. reflexivity.
        - cbv. reflexivity.
      Defined.
    End AbsOps.
  End Comparator.

  (** RV32I-relevant semantic lowering of [ALU/alu.v], [add_sub32.v], and
      [shifter.v].  The source's CLA hierarchy implements modular addition;
      the cases below retain the selected add/sub, bitwise, and shift paths.
      The raw mux has X-valued unconnected choices for unsupported controls;
      the imported two-state model maps precisely those excluded choices to 0. *)
  Module ALU.
    Module M.
      Notation "'alu'" := alu_o_result (in custom ce_top).
      Notation "'a'" := alu_i_a (in custom ce_expr).
      Notation "'b'" := alu_i_b (in custom ce_expr).
      Notation "'aluc'" := alu_i_aluc (in custom ce_expr).
      Notation "'result'" := alu_o_result (in custom ce_expr).
      Definition m : @VModuleDecl bzeeno_vid := #[
module alu
  (input logic [31:0] a, input logic [31:0] b, input logic [5:0] aluc,
   output logic [31:0] result);
always @* begin
  case (aluc[2:0])
    3'b000: result = aluc[3] ? (a - b) : (a + b);
    3'b010: result = aluc[3] ? (a | b) : (a & b);
    3'b100: result = aluc[3] ? b : (a ^ b);
    3'b101: begin
      if (!aluc[3]) result = a << b[4:0];
      else if (!aluc[4]) result = a >> b[4:0];
      else result = $signed(a) >>> b[4:0];
    end
    default: result = 'b0;
  endcase
end
endmodule].
    End M.
    Record Inputs := { a_v : SZ; b_v : SZ; aluc_v : SZ }.
    Record Outputs := { result_v : SZ }.
    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations. Import HMapNotations.
      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state =>
          a_v <- sfind alu_i_a state; b_v <- sfind alu_i_b state; aluc_v <- sfind alu_i_aluc state;
          Sret {| a_v := hbits a_v; b_v := hbits b_v; aluc_v := hbits aluc_v |};
        to_state := fun i => match i with
          | {| a_v := a; b_v := b; aluc_v := c |} =>
              HMapStr [(alu_i_a, HMapBits a); (alu_i_b, HMapBits b); (alu_i_aluc, HMapBits c)]
          end;
      }.
      #[export] Instance outputs_structured : StructuredState Outputs := {
        from_state := fun state => result_v <- sfind alu_o_result state;
          Sret {| result_v := hbits result_v |};
        to_state := fun o => match o with
          | {| result_v := a |} => HMapStr [(alu_o_result, HMapBits a)]
          end;
      }.
      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.
      Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Outputs.
      Proof.
        unshelve epose (trs := _ : MTrs).
        { apply Build_MTrs. 1-2: shelve. intros inputs flops.
          destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
          destruct (from_state (A := Outputs) flops) as [f_format|]; [| eapply (_, _)].
          destruct i_format, f_format. eapply (_, _). }
        apply mk_MTrsOf with (mtrsof_mtrs := trs). 1-2: vm_compute; reflexivity.
        red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
        destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
          vm_compute in Htrs; injection Htrs as <- <-.
        2-4: eauto. eexists _. split; [split|].
        - eapply trsM_iff_rep_is_chain with (n := 1%nat). cbv. reflexivity.
        - vm_compute. reflexivity.
        - cbv. reflexivity.
      Defined.
    End AbsOps.
  End ALU.

  (** Register file lowered from [Core/regfile.v].  The RTL writes on the
      inverted core clock; the top-level clock abstraction will account for
      that phase separation.  At this module boundary, each transition is one
      write opportunity followed by combinational reads. *)
  Module RegFile.
    Module M.
      Notation "'regfile'" := rf_array (in custom ce_top).
      Notation "'clk'" := rf_clk (in custom ce_expr).
      Notation "'resetn'" := rf_resetn (in custom ce_expr).
      Notation "'rs1'" := rf_rs1 (in custom ce_expr).
      Notation "'rs2'" := rf_rs2 (in custom ce_expr).
      Notation "'rd'" := rf_rd (in custom ce_expr).
      Notation "'reg_write'" := rf_reg_write (in custom ce_expr).
      Notation "'write_data'" := rf_write_data (in custom ce_expr).
      Notation "'read_data1'" := rf_read_data1 (in custom ce_expr).
      Notation "'read_data2'" := rf_read_data2 (in custom ce_expr).
      Notation "'reg_file'" := rf_array (in custom ce_expr).
      Definition m : @VModuleDecl bzeeno_vid := #[
module regfile
  (input logic clk, input logic resetn, input logic [4:0] rs1,
   input logic [4:0] rs2, input logic [4:0] rd, input logic reg_write,
   input logic [31:0] write_data, output logic [31:0] read_data1,
   output logic [31:0] read_data2);
logic [31:0][31:0] reg_file;
always @(posedge clk or negedge resetn) begin
  if (!resetn) reg_file <= {'d0};
  else if (reg_write & (rd != 0)) reg_file[rd] <= write_data;
end
assign read_data1 = (rs1 == 0) ? 'd0 : reg_file[rs1];
assign read_data2 = (rs2 == 0) ? 'd0 : reg_file[rs2];
endmodule].
    End M.
    Record Inputs := {
      resetn_v : SZ; rs1_v : SZ; rs2_v : SZ; rd_v : SZ;
      write_v : SZ; write_data_v : SZ;
    }.
    Record Flops := { regs_v : list (Z * Value) }.
    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations. Import HMapNotations.
      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state =>
          resetn_v <- sfind rf_resetn state; rs1_v <- sfind rf_rs1 state;
          rs2_v <- sfind rf_rs2 state; rd_v <- sfind rf_rd state;
          write_v <- sfind rf_reg_write state; write_data_v <- sfind rf_write_data state;
          Sret {| resetn_v := hbits resetn_v; rs1_v := hbits rs1_v; rs2_v := hbits rs2_v;
                  rd_v := hbits rd_v; write_v := hbits write_v;
                  write_data_v := hbits write_data_v |};
        to_state := fun i => match i with
          | {| resetn_v := a; rs1_v := b; rs2_v := c; rd_v := d;
               write_v := e; write_data_v := f |} =>
              HMapStr [(rf_resetn, HMapBits a); (rf_rs1, HMapBits b);
                       (rf_rs2, HMapBits c); (rf_rd, HMapBits d);
                       (rf_reg_write, HMapBits e); (rf_write_data, HMapBits f)]
          end;
      }.
      #[export] Instance flops_structured : StructuredState Flops := {
        from_state := fun state => regs_v <- sfind rf_array state;
          Sret {| regs_v := harr regs_v |};
        to_state := fun f => match f with
          | {| regs_v := a |} => HMapStr [(rf_array, HMapArr a)]
          end;
      }.
      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.
      Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Flops.
      Proof.
        unshelve epose (trs := _ : MTrs).
        { apply Build_MTrs. 1-2: shelve. intros inputs flops.
          destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
          destruct (from_state (A := Flops) flops) as [f_format|]; [| eapply (_, _)].
          destruct i_format, f_format. eapply (_, _). }
        apply mk_MTrsOf with (mtrsof_mtrs := trs). 1-2: vm_compute; reflexivity.
        red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
        destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
          vm_compute in Htrs; injection Htrs as <- <-.
        2-4: eauto. eexists _. split; [split|].
        - eapply trsM_iff_rep_is_chain with (n := 2%nat). vm_compute. reflexivity.
        - vm_compute. reflexivity.
        - vm_compute. reflexivity.
      Defined.
    End AbsOps.
  End RegFile.

  (** Byte-addressed data memory from the repaired derived RTL.  Its Verilog
      [initial] zeroing is deliberately not in the transition AST: memory
      contents belong to the initial-state relation of the eventual theorem. *)
  Module DataMem.
    Module M.
      Notation "'data_mem'" := dmem_ram (in custom ce_top).
      Notation "'i_clk'" := dmem_i_clk (in custom ce_expr).
      Notation "'we'" := dmem_i_we (in custom ce_expr).
      Notation "'i_sb'" := dmem_i_sb (in custom ce_expr).
      Notation "'i_sh'" := dmem_i_sh (in custom ce_expr).
      Notation "'i_data'" := dmem_i_data (in custom ce_expr).
      Notation "'i_addr'" := dmem_i_addr (in custom ce_expr).
      Notation "'o_data'" := dmem_o_data (in custom ce_expr).
      Notation "'ram'" := dmem_ram (in custom ce_expr).
      Definition m : @VModuleDecl bzeeno_vid := #[
module data_mem
  (input logic i_clk, input logic we, input logic i_sb, input logic i_sh,
   input logic [31:0] i_data, input logic [31:0] i_addr,
   output logic [31:0] o_data);
logic [127:0][7:0] ram;
always @(posedge i_clk) begin
  if (we)
    if (i_sb) ram[i_addr[6:0]] <= i_data[7:0];
    else if (i_sh) begin
      ram[i_addr & 32'd126] <= i_data[7:0];
      ram[(i_addr & 32'd126) + 32'd1] <= i_data[15:8];
    end
    else begin
      ram[i_addr & 32'd124] <= i_data[7:0];
      ram[(i_addr & 32'd124) + 32'd1] <= i_data[15:8];
      ram[(i_addr & 32'd124) + 32'd2] <= i_data[23:16];
      ram[(i_addr & 32'd124) + 32'd3] <= i_data[31:24];
    end
end
assign o_data = {ram[(i_addr & 32'd124) + 32'd3],
                 ram[(i_addr & 32'd124) + 32'd2],
                 ram[(i_addr & 32'd124) + 32'd1], ram[i_addr & 32'd124]};
endmodule].
    End M.
    Record Inputs := { we_v : SZ; sb_v : SZ; sh_v : SZ; data_v : SZ; addr_v : SZ }.
    Record Flops := { ram_v : list (Z * Value) }.
    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations. Import HMapNotations.
      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state =>
          we_v <- sfind dmem_i_we state; sb_v <- sfind dmem_i_sb state;
          sh_v <- sfind dmem_i_sh state; data_v <- sfind dmem_i_data state;
          addr_v <- sfind dmem_i_addr state;
          Sret {| we_v := hbits we_v; sb_v := hbits sb_v; sh_v := hbits sh_v;
                  data_v := hbits data_v; addr_v := hbits addr_v |};
        to_state := fun i => match i with
          | {| we_v := a; sb_v := b; sh_v := c; data_v := d; addr_v := e |} =>
              HMapStr [(dmem_i_we, HMapBits a); (dmem_i_sb, HMapBits b);
                       (dmem_i_sh, HMapBits c); (dmem_i_data, HMapBits d);
                       (dmem_i_addr, HMapBits e)]
          end;
      }.
      #[export] Instance flops_structured : StructuredState Flops := {
        from_state := fun state => ram_v <- sfind dmem_ram state;
          Sret {| ram_v := harr ram_v |};
        to_state := fun f => match f with
          | {| ram_v := a |} => HMapStr [(dmem_ram, HMapArr a)]
          end;
      }.
      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.
      Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Flops.
      Proof.
        unshelve epose (trs := _ : MTrs).
        { apply Build_MTrs. 1-2: shelve. intros inputs flops.
          destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
          destruct (from_state (A := Flops) flops) as [f_format|]; [| eapply (_, _)].
          destruct i_format, f_format. eapply (_, _). }
        apply mk_MTrsOf with (mtrsof_mtrs := trs). 1-2: vm_compute; reflexivity.
        red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
        destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
          vm_compute in Htrs; injection Htrs as <- <-.
        2-4: eauto. eexists _. split; [split|].
        - eapply trsM_iff_rep_is_chain with (n := 2%nat). vm_compute. reflexivity.
        - vm_compute. reflexivity.
        - vm_compute. reflexivity.
      Defined.
    End AbsOps.
  End DataMem.

  (** Read-only instruction memory.  The external [test_program.mem] file is
      an initial ROM interpretation, not a transition; [rom_v] makes that
      interpretation an explicit parameter of any whole-core theorem. *)
  Module InstructionMem.
    Module M.
      Notation "'instruction_mem'" := imem_rom (in custom ce_top).
      Notation "'i_addr'" := imem_i_addr (in custom ce_expr).
      Notation "'o_instr'" := imem_o_instr (in custom ce_expr).
      Notation "'rom'" := imem_rom (in custom ce_expr).
      Definition m : @VModuleDecl bzeeno_vid := #[
module instruction_mem
  (input logic [31:0] i_addr, output logic [31:0] o_instr);
logic [100:0][31:0] rom;
assign o_instr = rom[i_addr[31:2]];
endmodule].
    End M.
    Record Inputs := { addr_v : SZ }.
    Record Flops := { rom_v : list (Z * Value) }.
    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations. Import HMapNotations.
      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state => addr_v <- sfind imem_i_addr state;
          Sret {| addr_v := hbits addr_v |};
        to_state := fun i => match i with
          | {| addr_v := a |} => HMapStr [(imem_i_addr, HMapBits a)]
          end;
      }.
      #[export] Instance flops_structured : StructuredState Flops := {
        from_state := fun state => rom_v <- sfind imem_rom state;
          Sret {| rom_v := harr rom_v |};
        to_state := fun f => match f with
          | {| rom_v := a |} => HMapStr [(imem_rom, HMapArr a)]
          end;
      }.
      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.
      Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Flops.
      Proof.
        unshelve epose (trs := _ : MTrs).
        { apply Build_MTrs. 1-2: shelve. intros inputs flops.
          destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
          destruct (from_state (A := Flops) flops) as [f_format|]; [| eapply (_, _)].
          destruct i_format, f_format. eapply (_, _). }
        apply mk_MTrsOf with (mtrsof_mtrs := trs). 1-2: vm_compute; reflexivity.
        red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
        destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
          vm_compute in Htrs; injection Htrs as <- <-.
        2-4: eauto. eexists _. split; [split|].
        - eapply trsM_iff_rep_is_chain with (n := 1%nat). cbv. reflexivity.
        - vm_compute. reflexivity.
        - cbv. reflexivity.
      Defined.
    End AbsOps.
  End InstructionMem.

  (** Byte/halfword load-data formatter from the repaired external core. *)
  Module LoadModifier.
    Module M.
      Notation "'load_modifier'" := load_o_data (in custom ce_top).
      Notation "'lb'" := load_i_lb (in custom ce_expr).
      Notation "'lh'" := load_i_lh (in custom ce_expr).
      Notation "'load_signext'" := load_i_signext (in custom ce_expr).
      Notation "'byte_offset'" := load_i_offset (in custom ce_expr).
      Notation "'data_in'" := load_i_data (in custom ce_expr).
      Notation "'data_out'" := load_o_data (in custom ce_expr).
      Definition m : @VModuleDecl bzeeno_vid := #[
module load_modifier
  (input logic lb, input logic lh, input logic load_signext,
   input logic [1:0] byte_offset, input logic [31:0] data_in,
   output logic [31:0] data_out);
always @* begin
  if (!lb & !lh) data_out = data_in;
  else if (lb & !lh & load_signext) begin
    case (byte_offset)
      2'b00: data_out = {{24{data_in[7]}}, data_in[7:0]};
      2'b01: data_out = {{24{data_in[15]}}, data_in[15:8]};
      2'b10: data_out = {{24{data_in[23]}}, data_in[23:16]};
      default: data_out = {{24{data_in[31]}}, data_in[31:24]};
    endcase
  end
  else if (!lb & lh & load_signext) data_out = byte_offset[1] ? {{16{data_in[31]}}, data_in[31:16]} : {{16{data_in[15]}}, data_in[15:0]};
  else if (lb & !lh & !load_signext) begin
    case (byte_offset)
      2'b00: data_out = {{24{1'b0}}, data_in[7:0]};
      2'b01: data_out = {{24{1'b0}}, data_in[15:8]};
      2'b10: data_out = {{24{1'b0}}, data_in[23:16]};
      default: data_out = {{24{1'b0}}, data_in[31:24]};
    endcase
  end
  else if (!lb & lh & !load_signext) data_out = byte_offset[1] ? {{16{1'b0}}, data_in[31:16]} : {{16{1'b0}}, data_in[15:0]};
  else data_out = data_in;
end
endmodule].
    End M.
    Record Inputs := { lb_v : SZ; lh_v : SZ; signext_v : SZ; offset_v : SZ; data_v : SZ }.
    Record Outputs := { out_data_v : SZ }.
    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations. Import HMapNotations.
      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state =>
          lb_v <- sfind load_i_lb state; lh_v <- sfind load_i_lh state;
          signext_v <- sfind load_i_signext state; offset_v <- sfind load_i_offset state;
          data_v <- sfind load_i_data state;
          Sret {| lb_v := hbits lb_v; lh_v := hbits lh_v; signext_v := hbits signext_v;
                  offset_v := hbits offset_v; data_v := hbits data_v |};
        to_state := fun i => match i with
          | {| lb_v := a; lh_v := b; signext_v := c; offset_v := d; data_v := e |} =>
              HMapStr [(load_i_lb, HMapBits a); (load_i_lh, HMapBits b);
                       (load_i_signext, HMapBits c); (load_i_offset, HMapBits d);
                       (load_i_data, HMapBits e)]
          end;
      }.
      #[export] Instance outputs_structured : StructuredState Outputs := {
        from_state := fun state => out_data_v <- sfind load_o_data state;
          Sret {| out_data_v := hbits out_data_v |};
        to_state := fun o => match o with
          | {| out_data_v := a |} => HMapStr [(load_o_data, HMapBits a)]
          end;
      }.
      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.
      Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Outputs.
      Proof.
        unshelve epose (trs := _ : MTrs).
        { apply Build_MTrs. 1-2: shelve. intros inputs flops.
          destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
          destruct (from_state (A := Outputs) flops) as [f_format|]; [| eapply (_, _)].
          destruct i_format, f_format. eapply (_, _). }
        apply mk_MTrsOf with (mtrsof_mtrs := trs). 1-2: vm_compute; reflexivity.
        red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
        destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
          vm_compute in Htrs; injection Htrs as <- <-.
        2-4: eauto. eexists _. split; [split|].
        - eapply trsM_iff_rep_is_chain with (n := 2%nat). vm_compute. reflexivity.
        - vm_compute. reflexivity.
        - vm_compute. reflexivity.
      Defined.
    End AbsOps.
  End LoadModifier.

  (** Fixed 32-bit instances of the 3:1 and 4:1 muxes used in [core.v]. *)
  Module Mux3.
    Module M.
      Notation "'mux_3to1'" := mux3_o_data (in custom ce_top).
      Notation "'inputA'" := mux3_i_a (in custom ce_expr).
      Notation "'inputB'" := mux3_i_b (in custom ce_expr).
      Notation "'inputC'" := mux3_i_c (in custom ce_expr).
      Notation "'select'" := mux3_i_select (in custom ce_expr).
      Notation "'selected_out'" := mux3_o_data (in custom ce_expr).
      Definition m : @VModuleDecl bzeeno_vid := #[
module mux_3to1
  (input logic [31:0] inputA, input logic [31:0] inputB,
   input logic [31:0] inputC, input logic [1:0] select,
   output logic [31:0] selected_out);
always @* begin
  case (select)
    2'b00: selected_out = inputA;
    2'b01: selected_out = inputB;
    2'b10: selected_out = inputC;
    default: selected_out = 'b0;
  endcase
end
endmodule].
    End M.
    Record Inputs := { a_v : SZ; b_v : SZ; c_v : SZ; select_v : SZ }.
    Record Outputs := { out_v : SZ }.
    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations. Import HMapNotations.
      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state =>
          a_v <- sfind mux3_i_a state; b_v <- sfind mux3_i_b state;
          c_v <- sfind mux3_i_c state; select_v <- sfind mux3_i_select state;
          Sret {| a_v := hbits a_v; b_v := hbits b_v; c_v := hbits c_v; select_v := hbits select_v |};
        to_state := fun i => match i with
          | {| a_v := a; b_v := b; c_v := c; select_v := d |} =>
              HMapStr [(mux3_i_a,HMapBits a);(mux3_i_b,HMapBits b);(mux3_i_c,HMapBits c);(mux3_i_select,HMapBits d)]
          end;
      }.
      #[export] Instance outputs_structured : StructuredState Outputs := {
        from_state := fun state => out_v <- sfind mux3_o_data state; Sret {| out_v := hbits out_v |};
        to_state := fun o => match o with {| out_v := a |} => HMapStr [(mux3_o_data,HMapBits a)] end;
      }.
      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.
      Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Outputs.
      Proof.
        unshelve epose (trs := _ : MTrs).
        { apply Build_MTrs. 1-2: shelve. intros inputs flops.
          destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
          destruct (from_state (A := Outputs) flops) as [f_format|]; [| eapply (_, _)].
          destruct i_format, f_format. eapply (_, _). }
        apply mk_MTrsOf with (mtrsof_mtrs := trs). 1-2: vm_compute; reflexivity.
        red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
        destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
          vm_compute in Htrs; injection Htrs as <- <-.
        2-4: eauto. eexists _. split; [split|].
        - eapply trsM_iff_rep_is_chain with (n := 2%nat). vm_compute. reflexivity.
        - vm_compute. reflexivity.
        - vm_compute. reflexivity.
      Defined.
    End AbsOps.
  End Mux3.

  Module Mux4.
    Module M.
      Notation "'mux_4to1'" := mux4_o_data (in custom ce_top).
      Notation "'inputA'" := mux4_i_a (in custom ce_expr).
      Notation "'inputB'" := mux4_i_b (in custom ce_expr).
      Notation "'inputC'" := mux4_i_c (in custom ce_expr).
      Notation "'inputD'" := mux4_i_d (in custom ce_expr).
      Notation "'select'" := mux4_i_select (in custom ce_expr).
      Notation "'selected_out'" := mux4_o_data (in custom ce_expr).
      Definition m : @VModuleDecl bzeeno_vid := #[
module mux_4to1
  (input logic [31:0] inputA, input logic [31:0] inputB,
   input logic [31:0] inputC, input logic [31:0] inputD,
   input logic [1:0] select, output logic [31:0] selected_out);
always @* begin
  case (select)
    2'b00: selected_out = inputA;
    2'b01: selected_out = inputB;
    2'b10: selected_out = inputC;
    2'b11: selected_out = inputD;
    default: selected_out = 'b0;
  endcase
end
endmodule].
    End M.
    Record Inputs := { a_v : SZ; b_v : SZ; c_v : SZ; d_v : SZ; select_v : SZ }.
    Record Outputs := { out_v : SZ }.
    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations. Import HMapNotations.
      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state =>
          a_v <- sfind mux4_i_a state; b_v <- sfind mux4_i_b state; c_v <- sfind mux4_i_c state;
          d_v <- sfind mux4_i_d state; select_v <- sfind mux4_i_select state;
          Sret {| a_v := hbits a_v; b_v := hbits b_v; c_v := hbits c_v; d_v := hbits d_v; select_v := hbits select_v |};
        to_state := fun i => match i with
          | {| a_v := a; b_v := b; c_v := c; d_v := d; select_v := e |} =>
              HMapStr [(mux4_i_a,HMapBits a);(mux4_i_b,HMapBits b);(mux4_i_c,HMapBits c);(mux4_i_d,HMapBits d);(mux4_i_select,HMapBits e)]
          end;
      }.
      #[export] Instance outputs_structured : StructuredState Outputs := {
        from_state := fun state => out_v <- sfind mux4_o_data state; Sret {| out_v := hbits out_v |};
        to_state := fun o => match o with {| out_v := a |} => HMapStr [(mux4_o_data,HMapBits a)] end;
      }.
      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.
      Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Outputs.
      Proof.
        unshelve epose (trs := _ : MTrs).
        { apply Build_MTrs. 1-2: shelve. intros inputs flops.
          destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
          destruct (from_state (A := Outputs) flops) as [f_format|]; [| eapply (_, _)].
          destruct i_format, f_format. eapply (_, _). }
        apply mk_MTrsOf with (mtrsof_mtrs := trs). 1-2: vm_compute; reflexivity.
        red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
        destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
          vm_compute in Htrs; injection Htrs as <- <-.
        2-4: eauto. eexists _. split; [split|].
        - eapply trsM_iff_rep_is_chain with (n := 2%nat). vm_compute. reflexivity.
        - vm_compute. reflexivity.
        - vm_compute. reflexivity.
      Defined.
    End AbsOps.
  End Mux4.

  (** Semantic lowering of the [cla_32bit] hierarchy used three times by
      [core.v].  Its 4/8/16-bit carry-lookahead submodules implement this
      33-bit addition exactly; the normalized AST avoids unsupported nested
      parameterized instances while retaining both observable outputs. *)
  Module CLA32.
    Module M.
      Notation "'cla_32bit'" := cla_o_sum (in custom ce_top).
      Notation "'a'" := cla_i_a (in custom ce_expr).
      Notation "'b'" := cla_i_b (in custom ce_expr).
      Notation "'c_in'" := cla_i_cin (in custom ce_expr).
      Notation "'sum'" := cla_o_sum (in custom ce_expr).
      Notation "'c_out'" := cla_o_cout (in custom ce_expr).
      Notation "'total'" := cla_total (in custom ce_expr).
      Definition m : @VModuleDecl bzeeno_vid := #[
module cla_32bit
  (input logic [31:0] a, input logic [31:0] b, input logic c_in,
   output logic [31:0] sum, output logic c_out);
logic [32:0] total;
assign total = {1'b0, a} + {1'b0, b} + c_in;
assign sum = total[31:0];
assign c_out = total[32];
endmodule].
    End M.
    Record Inputs := { a_v : SZ; b_v : SZ; cin_v : SZ }.
    Record Outputs := { sum_v : SZ; cout_v : SZ }.
    Section AbsOps.
      Context `{sz_ops} `{array_ops hmap}.
      Import ListNotations. Import HMapNotations.
      #[export] Instance inputs_structured : StructuredState Inputs := {
        from_state := fun state => a_v <- sfind cla_i_a state; b_v <- sfind cla_i_b state; cin_v <- sfind cla_i_cin state;
          Sret {| a_v := hbits a_v; b_v := hbits b_v; cin_v := hbits cin_v |};
        to_state := fun i => match i with {| a_v := a; b_v := b; cin_v := c |} => HMapStr [(cla_i_a,HMapBits a);(cla_i_b,HMapBits b);(cla_i_cin,HMapBits c)] end;
      }.
      #[export] Instance outputs_structured : StructuredState Outputs := {
        from_state := fun state => sum_v <- sfind cla_o_sum state; cout_v <- sfind cla_o_cout state;
          Sret {| sum_v := hbits sum_v; cout_v := hbits cout_v |};
        to_state := fun o => match o with {| sum_v := a; cout_v := b |} => HMapStr [(cla_o_sum,HMapBits a);(cla_o_cout,HMapBits b)] end;
      }.
      Definition etrs (_ : bzeeno_vid) : trsOk MTrs := Fail TrsUndeclared.
      Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Outputs.
      Proof.
        unshelve epose (trs := _ : MTrs).
        { apply Build_MTrs. 1-2: shelve. intros inputs flops.
          destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
          destruct (from_state (A := Outputs) flops) as [f_format|]; [| eapply (_, _)].
          destruct i_format, f_format. eapply (_, _). }
        apply mk_MTrsOf with (mtrsof_mtrs := trs). 1-2: vm_compute; reflexivity.
        red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
        destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
          vm_compute in Htrs; injection Htrs as <- <-.
        2-4: eauto. eexists _. split; [split|].
        - eapply trsM_iff_rep_is_chain with (n := 2%nat). vm_compute. reflexivity.
        - vm_compute. reflexivity.
        - vm_compute. reflexivity.
      Defined.
    End AbsOps.
  End CLA32.
End BzeenoPipeline.
