(** Literal structural AST of the repaired bzeeno [CPU/Core/core.v].

    The direct children are all registered in [BzeenoCore.etrs].  The added
    commit ports are observational only: [commit_vld] and [commit_pc] expose
    the MEM/WB valid/PC state without changing the original datapath.
 *)
Require Import Coq.ZArith.BinInt Coq.Lists.List.
Require Import Lib.Lib. Import SZNotations.
Require Import Lang.Lang.
Require Import Ex.External.BzeenoPipeline Ex.External.BzeenoControl Ex.External.BzeenoCore.
Require Import Ex.External.BzeenoTopState.

#[local] Existing Instance bzeeno_vid_t_c.
#[local] Existing Instance bzeeno_vid_ops.
#[local] Existing Instance BzeenoTopState.inputs_structured.
#[local] Existing Instance BzeenoTopState.flops_structured.

Module BzeenoFullCore.
  Module M.
    (* Top-level names and every local net in [core.v]. *)
    Notation "'core'" := bcore_top (in custom ce_top).
    Notation "'i_clk'" := bcore_clk (in custom ce_expr).
    Notation "'i_resetn'" := bcore_resetn (in custom ce_expr).
    Notation "'i_instr'" := bcore_instr (in custom ce_expr).
    Notation "'i_dmem'" := bcore_dmem (in custom ce_expr).
    Notation "'o_pc'" := bcore_o_pc (in custom ce_expr).
    Notation "'o_addr'" := bcore_o_addr (in custom ce_expr).
    Notation "'o_dmem'" := bcore_o_dmem (in custom ce_expr).
    Notation "'o_wmem'" := bcore_o_wmem (in custom ce_expr).
    Notation "'o_sb'" := bcore_o_sb (in custom ce_expr).
    Notation "'o_sh'" := bcore_o_sh (in custom ce_expr).
    Notation "'o_commit_vld'" := bcore_o_commit_vld (in custom ce_expr).
    Notation "'o_commit_pc'" := bcore_o_commit_pc (in custom ce_expr).
    Notation "'pc_next'" := bcore_pc_next (in custom ce_expr).
    Notation "'if_pc'" := bcore_if_pc (in custom ce_expr).
    Notation "'if_p4'" := bcore_if_p4 (in custom ce_expr).
    Notation "'id_instr'" := bcore_id_instr (in custom ce_expr).
    Notation "'id_valid'" := bcore_id_valid (in custom ce_expr).
    Notation "'imm_val'" := bcore_imm_val (in custom ce_expr).
    Notation "'opcode'" := bcore_opcode (in custom ce_expr).
    Notation "'rd'" := bcore_rd (in custom ce_expr).
    Notation "'rs1'" := bcore_rs1 (in custom ce_expr).
    Notation "'rs2'" := bcore_rs2 (in custom ce_expr).
    Notation "'funct3'" := bcore_funct3 (in custom ce_expr).
    Notation "'funct7'" := bcore_funct7 (in custom ce_expr).
    Notation "'id_pc'" := bcore_id_pc (in custom ce_expr).
    Notation "'id_p4'" := bcore_id_p4 (in custom ce_expr).
    Notation "'jalr_branch_inputb'" := bcore_jalr_inputb (in custom ce_expr).
    Notation "'jal_pc'" := bcore_jal_pc (in custom ce_expr).
    Notation "'jalr_branch_pc_raw'" := bcore_jalr_pc_raw (in custom ce_expr).
    Notation "'jalr_branch_pc'" := bcore_jalr_pc (in custom ce_expr).
    Notation "'compare_inputb'" := bcore_compare_inputb (in custom ce_expr).
    Notation "'fwda'" := bcore_fwda (in custom ce_expr).
    Notation "'fwdb'" := bcore_fwdb (in custom ce_expr).
    Notation "'aluc'" := bcore_aluc (in custom ce_expr).
    Notation "'id_regdata1'" := bcore_id_regdata1 (in custom ce_expr).
    Notation "'id_regdata2'" := bcore_id_regdata2 (in custom ce_expr).
    Notation "'pcsrc'" := bcore_pcsrc (in custom ce_expr).
    Notation "'mem2reg'" := bcore_mem2reg (in custom ce_expr).
    Notation "'wmem'" := bcore_wmem (in custom ce_expr).
    Notation "'aluimm'" := bcore_aluimm (in custom ce_expr).
    Notation "'wreg'" := bcore_wreg (in custom ce_expr).
    Notation "'jal'" := bcore_jal (in custom ce_expr).
    Notation "'jalr'" := bcore_jalr (in custom ce_expr).
    Notation "'signext'" := bcore_signext (in custom ce_expr).
    Notation "'auipc'" := bcore_auipc (in custom ce_expr).
    Notation "'ls_b'" := bcore_lsb (in custom ce_expr).
    Notation "'ls_h'" := bcore_lsh (in custom ce_expr).
    Notation "'load_signext'" := bcore_load_signext (in custom ce_expr).
    Notation "'not_stall'" := bcore_not_stall (in custom ce_expr).
    Notation "'flush'" := bcore_flush (in custom ce_expr).
    Notation "'slt_instr'" := bcore_slt_instr (in custom ce_expr).
    Notation "'compare_lt'" := bcore_compare_lt (in custom ce_expr).
    Notation "'compare_eq'" := bcore_compare_eq (in custom ce_expr).
    Notation "'compare_signed'" := bcore_compare_signed (in custom ce_expr).
    Notation "'compare_imm'" := bcore_compare_imm (in custom ce_expr).
    Notation "'reg_wdata'" := bcore_reg_wdata (in custom ce_expr).
    Notation "'reg_rdata1'" := bcore_reg_rdata1 (in custom ce_expr).
    Notation "'reg_rdata2'" := bcore_reg_rdata2 (in custom ce_expr).
    Notation "'mod_rd_dmem'" := bcore_mod_rd_dmem (in custom ce_expr).
    Notation "'alu_r'" := bcore_alu_r (in custom ce_expr).
    Notation "'alu_inputa'" := bcore_alu_inputa (in custom ce_expr).
    Notation "'alu_inputb'" := bcore_alu_inputb (in custom ce_expr).
    Notation "'exe_data'" := bcore_exe_data (in custom ce_expr).
    Notation "'exe_p4'" := bcore_exe_p4 (in custom ce_expr).
    Notation "'exe_mem2reg'" := bcore_exe_mem2reg (in custom ce_expr).
    Notation "'exe_wmem'" := bcore_exe_wmem (in custom ce_expr).
    Notation "'exe_aluimm'" := bcore_exe_aluimm (in custom ce_expr).
    Notation "'exe_slt_instr'" := bcore_exe_slt_instr (in custom ce_expr).
    Notation "'exe_wreg'" := bcore_exe_wreg (in custom ce_expr).
    Notation "'exe_auipc'" := bcore_exe_auipc (in custom ce_expr).
    Notation "'exe_lsb'" := bcore_exe_lsb (in custom ce_expr).
    Notation "'exe_lsh'" := bcore_exe_lsh (in custom ce_expr).
    Notation "'exe_loadsignext'" := bcore_exe_loadsignext (in custom ce_expr).
    Notation "'exe_jal'" := bcore_exe_jal (in custom ce_expr).
    Notation "'exe_aluc'" := bcore_exe_aluc (in custom ce_expr).
    Notation "'exe_lt'" := bcore_exe_lt (in custom ce_expr).
    Notation "'exe_valid'" := bcore_exe_valid (in custom ce_expr).
    Notation "'lt_32bit'" := bcore_lt_32bit (in custom ce_expr).
    Notation "'exe_rd'" := bcore_exe_rd (in custom ce_expr).
    Notation "'exe_pc'" := bcore_exe_pc (in custom ce_expr).
    Notation "'exe_dmem'" := bcore_exe_dmem (in custom ce_expr).
    Notation "'exe_regdata1'" := bcore_exe_regdata1 (in custom ce_expr).
    Notation "'exe_regdata2'" := bcore_exe_regdata2 (in custom ce_expr).
    Notation "'exe_imm'" := bcore_exe_imm (in custom ce_expr).
    Notation "'mem_mem2reg'" := bcore_mem_mem2reg (in custom ce_expr).
    Notation "'mem_wmem'" := bcore_mem_wmem (in custom ce_expr).
    Notation "'mem_wreg'" := bcore_mem_wreg (in custom ce_expr).
    Notation "'mem_lsb'" := bcore_mem_lsb (in custom ce_expr).
    Notation "'mem_lsh'" := bcore_mem_lsh (in custom ce_expr).
    Notation "'mem_loadsignext'" := bcore_mem_loadsignext (in custom ce_expr).
    Notation "'mem_valid'" := bcore_mem_valid (in custom ce_expr).
    Notation "'mem_rd'" := bcore_mem_rd (in custom ce_expr).
    Notation "'mem_data'" := bcore_mem_data (in custom ce_expr).
    Notation "'mem_dmem'" := bcore_mem_dmem (in custom ce_expr).
    Notation "'mem_pc'" := bcore_mem_pc (in custom ce_expr).
    Notation "'wb_data'" := bcore_wb_data (in custom ce_expr).
    Notation "'wb_mem2reg'" := bcore_wb_mem2reg (in custom ce_expr).
    Notation "'wb_wreg'" := bcore_wb_wreg (in custom ce_expr).
    Notation "'wb_valid'" := bcore_wb_valid (in custom ce_expr).
    Notation "'wb_rd'" := bcore_wb_rd (in custom ce_expr).
    Notation "'wb_dmem'" := bcore_wb_dmem (in custom ce_expr).
    Notation "'wb_pc'" := bcore_wb_pc (in custom ce_expr).

    (* Module identifiers and distinct instance paths. *)
    Notation "'pc_reg'" := pc_o_pc (in custom ce_expr).
    Notation "'cla_32bit'" := cla_o_sum (in custom ce_expr).
    Notation "'mux_3to1'" := mux3_o_data (in custom ce_expr).
    Notation "'if_id_reg'" := ifid_o_id_instr (in custom ce_expr).
    Notation "'control_unit'" := ctl_o_aluc (in custom ce_expr).
    Notation "'comparator'" := cmp_o_lt (in custom ce_expr).
    Notation "'imm_decode'" := imm_o_value (in custom ce_expr).
    Notation "'mux_4to1'" := mux4_o_data (in custom ce_expr).
    Notation "'id_exe_reg'" := idexe_o_p4 (in custom ce_expr).
    Notation "'alu'" := alu_o_result (in custom ce_expr).
    Notation "'store_modifier'" := store_o_data (in custom ce_expr).
    Notation "'exe_mem_reg'" := exemem_o_data (in custom ce_expr).
    Notation "'load_modifier'" := load_o_data (in custom ce_expr).
    Notation "'mem_wb_reg'" := memwb_o_data (in custom ce_expr).
    Notation "'regfile'" := rf_array (in custom ce_expr).
    Notation "'pc_pipeline_reg'" := bcore_pc_pipeline_reg (in custom ce_expr).
    Notation "'p4_adder'" := bcore_p4_adder (in custom ce_expr).
    Notation "'next_pc_mux'" := bcore_next_pc_mux (in custom ce_expr).
    Notation "'if_id_pipeline_reg'" := bcore_if_id_pipeline_reg (in custom ce_expr).
    Notation "'controller'" := bcore_controller (in custom ce_expr).
    Notation "'compare_unit'" := bcore_compare_unit (in custom ce_expr).
    Notation "'immediate_decoder'" := bcore_immediate_decoder (in custom ce_expr).
    Notation "'jal_pc_adder'" := bcore_jal_pc_adder (in custom ce_expr).
    Notation "'br_jalr_adder'" := bcore_br_jalr_adder (in custom ce_expr).
    Notation "'fwda_mux'" := bcore_fwda_mux (in custom ce_expr).
    Notation "'fwdb_mux'" := bcore_fwdb_mux (in custom ce_expr).
    Notation "'id_exe_pipeline_reg'" := bcore_id_exe_pipeline_reg (in custom ce_expr).
    Notation "'alu_unit'" := bcore_alu_unit (in custom ce_expr).
    Notation "'exe_data_mux'" := bcore_exe_data_mux (in custom ce_expr).
    Notation "'store_unit'" := bcore_store_unit (in custom ce_expr).
    Notation "'exe_mem_pipeline_reg'" := bcore_exe_mem_pipeline_reg (in custom ce_expr).
    Notation "'load_unit'" := bcore_load_unit (in custom ce_expr).
    Notation "'mem_wb_pipeline_reg'" := bcore_mem_wb_pipeline_reg (in custom ce_expr).
    Notation "'register_file'" := bcore_register_file (in custom ce_expr).

    (* Child port identifiers. *)
    Notation "'pc_i_clk'" := pc_i_clk (in custom ce_portconnid).
    Notation "'pc_i_resetn'" := pc_i_resetn (in custom ce_portconnid).
    Notation "'pc_i_we'" := pc_i_we (in custom ce_portconnid).
    Notation "'pc_i_pc'" := pc_i_pc (in custom ce_portconnid).
    Notation "'pc_o_pc'" := pc_o_pc (in custom ce_portconnid).
    Notation "'cla_i_a'" := cla_i_a (in custom ce_portconnid).
    Notation "'cla_i_b'" := cla_i_b (in custom ce_portconnid).
    Notation "'cla_i_cin'" := cla_i_cin (in custom ce_portconnid).
    Notation "'cla_o_sum'" := cla_o_sum (in custom ce_portconnid).
    Notation "'mux3_i_a'" := mux3_i_a (in custom ce_portconnid).
    Notation "'mux3_i_b'" := mux3_i_b (in custom ce_portconnid).
    Notation "'mux3_i_c'" := mux3_i_c (in custom ce_portconnid).
    Notation "'mux3_i_select'" := mux3_i_select (in custom ce_portconnid).
    Notation "'mux3_o_data'" := mux3_o_data (in custom ce_portconnid).
    Notation "'ifid_i_clk'" := ifid_i_clk (in custom ce_portconnid).
    Notation "'ifid_i_resetn'" := ifid_i_resetn (in custom ce_portconnid).
    Notation "'ifid_i_we'" := ifid_i_we (in custom ce_portconnid).
    Notation "'ifid_i_flush'" := ifid_i_flush (in custom ce_portconnid).
    Notation "'ifid_i_if_p4'" := ifid_i_if_p4 (in custom ce_portconnid).
    Notation "'ifid_i_if_pc'" := ifid_i_if_pc (in custom ce_portconnid).
    Notation "'ifid_i_if_instr'" := ifid_i_if_instr (in custom ce_portconnid).
    Notation "'ifid_o_id_p4'" := ifid_o_id_p4 (in custom ce_portconnid).
    Notation "'ifid_o_id_pc'" := ifid_o_id_pc (in custom ce_portconnid).
    Notation "'ifid_o_id_instr'" := ifid_o_id_instr (in custom ce_portconnid).
    Notation "'ifid_o_id_valid'" := ifid_o_id_valid (in custom ce_portconnid).
    Notation "'ctl_i_resetn'" := ctl_i_resetn (in custom ce_portconnid).
    Notation "'ctl_i_opcode'" := ctl_i_opcode (in custom ce_portconnid).
    Notation "'ctl_i_funct3'" := ctl_i_funct3 (in custom ce_portconnid).
    Notation "'ctl_i_funct7'" := ctl_i_funct7 (in custom ce_portconnid).
    Notation "'ctl_i_rs1'" := ctl_i_rs1 (in custom ce_portconnid).
    Notation "'ctl_i_rs2'" := ctl_i_rs2 (in custom ce_portconnid).
    Notation "'ctl_i_cmp_lt'" := ctl_i_cmp_lt (in custom ce_portconnid).
    Notation "'ctl_i_cmp_eq'" := ctl_i_cmp_eq (in custom ce_portconnid).
    Notation "'ctl_i_mem_wreg'" := ctl_i_mem_wreg (in custom ce_portconnid).
    Notation "'ctl_i_mem_mem2reg'" := ctl_i_mem_mem2reg (in custom ce_portconnid).
    Notation "'ctl_i_exe_wreg'" := ctl_i_exe_wreg (in custom ce_portconnid).
    Notation "'ctl_i_exe_mem2reg'" := ctl_i_exe_mem2reg (in custom ce_portconnid).
    Notation "'ctl_i_mem_rd'" := ctl_i_mem_rd (in custom ce_portconnid).
    Notation "'ctl_i_exe_rd'" := ctl_i_exe_rd (in custom ce_portconnid).
    Notation "'ctl_o_not_stall'" := ctl_o_not_stall (in custom ce_portconnid).
    Notation "'ctl_o_flush'" := ctl_o_flush (in custom ce_portconnid).
    Notation "'ctl_o_aluc'" := ctl_o_aluc (in custom ce_portconnid).
    Notation "'ctl_o_pcsrc'" := ctl_o_pcsrc (in custom ce_portconnid).
    Notation "'ctl_o_fwda'" := ctl_o_fwda (in custom ce_portconnid).
    Notation "'ctl_o_fwdb'" := ctl_o_fwdb (in custom ce_portconnid).
    Notation "'ctl_o_wreg'" := ctl_o_wreg (in custom ce_portconnid).
    Notation "'ctl_o_wmem'" := ctl_o_wmem (in custom ce_portconnid).
    Notation "'ctl_o_mem2reg'" := ctl_o_mem2reg (in custom ce_portconnid).
    Notation "'ctl_o_aluimm'" := ctl_o_aluimm (in custom ce_portconnid).
    Notation "'ctl_o_jal'" := ctl_o_jal (in custom ce_portconnid).
    Notation "'ctl_o_jalr'" := ctl_o_jalr (in custom ce_portconnid).
    Notation "'ctl_o_signext'" := ctl_o_signext (in custom ce_portconnid).
    Notation "'ctl_o_auipc'" := ctl_o_auipc (in custom ce_portconnid).
    Notation "'ctl_o_lsb'" := ctl_o_lsb (in custom ce_portconnid).
    Notation "'ctl_o_lsh'" := ctl_o_lsh (in custom ce_portconnid).
    Notation "'ctl_o_loadsignext'" := ctl_o_load_signext (in custom ce_portconnid).
    Notation "'ctl_o_slt_instr'" := ctl_o_slt_instr (in custom ce_portconnid).
    Notation "'ctl_o_compare_signed'" := ctl_o_compare_signed (in custom ce_portconnid).
    Notation "'ctl_o_compare_imm'" := ctl_o_compare_imm (in custom ce_portconnid).
    Notation "'cmp_i_a'" := cmp_i_a (in custom ce_portconnid).
    Notation "'cmp_i_b'" := cmp_i_b (in custom ce_portconnid).
    Notation "'cmp_i_unsigned'" := cmp_i_unsigned (in custom ce_portconnid).
    Notation "'cmp_o_lt'" := cmp_o_lt (in custom ce_portconnid).
    Notation "'cmp_o_eq'" := cmp_o_eq (in custom ce_portconnid).
    Notation "'imm_i_instr'" := imm_i_instr (in custom ce_portconnid).
    Notation "'imm_i_opcode'" := imm_i_opcode (in custom ce_portconnid).
    Notation "'imm_i_signext'" := imm_i_signext (in custom ce_portconnid).
    Notation "'imm_o_value'" := imm_o_value (in custom ce_portconnid).
    Notation "'mux4_i_a'" := mux4_i_a (in custom ce_portconnid).
    Notation "'mux4_i_b'" := mux4_i_b (in custom ce_portconnid).
    Notation "'mux4_i_c'" := mux4_i_c (in custom ce_portconnid).
    Notation "'mux4_i_d'" := mux4_i_d (in custom ce_portconnid).
    Notation "'mux4_i_select'" := mux4_i_select (in custom ce_portconnid).
    Notation "'mux4_o_data'" := mux4_o_data (in custom ce_portconnid).
    Notation "'idexe_i_clk'" := idexe_i_clk (in custom ce_portconnid).
    Notation "'idexe_i_resetn'" := idexe_i_resetn (in custom ce_portconnid).
    Notation "'idexe_i_mem2reg'" := idexe_i_mem2reg (in custom ce_portconnid).
    Notation "'idexe_i_wmem'" := idexe_i_wmem (in custom ce_portconnid).
    Notation "'idexe_i_aluimm'" := idexe_i_aluimm (in custom ce_portconnid).
    Notation "'idexe_i_slt_instr'" := idexe_i_slt_instr (in custom ce_portconnid).
    Notation "'idexe_i_wreg'" := idexe_i_wreg (in custom ce_portconnid).
    Notation "'idexe_i_auipc'" := idexe_i_auipc (in custom ce_portconnid).
    Notation "'idexe_i_lsb'" := idexe_i_lsb (in custom ce_portconnid).
    Notation "'idexe_i_lsh'" := idexe_i_lsh (in custom ce_portconnid).
    Notation "'idexe_i_loadsignext'" := idexe_i_loadsignext (in custom ce_portconnid).
    Notation "'idexe_i_jal'" := idexe_i_jal (in custom ce_portconnid).
    Notation "'idexe_i_aluc'" := idexe_i_aluc (in custom ce_portconnid).
    Notation "'idexe_i_lt'" := idexe_i_lt (in custom ce_portconnid).
    Notation "'idexe_i_valid'" := idexe_i_valid (in custom ce_portconnid).
    Notation "'idexe_i_rd'" := idexe_i_rd (in custom ce_portconnid).
    Notation "'idexe_i_pc'" := idexe_i_pc (in custom ce_portconnid).
    Notation "'idexe_i_regdata1'" := idexe_i_regdata1 (in custom ce_portconnid).
    Notation "'idexe_i_regdata2'" := idexe_i_regdata2 (in custom ce_portconnid).
    Notation "'idexe_i_imm'" := idexe_i_imm (in custom ce_portconnid).
    Notation "'idexe_i_p4'" := idexe_i_p4 (in custom ce_portconnid).
    Notation "'idexe_o_mem2reg'" := idexe_o_mem2reg (in custom ce_portconnid).
    Notation "'idexe_o_wmem'" := idexe_o_wmem (in custom ce_portconnid).
    Notation "'idexe_o_aluimm'" := idexe_o_aluimm (in custom ce_portconnid).
    Notation "'idexe_o_slt_instr'" := idexe_o_slt_instr (in custom ce_portconnid).
    Notation "'idexe_o_wreg'" := idexe_o_wreg (in custom ce_portconnid).
    Notation "'idexe_o_auipc'" := idexe_o_auipc (in custom ce_portconnid).
    Notation "'idexe_o_lsb'" := idexe_o_lsb (in custom ce_portconnid).
    Notation "'idexe_o_lsh'" := idexe_o_lsh (in custom ce_portconnid).
    Notation "'idexe_o_loadsignext'" := idexe_o_loadsignext (in custom ce_portconnid).
    Notation "'idexe_o_jal'" := idexe_o_jal (in custom ce_portconnid).
    Notation "'idexe_o_aluc'" := idexe_o_aluc (in custom ce_portconnid).
    Notation "'idexe_o_lt'" := idexe_o_lt (in custom ce_portconnid).
    Notation "'idexe_o_valid'" := idexe_o_valid (in custom ce_portconnid).
    Notation "'idexe_o_rd'" := idexe_o_rd (in custom ce_portconnid).
    Notation "'idexe_o_pc'" := idexe_o_pc (in custom ce_portconnid).
    Notation "'idexe_o_regdata1'" := idexe_o_regdata1 (in custom ce_portconnid).
    Notation "'idexe_o_regdata2'" := idexe_o_regdata2 (in custom ce_portconnid).
    Notation "'idexe_o_imm'" := idexe_o_imm (in custom ce_portconnid).
    Notation "'idexe_o_p4'" := idexe_o_p4 (in custom ce_portconnid).
    Notation "'alu_i_a'" := alu_i_a (in custom ce_portconnid).
    Notation "'alu_i_b'" := alu_i_b (in custom ce_portconnid).
    Notation "'alu_i_aluc'" := alu_i_aluc (in custom ce_portconnid).
    Notation "'alu_o_result'" := alu_o_result (in custom ce_portconnid).
    Notation "'store_i_sb'" := store_i_sb (in custom ce_portconnid).
    Notation "'store_i_sh'" := store_i_sh (in custom ce_portconnid).
    Notation "'store_i_data'" := store_i_data (in custom ce_portconnid).
    Notation "'store_o_data'" := store_o_data (in custom ce_portconnid).
    Notation "'exemem_i_clk'" := exemem_i_clk (in custom ce_portconnid).
    Notation "'exemem_i_resetn'" := exemem_i_resetn (in custom ce_portconnid).
    Notation "'exemem_i_mem2reg'" := exemem_i_mem2reg (in custom ce_portconnid).
    Notation "'exemem_i_wmem'" := exemem_i_wmem (in custom ce_portconnid).
    Notation "'exemem_i_wreg'" := exemem_i_wreg (in custom ce_portconnid).
    Notation "'exemem_i_lsb'" := exemem_i_lsb (in custom ce_portconnid).
    Notation "'exemem_i_lsh'" := exemem_i_lsh (in custom ce_portconnid).
    Notation "'exemem_i_loadsignext'" := exemem_i_loadsignext (in custom ce_portconnid).
    Notation "'exemem_i_valid'" := exemem_i_valid (in custom ce_portconnid).
    Notation "'exemem_i_rd'" := exemem_i_rd (in custom ce_portconnid).
    Notation "'exemem_i_data'" := exemem_i_data (in custom ce_portconnid).
    Notation "'exemem_i_dmem'" := exemem_i_dmem (in custom ce_portconnid).
    Notation "'exemem_i_pc'" := exemem_i_pc (in custom ce_portconnid).
    Notation "'exemem_o_mem2reg'" := exemem_o_mem2reg (in custom ce_portconnid).
    Notation "'exemem_o_wmem'" := exemem_o_wmem (in custom ce_portconnid).
    Notation "'exemem_o_wreg'" := exemem_o_wreg (in custom ce_portconnid).
    Notation "'exemem_o_lsb'" := exemem_o_lsb (in custom ce_portconnid).
    Notation "'exemem_o_lsh'" := exemem_o_lsh (in custom ce_portconnid).
    Notation "'exemem_o_loadsignext'" := exemem_o_loadsignext (in custom ce_portconnid).
    Notation "'exemem_o_valid'" := exemem_o_valid (in custom ce_portconnid).
    Notation "'exemem_o_rd'" := exemem_o_rd (in custom ce_portconnid).
    Notation "'exemem_o_data'" := exemem_o_data (in custom ce_portconnid).
    Notation "'exemem_o_dmem'" := exemem_o_dmem (in custom ce_portconnid).
    Notation "'exemem_o_pc'" := exemem_o_pc (in custom ce_portconnid).
    Notation "'load_i_lb'" := load_i_lb (in custom ce_portconnid).
    Notation "'load_i_lh'" := load_i_lh (in custom ce_portconnid).
    Notation "'load_i_signext'" := load_i_signext (in custom ce_portconnid).
    Notation "'load_i_offset'" := load_i_offset (in custom ce_portconnid).
    Notation "'load_i_data'" := load_i_data (in custom ce_portconnid).
    Notation "'load_o_data'" := load_o_data (in custom ce_portconnid).
    Notation "'memwb_i_clk'" := memwb_i_clk (in custom ce_portconnid).
    Notation "'memwb_i_resetn'" := memwb_i_resetn (in custom ce_portconnid).
    Notation "'memwb_i_mem2reg'" := memwb_i_mem2reg (in custom ce_portconnid).
    Notation "'memwb_i_wreg'" := memwb_i_wreg (in custom ce_portconnid).
    Notation "'memwb_i_valid'" := memwb_i_valid (in custom ce_portconnid).
    Notation "'memwb_i_rd'" := memwb_i_rd (in custom ce_portconnid).
    Notation "'memwb_i_data'" := memwb_i_data (in custom ce_portconnid).
    Notation "'memwb_i_rd_dmem'" := memwb_i_rd_dmem (in custom ce_portconnid).
    Notation "'memwb_i_pc'" := memwb_i_pc (in custom ce_portconnid).
    Notation "'memwb_o_mem2reg'" := memwb_o_mem2reg (in custom ce_portconnid).
    Notation "'memwb_o_wreg'" := memwb_o_wreg (in custom ce_portconnid).
    Notation "'memwb_o_valid'" := memwb_o_valid (in custom ce_portconnid).
    Notation "'memwb_o_rd'" := memwb_o_rd (in custom ce_portconnid).
    Notation "'memwb_o_data'" := memwb_o_data (in custom ce_portconnid).
    Notation "'memwb_o_dmem'" := memwb_o_dmem (in custom ce_portconnid).
    Notation "'memwb_o_pc'" := memwb_o_pc (in custom ce_portconnid).
    Notation "'rf_clk'" := rf_clk (in custom ce_portconnid).
    Notation "'rf_resetn'" := rf_resetn (in custom ce_portconnid).
    Notation "'rf_rs1'" := rf_rs1 (in custom ce_portconnid).
    Notation "'rf_rs2'" := rf_rs2 (in custom ce_portconnid).
    Notation "'rf_rd'" := rf_rd (in custom ce_portconnid).
    Notation "'rf_reg_write'" := rf_reg_write (in custom ce_portconnid).
    Notation "'rf_write_data'" := rf_write_data (in custom ce_portconnid).
    Notation "'rf_read_data1'" := rf_read_data1 (in custom ce_portconnid).
    Notation "'rf_read_data2'" := rf_read_data2 (in custom ce_portconnid).

    Definition m : @VModuleDecl bzeeno_vid := #[
module core
 (input logic i_clk, input logic i_resetn, input logic [31:0] i_instr,
  input logic [31:0] i_dmem, output logic [31:0] o_pc,
  output logic [31:0] o_addr, output logic [31:0] o_dmem,
  output logic o_wmem, output logic o_sb, output logic o_sh,
  output logic o_commit_vld, output logic [31:0] o_commit_pc);
logic [31:0] pc_next; logic [31:0] if_pc; logic [31:0] if_p4;
logic [31:0] id_instr; logic id_valid; logic [31:0] imm_val;
logic [6:0] opcode; logic [4:0] rd; logic [4:0] rs1; logic [4:0] rs2;
logic [2:0] funct3; logic [6:0] funct7; logic [31:0] id_pc; logic [31:0] id_p4;
logic [31:0] jalr_branch_inputb; logic [31:0] jal_pc; logic [31:0] jalr_branch_pc_raw;
logic [31:0] jalr_branch_pc; logic [31:0] compare_inputb; logic [1:0] fwda; logic [1:0] fwdb;
logic [5:0] aluc; logic [31:0] id_regdata1; logic [31:0] id_regdata2; logic [1:0] pcsrc;
logic mem2reg; logic wmem; logic aluimm; logic wreg; logic jal; logic jalr; logic signext;
logic auipc; logic ls_b; logic ls_h; logic load_signext; logic not_stall; logic flush; logic slt_instr;
logic compare_lt; logic compare_eq; logic compare_signed; logic compare_imm; logic [31:0] reg_wdata;
logic [31:0] reg_rdata1; logic [31:0] reg_rdata2; logic [31:0] mod_rd_dmem;
logic [31:0] alu_r; logic [31:0] alu_inputa; logic [31:0] alu_inputb; logic [31:0] exe_data;
logic [31:0] exe_p4; logic exe_mem2reg; logic exe_wmem; logic exe_aluimm; logic exe_slt_instr;
logic exe_wreg; logic exe_auipc; logic exe_lsb; logic exe_lsh; logic exe_loadsignext; logic exe_jal; logic exe_valid;
logic [5:0] exe_aluc; logic exe_lt; logic [31:0] lt_32bit; logic [4:0] exe_rd; logic [31:0] exe_pc;
logic [31:0] exe_dmem; logic [31:0] exe_regdata1; logic [31:0] exe_regdata2; logic [31:0] exe_imm;
logic mem_mem2reg; logic mem_wmem; logic mem_wreg; logic mem_lsb; logic mem_lsh; logic mem_loadsignext;
logic mem_valid; logic [4:0] mem_rd; logic [31:0] mem_data; logic [31:0] mem_dmem; logic [31:0] mem_pc;
logic [31:0] wb_data; logic wb_mem2reg; logic wb_wreg; logic wb_valid; logic [4:0] wb_rd;
logic [31:0] wb_dmem; logic [31:0] wb_pc;
pc_reg pc_pipeline_reg(pc_i_clk(i_clk), pc_i_resetn(i_resetn), pc_i_we(not_stall), pc_i_pc(pc_next), pc_o_pc(if_pc));
cla_32bit p4_adder(cla_i_a(if_pc), cla_i_b(32'h4), cla_i_cin(1'b0), cla_o_sum(if_p4));
mux_3to1 next_pc_mux(mux3_i_a(if_p4), mux3_i_b(jalr_branch_pc), mux3_i_c(jal_pc), mux3_i_select(pcsrc), mux3_o_data(pc_next));
if_id_reg if_id_pipeline_reg(ifid_i_clk(i_clk), ifid_i_resetn(i_resetn), ifid_i_we(not_stall), ifid_i_flush(flush), ifid_i_if_p4(if_p4), ifid_i_if_pc(if_pc), ifid_i_if_instr(i_instr), ifid_o_id_p4(id_p4), ifid_o_id_pc(id_pc), ifid_o_id_instr(id_instr), ifid_o_id_valid(id_valid));
assign opcode = id_instr[6:0]; assign rd = id_instr[11:7]; assign rs1 = id_instr[19:15]; assign rs2 = id_instr[24:20]; assign funct3 = id_instr[14:12]; assign funct7 = id_instr[31:25];
control_unit controller(ctl_i_resetn(i_resetn), ctl_i_opcode(opcode), ctl_i_funct3(funct3), ctl_i_funct7(funct7), ctl_i_rs1(rs1), ctl_i_rs2(rs2), ctl_i_cmp_lt(compare_lt), ctl_i_cmp_eq(compare_eq), ctl_i_mem_wreg(mem_wreg), ctl_i_mem_mem2reg(mem_mem2reg), ctl_i_exe_wreg(exe_wreg), ctl_i_exe_mem2reg(exe_mem2reg), ctl_i_mem_rd(mem_rd), ctl_i_exe_rd(exe_rd), ctl_o_not_stall(not_stall), ctl_o_flush(flush), ctl_o_aluc(aluc), ctl_o_pcsrc(pcsrc), ctl_o_fwda(fwda), ctl_o_fwdb(fwdb), ctl_o_wreg(wreg), ctl_o_wmem(wmem), ctl_o_mem2reg(mem2reg), ctl_o_aluimm(aluimm), ctl_o_jal(jal), ctl_o_jalr(jalr), ctl_o_signext(signext), ctl_o_auipc(auipc), ctl_o_lsb(ls_b), ctl_o_lsh(ls_h), ctl_o_loadsignext(load_signext), ctl_o_slt_instr(slt_instr), ctl_o_compare_signed(compare_signed), ctl_o_compare_imm(compare_imm));
assign compare_inputb = compare_imm ? imm_val : id_regdata2;
comparator compare_unit(cmp_i_a(id_regdata1), cmp_i_b(compare_inputb), cmp_i_unsigned(~compare_signed), cmp_o_lt(compare_lt), cmp_o_eq(compare_eq));
imm_decode immediate_decoder(imm_i_instr(id_instr), imm_i_opcode(opcode), imm_i_signext(signext), imm_o_value(imm_val));
cla_32bit jal_pc_adder(cla_i_a(imm_val), cla_i_b(id_pc), cla_i_cin(1'b0), cla_o_sum(jal_pc));
assign jalr_branch_inputb = jalr ? id_regdata1 : id_pc;
cla_32bit br_jalr_adder(cla_i_a(imm_val), cla_i_b(jalr_branch_inputb), cla_i_cin(1'b0), cla_o_sum(jalr_branch_pc_raw));
assign jalr_branch_pc = {jalr_branch_pc_raw[31:1], 1'b0};
mux_4to1 fwda_mux(mux4_i_a(reg_rdata1), mux4_i_b(exe_data), mux4_i_c(mem_data), mux4_i_d(mod_rd_dmem), mux4_i_select(fwda), mux4_o_data(id_regdata1));
mux_4to1 fwdb_mux(mux4_i_a(reg_rdata2), mux4_i_b(exe_data), mux4_i_c(mem_data), mux4_i_d(mod_rd_dmem), mux4_i_select(fwdb), mux4_o_data(id_regdata2));
id_exe_reg id_exe_pipeline_reg(idexe_i_clk(i_clk), idexe_i_resetn(i_resetn), idexe_i_mem2reg(mem2reg), idexe_i_wmem(wmem), idexe_i_aluimm(aluimm), idexe_i_slt_instr(slt_instr), idexe_i_wreg(wreg), idexe_i_auipc(auipc), idexe_i_lsb(ls_b), idexe_i_lsh(ls_h), idexe_i_loadsignext(load_signext), idexe_i_jal(jal), idexe_i_aluc(aluc), idexe_i_lt(compare_lt), idexe_i_valid(id_valid & not_stall), idexe_i_rd(rd), idexe_i_pc(id_pc), idexe_i_regdata1(id_regdata1), idexe_i_regdata2(id_regdata2), idexe_i_imm(imm_val), idexe_i_p4(id_p4), idexe_o_mem2reg(exe_mem2reg), idexe_o_wmem(exe_wmem), idexe_o_aluimm(exe_aluimm), idexe_o_slt_instr(exe_slt_instr), idexe_o_wreg(exe_wreg), idexe_o_auipc(exe_auipc), idexe_o_lsb(exe_lsb), idexe_o_lsh(exe_lsh), idexe_o_loadsignext(exe_loadsignext), idexe_o_jal(exe_jal), idexe_o_aluc(exe_aluc), idexe_o_lt(exe_lt), idexe_o_valid(exe_valid), idexe_o_rd(exe_rd), idexe_o_pc(exe_pc), idexe_o_regdata1(exe_regdata1), idexe_o_regdata2(exe_regdata2), idexe_o_imm(exe_imm), idexe_o_p4(exe_p4));
assign alu_inputa = exe_auipc ? exe_pc : exe_regdata1; assign alu_inputb = exe_aluimm ? exe_imm : exe_regdata2;
alu alu_unit(alu_i_a(alu_inputa), alu_i_b(alu_inputb), alu_i_aluc(exe_aluc), alu_o_result(alu_r));
assign lt_32bit = {31'b0, exe_lt};
mux_3to1 exe_data_mux(mux3_i_a(alu_r), mux3_i_b(lt_32bit), mux3_i_c(exe_p4), mux3_i_select({exe_jal, exe_slt_instr}), mux3_o_data(exe_data));
store_modifier store_unit(store_i_sb(exe_lsb), store_i_sh(exe_lsh), store_i_data(exe_regdata2), store_o_data(exe_dmem));
exe_mem_reg exe_mem_pipeline_reg(exemem_i_clk(i_clk), exemem_i_resetn(i_resetn), exemem_i_mem2reg(exe_mem2reg), exemem_i_wmem(exe_wmem), exemem_i_wreg(exe_wreg), exemem_i_lsb(exe_lsb), exemem_i_lsh(exe_lsh), exemem_i_loadsignext(exe_loadsignext), exemem_i_valid(exe_valid), exemem_i_rd(exe_rd), exemem_i_data(exe_data), exemem_i_dmem(exe_dmem), exemem_i_pc(exe_pc), exemem_o_mem2reg(mem_mem2reg), exemem_o_wmem(mem_wmem), exemem_o_wreg(mem_wreg), exemem_o_lsb(mem_lsb), exemem_o_lsh(mem_lsh), exemem_o_loadsignext(mem_loadsignext), exemem_o_valid(mem_valid), exemem_o_rd(mem_rd), exemem_o_data(mem_data), exemem_o_dmem(mem_dmem), exemem_o_pc(mem_pc));
load_modifier load_unit(load_i_lb(mem_lsb), load_i_lh(mem_lsh), load_i_signext(mem_loadsignext), load_i_offset(mem_data[1:0]), load_i_data(i_dmem), load_o_data(mod_rd_dmem));
mem_wb_reg mem_wb_pipeline_reg(memwb_i_clk(i_clk), memwb_i_resetn(i_resetn), memwb_i_mem2reg(mem_mem2reg), memwb_i_wreg(mem_wreg), memwb_i_valid(mem_valid), memwb_i_rd(mem_rd), memwb_i_data(mem_data), memwb_i_rd_dmem(mod_rd_dmem), memwb_i_pc(mem_pc), memwb_o_mem2reg(wb_mem2reg), memwb_o_wreg(wb_wreg), memwb_o_valid(wb_valid), memwb_o_rd(wb_rd), memwb_o_data(wb_data), memwb_o_dmem(wb_dmem), memwb_o_pc(wb_pc));
assign reg_wdata = wb_mem2reg ? wb_dmem : wb_data;
regfile register_file(rf_clk(~i_clk), rf_resetn(i_resetn), rf_rs1(rs1), rf_rs2(rs2), rf_rd(wb_rd), rf_reg_write(wb_wreg), rf_write_data(reg_wdata), rf_read_data1(reg_rdata1), rf_read_data2(reg_rdata2));
assign o_pc = if_pc; assign o_wmem = mem_wmem; assign o_addr = mem_data; assign o_dmem = mem_dmem; assign o_sb = mem_lsb; assign o_sh = mem_lsh; assign o_commit_vld = wb_valid; assign o_commit_pc = wb_pc;
endmodule].
  End M.

  (** This is the actual VerilRocq transition of the complete hierarchy.  The
      existential function is accepted only after its graph is checked against
      the least fixed point of [M.m] with the registered child transitions. *)
  Section AbsOps.
    Context `{sz_ops} `{array_ops hmap}.
    Import ListNotations HMapNotations.

    Definition mtrs : MTrsOf M.m fmapEmpty BzeenoCore.etrs
        BzeenoTopState.Inputs BzeenoTopState.Flops.
    Proof.
      unshelve epose (trs := _ : MTrs).
      { apply Build_MTrs. 1-2: shelve.
        intros inputs flops.
        destruct (from_state (A := BzeenoTopState.Inputs) inputs) as [i_format|]; [| eapply (_, _)].
        destruct (from_state (A := BzeenoTopState.Flops) flops) as [f_format|]; [| eapply (_, _)].
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
  End AbsOps.
End BzeenoFullCore.
