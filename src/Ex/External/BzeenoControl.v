(** Deterministic RV32I control-unit AST for the repaired bzeeno-derived
    core.  The global signal type is deliberately shared with
    [BzeenoPipeline], so this module can later be instantiated by [core]. *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Lib.Lib. Import SZNotations.
Require Import Lang.Lang.
Require Import Ex.External.BzeenoPipeline.

Module BzeenoControl.
  Module M.
    Notation "'control_unit'" := ctl_o_aluc (in custom ce_top).
    Notation "'i_resetn'" := ctl_i_resetn (in custom ce_expr).
    Notation "'opcode'" := ctl_i_opcode (in custom ce_expr).
    Notation "'funct3'" := ctl_i_funct3 (in custom ce_expr).
    Notation "'funct7'" := ctl_i_funct7 (in custom ce_expr).
    Notation "'rs1'" := ctl_i_rs1 (in custom ce_expr).
    Notation "'rs2'" := ctl_i_rs2 (in custom ce_expr).
    Notation "'i_compare_lt'" := ctl_i_cmp_lt (in custom ce_expr).
    Notation "'i_compare_eq'" := ctl_i_cmp_eq (in custom ce_expr).
    Notation "'i_mem_wreg'" := ctl_i_mem_wreg (in custom ce_expr).
    Notation "'i_mem_mem2reg'" := ctl_i_mem_mem2reg (in custom ce_expr).
    Notation "'i_exe_wreg'" := ctl_i_exe_wreg (in custom ce_expr).
    Notation "'i_exe_mem2reg'" := ctl_i_exe_mem2reg (in custom ce_expr).
    Notation "'i_mem_rd'" := ctl_i_mem_rd (in custom ce_expr).
    Notation "'i_exe_rd'" := ctl_i_exe_rd (in custom ce_expr).
    Notation "'o_not_stall'" := ctl_o_not_stall (in custom ce_expr).
    Notation "'o_flush'" := ctl_o_flush (in custom ce_expr).
    Notation "'aluc'" := ctl_o_aluc (in custom ce_expr).
    Notation "'pcsrc'" := ctl_o_pcsrc (in custom ce_expr).
    Notation "'o_fwda'" := ctl_o_fwda (in custom ce_expr).
    Notation "'o_fwdb'" := ctl_o_fwdb (in custom ce_expr).
    Notation "'o_wreg'" := ctl_o_wreg (in custom ce_expr).
    Notation "'o_wmem'" := ctl_o_wmem (in custom ce_expr).
    Notation "'mem2reg'" := ctl_o_mem2reg (in custom ce_expr).
    Notation "'aluimm'" := ctl_o_aluimm (in custom ce_expr).
    Notation "'jal'" := ctl_o_jal (in custom ce_expr).
    Notation "'jalr'" := ctl_o_jalr (in custom ce_expr).
    Notation "'signext'" := ctl_o_signext (in custom ce_expr).
    Notation "'auipc'" := ctl_o_auipc (in custom ce_expr).
    Notation "'ls_b'" := ctl_o_lsb (in custom ce_expr).
    Notation "'ls_h'" := ctl_o_lsh (in custom ce_expr).
    Notation "'load_signext'" := ctl_o_load_signext (in custom ce_expr).
    Notation "'slt_instr'" := ctl_o_slt_instr (in custom ce_expr).
    Notation "'compare_signed'" := ctl_o_compare_signed (in custom ce_expr).
    Notation "'compare_imm'" := ctl_o_compare_imm (in custom ce_expr).
    Notation "'use_rs1'" := ctl_use_rs1 (in custom ce_expr).
    Notation "'use_rs2'" := ctl_use_rs2 (in custom ce_expr).

    Definition m : @VModuleDecl bzeeno_vid := #[
module control_unit
 (input logic i_resetn, input logic [6:0] opcode, input logic [2:0] funct3,
  input logic [6:0] funct7, input logic [4:0] rs1, input logic [4:0] rs2,
  input logic i_compare_lt, input logic i_compare_eq, input logic i_mem_wreg,
  input logic i_mem_mem2reg, input logic i_exe_wreg, input logic i_exe_mem2reg,
  input logic [4:0] i_mem_rd, input logic [4:0] i_exe_rd,
  output logic o_not_stall, output logic o_flush, output logic [5:0] aluc,
  output logic [1:0] pcsrc, output logic [1:0] o_fwda, output logic [1:0] o_fwdb,
  output logic o_wreg, output logic o_wmem, output logic mem2reg,
  output logic aluimm, output logic jal, output logic jalr, output logic signext,
  output logic auipc, output logic ls_b, output logic ls_h, output logic load_signext,
  output logic slt_instr, output logic compare_signed, output logic compare_imm);
logic use_rs1; logic use_rs2;
always @* begin
  o_fwda = 2'b00; o_fwdb = 2'b00;
  if (i_exe_wreg & (i_exe_rd != 0) & (i_exe_rd == rs1) & !i_exe_mem2reg) o_fwda = 2'b01;
  else if (i_mem_wreg & (i_mem_rd != 0) & (i_mem_rd == rs1) & !i_mem_mem2reg) o_fwda = 2'b10;
  else if (i_mem_wreg & (i_mem_rd != 0) & (i_mem_rd == rs1) & i_mem_mem2reg) o_fwda = 2'b11;
  if (i_exe_wreg & (i_exe_rd != 0) & (i_exe_rd == rs2) & !i_exe_mem2reg) o_fwdb = 2'b01;
  else if (i_mem_wreg & (i_mem_rd != 0) & (i_mem_rd == rs2) & !i_mem_mem2reg) o_fwdb = 2'b10;
  else if (i_mem_wreg & (i_mem_rd != 0) & (i_mem_rd == rs2) & i_mem_mem2reg) o_fwdb = 2'b11;
  o_not_stall = 1'b1; o_flush = 1'b0; o_wreg = 1'b0; o_wmem = 1'b0;
  mem2reg = 1'b0; aluimm = 1'b0; jal = 1'b0; jalr = 1'b0; signext = 1'b0;
  auipc = 1'b0; ls_b = 1'b0; ls_h = 1'b0; load_signext = 1'b0; slt_instr = 1'b0;
  compare_signed = 1'b0; compare_imm = 1'b0; use_rs1 = 1'b0; use_rs2 = 1'b0;
  pcsrc = 2'b00; aluc = 6'b000000;
  if (i_resetn) case (opcode)
    7'b0110011: begin use_rs1 = 1'b1; use_rs2 = 1'b1; case ({funct7,funct3})
      {7'b0000000,3'b000}: o_wreg = 1'b1;
      {7'b0100000,3'b000}: begin o_wreg = 1'b1; aluc = 6'b001000; end
      {7'b0000000,3'b001}: begin o_wreg = 1'b1; aluc = 6'b000101; end
      {7'b0000000,3'b010}: begin o_wreg = 1'b1; slt_instr = 1'b1; compare_signed = 1'b1; end
      {7'b0000000,3'b011}: begin o_wreg = 1'b1; slt_instr = 1'b1; end
      {7'b0000000,3'b100}: begin o_wreg = 1'b1; aluc = 6'b000100; end
      {7'b0000000,3'b101}: begin o_wreg = 1'b1; aluc = 6'b001101; end
      {7'b0100000,3'b101}: begin o_wreg = 1'b1; aluc = 6'b011101; end
      {7'b0000000,3'b110}: begin o_wreg = 1'b1; aluc = 6'b001010; end
      {7'b0000000,3'b111}: begin o_wreg = 1'b1; aluc = 6'b000010; end
      default: begin end endcase end
    7'b0010011: begin use_rs1 = 1'b1; aluimm = 1'b1; signext = 1'b1; case (funct3)
      3'b000: o_wreg = 1'b1;
      3'b010: begin o_wreg = 1'b1; slt_instr = 1'b1; compare_signed = 1'b1; compare_imm = 1'b1; end
      3'b011: begin o_wreg = 1'b1; slt_instr = 1'b1; compare_imm = 1'b1; end
      3'b100: begin o_wreg = 1'b1; aluc = 6'b000100; end
      3'b110: begin o_wreg = 1'b1; aluc = 6'b001010; end
      3'b111: begin o_wreg = 1'b1; aluc = 6'b000010; end
      3'b001: if (funct7 == 7'b0000000) begin o_wreg = 1'b1; signext = 1'b0; aluc = 6'b000101; end
      3'b101: begin signext = 1'b0; if (funct7 == 7'b0000000) begin o_wreg = 1'b1; aluc = 6'b001101; end else if (funct7 == 7'b0100000) begin o_wreg = 1'b1; aluc = 6'b011101; end end
      default: begin end endcase end
    7'b1100011: begin use_rs1 = 1'b1; use_rs2 = 1'b1; signext = 1'b1; case (funct3)
      3'b000: begin compare_signed = 1'b1; pcsrc = i_compare_eq ? 2'b01 : 2'b00; end
      3'b001: begin compare_signed = 1'b1; pcsrc = i_compare_eq ? 2'b00 : 2'b01; end
      3'b100: begin compare_signed = 1'b1; pcsrc = i_compare_lt ? 2'b01 : 2'b00; end
      3'b101: begin compare_signed = 1'b1; pcsrc = i_compare_lt ? 2'b00 : 2'b01; end
      3'b110: pcsrc = i_compare_lt ? 2'b01 : 2'b00;
      3'b111: pcsrc = i_compare_lt ? 2'b00 : 2'b01;
      default: begin end endcase end
    7'b0000011: begin use_rs1 = 1'b1; signext = 1'b1; aluimm = 1'b1; case (funct3)
      3'b000: begin o_wreg = 1'b1; mem2reg = 1'b1; ls_b = 1'b1; load_signext = 1'b1; end
      3'b001: begin o_wreg = 1'b1; mem2reg = 1'b1; ls_h = 1'b1; load_signext = 1'b1; end
      3'b010: begin o_wreg = 1'b1; mem2reg = 1'b1; end
      3'b100: begin o_wreg = 1'b1; mem2reg = 1'b1; ls_b = 1'b1; end
      3'b101: begin o_wreg = 1'b1; mem2reg = 1'b1; ls_h = 1'b1; end
      default: begin end endcase end
    7'b0100011: begin use_rs1 = 1'b1; use_rs2 = 1'b1; signext = 1'b1; aluimm = 1'b1; case (funct3)
      3'b000: begin o_wmem = 1'b1; ls_b = 1'b1; end
      3'b001: begin o_wmem = 1'b1; ls_h = 1'b1; end
      3'b010: o_wmem = 1'b1;
      default: begin end endcase end
    7'b0110111: begin o_wreg = 1'b1; aluimm = 1'b1; aluc = 6'b001100; end
    7'b0010111: begin o_wreg = 1'b1; aluimm = 1'b1; signext = 1'b1; auipc = 1'b1; end
    7'b1101111: begin o_wreg = 1'b1; jal = 1'b1; pcsrc = 2'b10; end
    7'b1100111: if (funct3 == 3'b000) begin use_rs1 = 1'b1; o_wreg = 1'b1; jal = 1'b1; jalr = 1'b1; signext = 1'b1; pcsrc = 2'b01; end
    default: begin end
  endcase
  if (i_exe_wreg & i_exe_mem2reg & (i_exe_rd != 0) & ((use_rs1 & (i_exe_rd == rs1)) | (use_rs2 & (i_exe_rd == rs2)))) begin
    o_not_stall = 1'b0; o_wreg = 1'b0; o_wmem = 1'b0;
  end
  if (pcsrc != 2'b00) o_flush = 1'b1;
end
endmodule].
  End M.

  Record Inputs := {
    resetn_v : SZ; opcode_v : SZ; funct3_v : SZ; funct7_v : SZ; rs1_v : SZ; rs2_v : SZ;
    cmp_lt_v : SZ; cmp_eq_v : SZ; mem_wreg_v : SZ; mem_mem2reg_v : SZ;
    exe_wreg_v : SZ; exe_mem2reg_v : SZ; mem_rd_v : SZ; exe_rd_v : SZ;
  }.
  Definition Flops := unit.

  Section AbsOps.
    Context `{sz_ops} `{array_ops hmap}.
    Import ListNotations. Import HMapNotations.
    #[export] Instance inputs_structured : StructuredState Inputs := {
      from_state := fun state =>
        resetn_v <- sfind ctl_i_resetn state; opcode_v <- sfind ctl_i_opcode state;
        funct3_v <- sfind ctl_i_funct3 state; funct7_v <- sfind ctl_i_funct7 state;
        rs1_v <- sfind ctl_i_rs1 state; rs2_v <- sfind ctl_i_rs2 state;
        cmp_lt_v <- sfind ctl_i_cmp_lt state; cmp_eq_v <- sfind ctl_i_cmp_eq state;
        mem_wreg_v <- sfind ctl_i_mem_wreg state; mem_mem2reg_v <- sfind ctl_i_mem_mem2reg state;
        exe_wreg_v <- sfind ctl_i_exe_wreg state; exe_mem2reg_v <- sfind ctl_i_exe_mem2reg state;
        mem_rd_v <- sfind ctl_i_mem_rd state; exe_rd_v <- sfind ctl_i_exe_rd state;
        Sret {| resetn_v := hbits resetn_v; opcode_v := hbits opcode_v; funct3_v := hbits funct3_v;
                funct7_v := hbits funct7_v; rs1_v := hbits rs1_v; rs2_v := hbits rs2_v;
                cmp_lt_v := hbits cmp_lt_v; cmp_eq_v := hbits cmp_eq_v;
                mem_wreg_v := hbits mem_wreg_v; mem_mem2reg_v := hbits mem_mem2reg_v;
                exe_wreg_v := hbits exe_wreg_v; exe_mem2reg_v := hbits exe_mem2reg_v;
                mem_rd_v := hbits mem_rd_v; exe_rd_v := hbits exe_rd_v |};
      to_state := fun i => match i with
        | {| resetn_v := a; opcode_v := b; funct3_v := c; funct7_v := d; rs1_v := e; rs2_v := f;
             cmp_lt_v := g; cmp_eq_v := h; mem_wreg_v := j; mem_mem2reg_v := k;
             exe_wreg_v := l; exe_mem2reg_v := n; mem_rd_v := o; exe_rd_v := p |} =>
            HMapStr [(ctl_i_resetn,HMapBits a);(ctl_i_opcode,HMapBits b);(ctl_i_funct3,HMapBits c);
                     (ctl_i_funct7,HMapBits d);(ctl_i_rs1,HMapBits e);(ctl_i_rs2,HMapBits f);
                     (ctl_i_cmp_lt,HMapBits g);(ctl_i_cmp_eq,HMapBits h);(ctl_i_mem_wreg,HMapBits j);
                     (ctl_i_mem_mem2reg,HMapBits k);(ctl_i_exe_wreg,HMapBits l);(ctl_i_exe_mem2reg,HMapBits n);
                     (ctl_i_mem_rd,HMapBits o);(ctl_i_exe_rd,HMapBits p)]
        end;
    }.
    #[export] Instance flops_structured : StructuredState Flops := {
      from_state := fun _ => Sret tt;
      to_state := fun _ => [];
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
End BzeenoControl.
