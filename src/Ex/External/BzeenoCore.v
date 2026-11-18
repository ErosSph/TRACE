(** Module-transition registry for the repaired bzeeno RV32I core.

    Module identifiers are represented by the (globally unique) constructor
    chosen as each imported module's AST name.  This table is the link that
    makes a [VModuleIns] executable rather than [TrsUndeclared]. *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Lib.Lib. Import SZNotations.
Require Import Lang.Lang.
Require Import Ex.External.BzeenoPipeline.
Require Import Ex.External.BzeenoControl.

Module BzeenoCore.
  Section Registry.
  Context `{sz_ops} `{array_ops hmap}.
  Definition etrs (eid : bzeeno_vid) : trsOk MTrs :=
    match eid with
    | pc_o_pc => Sret (BzeenoPipeline.PCReg.mtrs : MTrs)
    | ifid_o_id_instr => Sret (BzeenoPipeline.IFIDReg.mtrs : MTrs)
    | idexe_o_p4 => Sret (BzeenoPipeline.IDEXEReg.mtrs : MTrs)
    | exemem_o_data => Sret (BzeenoPipeline.EXEMEMReg.mtrs : MTrs)
    | memwb_o_data => Sret (BzeenoPipeline.MEMWBReg.mtrs : MTrs)
    | store_o_data => Sret (BzeenoPipeline.StoreModifier.mtrs : MTrs)
    | load_o_data => Sret (BzeenoPipeline.LoadModifier.mtrs : MTrs)
    | imm_o_value => Sret (BzeenoPipeline.ImmDecode.mtrs : MTrs)
    | cmp_o_lt => Sret (BzeenoPipeline.Comparator.mtrs : MTrs)
    | alu_o_result => Sret (BzeenoPipeline.ALU.mtrs : MTrs)
    | mux3_o_data => Sret (BzeenoPipeline.Mux3.mtrs : MTrs)
    | mux4_o_data => Sret (BzeenoPipeline.Mux4.mtrs : MTrs)
    | cla_o_sum => Sret (BzeenoPipeline.CLA32.mtrs : MTrs)
    | rf_array => Sret (BzeenoPipeline.RegFile.mtrs : MTrs)
    | ctl_o_aluc => Sret (BzeenoControl.mtrs : MTrs)
    | dmem_ram => Sret (BzeenoPipeline.DataMem.mtrs : MTrs)
    | imem_rom => Sret (BzeenoPipeline.InstructionMem.mtrs : MTrs)
    | _ => Fail TrsUndeclared
    end.

  (** A small executable check: known direct children resolve, while an
      unrelated signal remains undeclared. *)
  Example etrs_pc : etrs pc_o_pc = Sret (BzeenoPipeline.PCReg.mtrs : MTrs).
  Proof. reflexivity. Qed.

  Example etrs_control : etrs ctl_o_aluc = Sret (BzeenoControl.mtrs : MTrs).
  Proof. reflexivity. Qed.

  Example etrs_unknown : etrs pc_i_clk = Fail TrsUndeclared.
  Proof. reflexivity. Qed.
  End Registry.
End BzeenoCore.
