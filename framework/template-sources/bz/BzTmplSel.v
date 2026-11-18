(** Bzeeno: forwarding selects per instruction class (tools/cpu_tmpl_bzid.py --sel). proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import coqutil.Z.BitOps Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVBankAlignment Lang.ExtendedSVSymExec GeneratedRuntimeInput.ConfiguredAST
 Ex.External.CPUClassTableInverse Ex.External.CPUDatapathFacts Ex.External.CPUISARegView Ex.External.CPUJumpFamilyProgramDomain Ex.External.CPUImmediateShapes
 Ex.External.CV32E40PBranchISACondition
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Spec.Decode
 TmplBzLink.BzTmplLink TmplBzCtlIn.BzTmplCtlIn TmplBzDisp.BzTmplDisp TmplBzDisp2.BzTmplDisp2 TmplBzFlow.BzTmplFlow TmplBzExCmp.BzTmplExCmp TmplBzExIface.BzTmplExIface.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVBankAlignment CPUDatapathFacts CPUISARegView BzTmplLink BzTmplCtlIn CV32E40PBranchISACondition BzeenoLoadUseJalASTConfigured3122be4a95.
Local Open Scope Z_scope.
Module BzTmplSel.
Notation P := bzeeno_load_use_jal_program (only parsing).
Module Inv := Ex.External.CPUClassTableInverse.CPUClassTableInverse.
Module Dp := TmplBzDisp2.BzTmplDisp2.BzTmplDisp2.
Module Fw := TmplBzFlow.BzTmplFlow.BzTmplFlow.
Module Dq := TmplBzDisp.BzTmplDisp.BzTmplDisp.
Module Ex := TmplBzExIface.BzTmplExIface.BzTmplExIface.
Module Cm := TmplBzExCmp.BzTmplExCmp.BzTmplExCmp.
Ltac slice_goal w :=
  first [ (rewrite (slice_val w 0 7 ltac:(lia)); cbn; assumption)
        | (rewrite (slice_val w 12 3 ltac:(lia)); cbn; assumption)
        | (rewrite (slice_val w 25 7 ltac:(lia)); cbn; assumption)
        | (rewrite (bs7_shift w ltac:(assumption)); match goal with H : bitSlice w 26 32 = _ |- _ => rewrite H end; reflexivity) ].

Lemma sel_Add seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Add a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Add w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Add_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Sub seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Sub a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Sub w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Sub_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Sll seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Sll a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Sll w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Sll_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Slt seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Slt a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Slt w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Slt_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Sltu seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Sltu a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Sltu w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Sltu_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Xor seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Xor a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Xor w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Xor_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Srl seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Srl a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Srl w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Srl_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Sra seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Sra a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Sra w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Sra_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Or seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Or a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Or w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Or_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_And seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.And a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_And w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.And_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Addi seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Addi a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Addi w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Addi_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Slti seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Slti a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Slti w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Slti_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Sltiu seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Sltiu a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Sltiu w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Sltiu_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Xori seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Xori a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Xori w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Xori_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Ori seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Ori a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Ori w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Ori_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Andi seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Andi a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Andi w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Andi_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Slli seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Slli a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Slli w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Slli_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Srli seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Srli a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Srli w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Srli_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Srai seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Srai a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Srai w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Srai_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Lui seed d w a0 a1 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Lui a0 a1) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Lui w a0 a1 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Lui_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Auipc seed d w a0 a1 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Auipc a0 a1) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Auipc w a0 a1 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Auipc_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Jal seed d w a0 a1 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Jal a0 a1) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Jal w a0 a1 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Jal_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Jalr seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Jalr a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Jalr w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Jalr_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)))).
Qed.
Lemma sel_Beq seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Beq a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Beq w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Beq_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (Dq.bit_cases (read_signal d 149%nat)))).
Qed.
Lemma sel_Bne seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Bne a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Bne w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Bne_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (Dq.bit_cases (read_signal d 149%nat)))).
Qed.
Lemma sel_Blt seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Blt a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Blt w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Blt_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (Dq.bit_cases (read_signal d 148%nat)))).
Qed.
Lemma sel_Bge seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Bge a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Bge w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Bge_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (Dq.bit_cases (read_signal d 148%nat)))).
Qed.
Lemma sel_Bltu seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Bltu a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Bltu w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Bltu_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (Dq.bit_cases (read_signal d 148%nat)))).
Qed.
Lemma sel_Bgeu seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Bgeu a0 a1 a2) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Bgeu w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.Bgeu_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (Dq.bit_cases (read_signal d 148%nat)))).
Qed.
Theorem sel_all seed d w i : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction i -> CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.legal_instruction i = true -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.
Proof. intros HL Hw H153 H151 H142 Hdec Hleg. destruct i; try (vm_compute in Hleg; discriminate Hleg).
 all: first [ exact (sel_Add seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Sub seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Sll seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Slt seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Sltu seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Xor seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Srl seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Sra seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Or seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_And seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Addi seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Slti seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Sltiu seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Xori seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Ori seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Andi seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Slli seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Srli seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Srai seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Lui seed d w _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Auipc seed d w _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Jal seed d w _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Jalr seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Beq seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Bne seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Blt seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Bge seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Bltu seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (sel_Bgeu seed d w _ _ _ HL Hw H153 H151 H142 Hdec) ].
Qed.
End BzTmplSel.
Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.
Print Assumptions BzTmplSel.sel_all.
