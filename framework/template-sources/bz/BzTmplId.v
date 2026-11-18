(** Bzeeno: ID-stage controller facts per instruction class (tools/cpu_tmpl_bzid.py). proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import coqutil.Z.BitOps Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVBankAlignment Lang.ExtendedSVSymExec GeneratedRuntimeInput.ConfiguredAST
 Ex.External.CPUClassTableInverse Ex.External.CPUDatapathFacts Ex.External.CPUISARegView Ex.External.CPUJumpFamilyProgramDomain Ex.External.CPUImmediateShapes
 Ex.External.CV32E40PBranchISACondition
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Spec.Decode
 TmplBzLink.BzTmplLink TmplBzCtlIn.BzTmplCtlIn TmplBzDisp.BzTmplDisp TmplBzDisp2.BzTmplDisp2 TmplBzFlow.BzTmplFlow TmplBzExCmp.BzTmplExCmp TmplBzExIface.BzTmplExIface.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVBankAlignment CPUDatapathFacts CPUISARegView BzTmplLink BzTmplCtlIn CV32E40PBranchISACondition BzeenoLoadUseJalASTConfigured3122be4a95.
Local Open Scope Z_scope.
Module BzTmplId.
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

Definition IC (d : State) (i : Decode.InstructionI) : Prop :=
 norm 1 (read_signal d 163%nat) = 0 /\ norm 1 (read_signal d 164%nat) = 0 /\ norm 1 (read_signal d 168%nat) = (match i with
   | Decode.Add _ _ _ => 0
   | Decode.Sub _ _ _ => 0
   | Decode.Sll _ _ _ => 0
   | Decode.Slt _ _ _ => 0
   | Decode.Sltu _ _ _ => 0
   | Decode.Xor _ _ _ => 0
   | Decode.Srl _ _ _ => 0
   | Decode.Sra _ _ _ => 0
   | Decode.Or _ _ _ => 0
   | Decode.And _ _ _ => 0
   | Decode.Addi _ _ _ => 1
   | Decode.Slti _ _ _ => 1
   | Decode.Sltiu _ _ _ => 1
   | Decode.Xori _ _ _ => 1
   | Decode.Ori _ _ _ => 1
   | Decode.Andi _ _ _ => 1
   | Decode.Slli _ _ _ => 0
   | Decode.Srli _ _ _ => 0
   | Decode.Srai _ _ _ => 0
   | Decode.Lui _ _ => 0
   | Decode.Auipc _ _ => 1
   | Decode.Jal _ _ => 1
   | Decode.Jalr _ _ _ => 1
   | Decode.Beq _ _ _ => 1
   | Decode.Bne _ _ _ => 1
   | Decode.Blt _ _ _ => 1
   | Decode.Bge _ _ _ => 1
   | Decode.Bltu _ _ _ => 1
   | Decode.Bgeu _ _ _ => 1
   | _ => 0 end) /\
 match i with
 | Decode.Add _ _ _ => Fw.Fl d 0 0 0
 | Decode.Sub _ _ _ => Fw.Fl d 0 0 0
 | Decode.Sll _ _ _ => Fw.Fl d 0 0 0
 | Decode.Slt _ _ _ => Fw.Fl d 0 0 0
 | Decode.Sltu _ _ _ => Fw.Fl d 0 0 0
 | Decode.Xor _ _ _ => Fw.Fl d 0 0 0
 | Decode.Srl _ _ _ => Fw.Fl d 0 0 0
 | Decode.Sra _ _ _ => Fw.Fl d 0 0 0
 | Decode.Or _ _ _ => Fw.Fl d 0 0 0
 | Decode.And _ _ _ => Fw.Fl d 0 0 0
 | Decode.Addi _ _ _ => Fw.Fl d 0 0 0
 | Decode.Slti _ _ _ => Fw.Fl d 0 0 0
 | Decode.Sltiu _ _ _ => Fw.Fl d 0 0 0
 | Decode.Xori _ _ _ => Fw.Fl d 0 0 0
 | Decode.Ori _ _ _ => Fw.Fl d 0 0 0
 | Decode.Andi _ _ _ => Fw.Fl d 0 0 0
 | Decode.Slli _ _ _ => Fw.Fl d 0 0 0
 | Decode.Srli _ _ _ => Fw.Fl d 0 0 0
 | Decode.Srai _ _ _ => Fw.Fl d 0 0 0
 | Decode.Lui _ _ => Fw.Fl d 0 0 0
 | Decode.Auipc _ _ => Fw.Fl d 0 0 0
 | Decode.Jal _ _ => Fw.Fl d 1 2 0
 | Decode.Jalr _ _ _ => Fw.Fl d 1 1 1
 | Decode.Beq _ _ _ => norm 1 (read_signal d 174%nat) = 1 /\ norm 1 (read_signal d 175%nat) = 0 /\ ((norm 1 (read_signal d 149%nat) = 0 -> Fw.Fl d 0 0 0) /\ (norm 1 (read_signal d 149%nat) = 1 -> Fw.Fl d 1 1 0))
 | Decode.Bne _ _ _ => norm 1 (read_signal d 174%nat) = 1 /\ norm 1 (read_signal d 175%nat) = 0 /\ ((norm 1 (read_signal d 149%nat) = 0 -> Fw.Fl d 1 1 0) /\ (norm 1 (read_signal d 149%nat) = 1 -> Fw.Fl d 0 0 0))
 | Decode.Blt _ _ _ => norm 1 (read_signal d 174%nat) = 1 /\ norm 1 (read_signal d 175%nat) = 0 /\ ((norm 1 (read_signal d 148%nat) = 0 -> Fw.Fl d 0 0 0) /\ (norm 1 (read_signal d 148%nat) = 1 -> Fw.Fl d 1 1 0))
 | Decode.Bge _ _ _ => norm 1 (read_signal d 174%nat) = 1 /\ norm 1 (read_signal d 175%nat) = 0 /\ ((norm 1 (read_signal d 148%nat) = 0 -> Fw.Fl d 1 1 0) /\ (norm 1 (read_signal d 148%nat) = 1 -> Fw.Fl d 0 0 0))
 | Decode.Bltu _ _ _ => norm 1 (read_signal d 174%nat) = 0 /\ norm 1 (read_signal d 175%nat) = 0 /\ ((norm 1 (read_signal d 148%nat) = 0 -> Fw.Fl d 0 0 0) /\ (norm 1 (read_signal d 148%nat) = 1 -> Fw.Fl d 1 1 0))
 | Decode.Bgeu _ _ _ => norm 1 (read_signal d 174%nat) = 0 /\ norm 1 (read_signal d 175%nat) = 0 /\ ((norm 1 (read_signal d 148%nat) = 0 -> Fw.Fl d 1 1 0) /\ (norm 1 (read_signal d 148%nat) = 1 -> Fw.Fl d 0 0 0))
 | _ => False end.
Lemma ic_Add seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Add a0 a1 a2) -> IC d (Decode.Add a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Add w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Add_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Add_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Sub seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Sub a0 a1 a2) -> IC d (Decode.Sub a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Sub w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Sub_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Sub_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Sll seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Sll a0 a1 a2) -> IC d (Decode.Sll a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Sll w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Sll_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Sll_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Slt seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Slt a0 a1 a2) -> IC d (Decode.Slt a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Slt w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Slt_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Slt_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Sltu seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Sltu a0 a1 a2) -> IC d (Decode.Sltu a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Sltu w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Sltu_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Sltu_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Xor seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Xor a0 a1 a2) -> IC d (Decode.Xor a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Xor w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Xor_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Xor_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Srl seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Srl a0 a1 a2) -> IC d (Decode.Srl a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Srl w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Srl_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Srl_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Sra seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Sra a0 a1 a2) -> IC d (Decode.Sra a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Sra w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Sra_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Sra_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Or seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Or a0 a1 a2) -> IC d (Decode.Or a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Or w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Or_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Or_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_And seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.And a0 a1 a2) -> IC d (Decode.And a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_And w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.And_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.And_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Addi seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Addi a0 a1 a2) -> IC d (Decode.Addi a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Addi w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Addi_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Addi_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Slti seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Slti a0 a1 a2) -> IC d (Decode.Slti a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Slti w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Slti_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Slti_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Sltiu seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Sltiu a0 a1 a2) -> IC d (Decode.Sltiu a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Sltiu w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Sltiu_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Sltiu_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Xori seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Xori a0 a1 a2) -> IC d (Decode.Xori a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Xori w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Xori_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Xori_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Ori seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Ori a0 a1 a2) -> IC d (Decode.Ori a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Ori w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Ori_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Ori_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Andi seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Andi a0 a1 a2) -> IC d (Decode.Andi a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Andi w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Andi_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Andi_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Slli seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Slli a0 a1 a2) -> IC d (Decode.Slli a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Slli w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Slli_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Slli_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Srli seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Srli a0 a1 a2) -> IC d (Decode.Srli a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Srli w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Srli_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Srli_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Srai seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Srai a0 a1 a2) -> IC d (Decode.Srai a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Srai w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Srai_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Srai_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct7 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Lui seed d w a0 a1 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Lui a0 a1) -> IC d (Decode.Lui a0 a1).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Lui w a0 a1 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Lui_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Lui_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Auipc seed d w a0 a1 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Auipc a0 a1) -> IC d (Decode.Auipc a0 a1).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Auipc w a0 a1 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Auipc_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Auipc_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Jal seed d w a0 a1 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Jal a0 a1) -> IC d (Decode.Jal a0 a1).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Jal w a0 a1 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Jal_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Jal_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Jalr seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Jalr a0 a1 a2) -> IC d (Decode.Jalr a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Jalr w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Jalr_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HO.
 pose proof (Fw.Jalr_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.
Qed.
Lemma ic_Beq seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Beq a0 a1 a2) -> IC d (Decode.Beq a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Beq w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Beq_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (Dq.bit_cases (read_signal d 149%nat))) as HO.
 pose proof (Fw.Beq_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. split; [exact H174|]. split; [exact H175|]. exact HF.
Qed.
Lemma ic_Bne seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Bne a0 a1 a2) -> IC d (Decode.Bne a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Bne w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Bne_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (Dq.bit_cases (read_signal d 149%nat))) as HO.
 pose proof (Fw.Bne_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. split; [exact H174|]. split; [exact H175|]. exact HF.
Qed.
Lemma ic_Blt seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Blt a0 a1 a2) -> IC d (Decode.Blt a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Blt w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Blt_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (Dq.bit_cases (read_signal d 148%nat))) as HO.
 pose proof (Fw.Blt_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. split; [exact H174|]. split; [exact H175|]. exact HF.
Qed.
Lemma ic_Bge seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Bge a0 a1 a2) -> IC d (Decode.Bge a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Bge w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Bge_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (Dq.bit_cases (read_signal d 148%nat))) as HO.
 pose proof (Fw.Bge_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. split; [exact H174|]. split; [exact H175|]. exact HF.
Qed.
Lemma ic_Bltu seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Bltu a0 a1 a2) -> IC d (Decode.Bltu a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Bltu w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Bltu_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (Dq.bit_cases (read_signal d 148%nat))) as HO.
 pose proof (Fw.Bltu_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. split; [exact H174|]. split; [exact H175|]. exact HF.
Qed.
Lemma ic_Bgeu seed d w a0 a1 a2 : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Bgeu a0 a1 a2) -> IC d (Decode.Bgeu a0 a1 a2).
Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_Bgeu w a0 a1 a2 Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.
 pose proof (Dp.Bgeu_o seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w)) (Dq.bit_cases (read_signal d 148%nat))) as HO.
 pose proof (Fw.Bgeu_f seed d HL H153 H151 H142 (ltac:(rewrite (link_opcode seed d HL), Hw; slice_goal w)) (ltac:(rewrite (link_funct3 seed d HL), Hw; slice_goal w))) as HF.
 destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].
 unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. split; [exact H174|]. split; [exact H175|]. exact HF.
Qed.
Theorem ic_all seed d w i : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->
 Decode.decode Decode.RV32I w = Decode.IInstruction i -> CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.legal_instruction i = true -> IC d i.
Proof. intros HL Hw H153 H151 H142 Hdec Hleg. destruct i; try (vm_compute in Hleg; discriminate Hleg).
 all: first [ exact (ic_Add seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Sub seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Sll seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Slt seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Sltu seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Xor seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Srl seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Sra seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Or seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_And seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Addi seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Slti seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Sltiu seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Xori seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Ori seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Andi seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Slli seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Srli seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Srai seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Lui seed d w _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Auipc seed d w _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Jal seed d w _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Jalr seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Beq seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Bne seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Blt seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Bge seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Bltu seed d w _ _ _ HL Hw H153 H151 H142 Hdec) | exact (ic_Bgeu seed d w _ _ _ HL Hw H153 H151 H142 Hdec) ].
Qed.
Lemma icfp_Add d a0 a1 a2 : IC d (Decode.Add a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Sub d a0 a1 a2 : IC d (Decode.Sub a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Sll d a0 a1 a2 : IC d (Decode.Sll a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Slt d a0 a1 a2 : IC d (Decode.Slt a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Sltu d a0 a1 a2 : IC d (Decode.Sltu a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Xor d a0 a1 a2 : IC d (Decode.Xor a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Srl d a0 a1 a2 : IC d (Decode.Srl a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Sra d a0 a1 a2 : IC d (Decode.Sra a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Or d a0 a1 a2 : IC d (Decode.Or a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_And d a0 a1 a2 : IC d (Decode.And a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Addi d a0 a1 a2 : IC d (Decode.Addi a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Slti d a0 a1 a2 : IC d (Decode.Slti a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Sltiu d a0 a1 a2 : IC d (Decode.Sltiu a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Xori d a0 a1 a2 : IC d (Decode.Xori a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Ori d a0 a1 a2 : IC d (Decode.Ori a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Andi d a0 a1 a2 : IC d (Decode.Andi a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Slli d a0 a1 a2 : IC d (Decode.Slli a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Srli d a0 a1 a2 : IC d (Decode.Srli a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Srai d a0 a1 a2 : IC d (Decode.Srai a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Lui d a0 a1 : IC d (Decode.Lui a0 a1) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Auipc d a0 a1 : IC d (Decode.Auipc a0 a1) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. exact B.
Qed.
Lemma icfp_Jal d a0 a1 : IC d (Decode.Jal a0 a1) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. rewrite A in H157; discriminate H157.
Qed.
Lemma icfp_Jalr d a0 a1 a2 : IC d (Decode.Jalr a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [A [B C]]]]] H157. rewrite A in H157; discriminate H157.
Qed.
Lemma icfp_Beq d a0 a1 a2 : IC d (Decode.Beq a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [_ [_ [H0 H1]]]]]] H157. destruct (Dq.bit_cases (read_signal d 149%nat)) as [Hb|Hb].
 - destruct (H0 Hb) as [A [B C]]. exact B.
 - destruct (H1 Hb) as [A [B C]]. rewrite A in H157; discriminate H157.
Qed.
Lemma icfp_Bne d a0 a1 a2 : IC d (Decode.Bne a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [_ [_ [H0 H1]]]]]] H157. destruct (Dq.bit_cases (read_signal d 149%nat)) as [Hb|Hb].
 - destruct (H0 Hb) as [A [B C]]. rewrite A in H157; discriminate H157.
 - destruct (H1 Hb) as [A [B C]]. exact B.
Qed.
Lemma icfp_Blt d a0 a1 a2 : IC d (Decode.Blt a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [_ [_ [H0 H1]]]]]] H157. destruct (Dq.bit_cases (read_signal d 148%nat)) as [Hb|Hb].
 - destruct (H0 Hb) as [A [B C]]. exact B.
 - destruct (H1 Hb) as [A [B C]]. rewrite A in H157; discriminate H157.
Qed.
Lemma icfp_Bge d a0 a1 a2 : IC d (Decode.Bge a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [_ [_ [H0 H1]]]]]] H157. destruct (Dq.bit_cases (read_signal d 148%nat)) as [Hb|Hb].
 - destruct (H0 Hb) as [A [B C]]. rewrite A in H157; discriminate H157.
 - destruct (H1 Hb) as [A [B C]]. exact B.
Qed.
Lemma icfp_Bltu d a0 a1 a2 : IC d (Decode.Bltu a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [_ [_ [H0 H1]]]]]] H157. destruct (Dq.bit_cases (read_signal d 148%nat)) as [Hb|Hb].
 - destruct (H0 Hb) as [A [B C]]. exact B.
 - destruct (H1 Hb) as [A [B C]]. rewrite A in H157; discriminate H157.
Qed.
Lemma icfp_Bgeu d a0 a1 a2 : IC d (Decode.Bgeu a0 a1 a2) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros [_ [_ [_ [_ [_ [H0 H1]]]]]] H157. destruct (Dq.bit_cases (read_signal d 148%nat)) as [Hb|Hb].
 - destruct (H0 Hb) as [A [B C]]. rewrite A in H157; discriminate H157.
 - destruct (H1 Hb) as [A [B C]]. exact B.
Qed.
Theorem ic_fp d i : CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.legal_instruction i = true -> IC d i -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.
Proof. intros Hleg HI H157. destruct i; try (vm_compute in Hleg; discriminate Hleg).
 all: first [ exact (icfp_Add _ _ _ _ HI H157) | exact (icfp_Sub _ _ _ _ HI H157) | exact (icfp_Sll _ _ _ _ HI H157) | exact (icfp_Slt _ _ _ _ HI H157) | exact (icfp_Sltu _ _ _ _ HI H157) | exact (icfp_Xor _ _ _ _ HI H157) | exact (icfp_Srl _ _ _ _ HI H157) | exact (icfp_Sra _ _ _ _ HI H157) | exact (icfp_Or _ _ _ _ HI H157) | exact (icfp_And _ _ _ _ HI H157) | exact (icfp_Addi _ _ _ _ HI H157) | exact (icfp_Slti _ _ _ _ HI H157) | exact (icfp_Sltiu _ _ _ _ HI H157) | exact (icfp_Xori _ _ _ _ HI H157) | exact (icfp_Ori _ _ _ _ HI H157) | exact (icfp_Andi _ _ _ _ HI H157) | exact (icfp_Slli _ _ _ _ HI H157) | exact (icfp_Srli _ _ _ _ HI H157) | exact (icfp_Srai _ _ _ _ HI H157) | exact (icfp_Lui _ _ _ HI H157) | exact (icfp_Auipc _ _ _ HI H157) | exact (icfp_Jal _ _ _ HI H157) | exact (icfp_Jalr _ _ _ _ HI H157) | exact (icfp_Beq _ _ _ _ HI H157) | exact (icfp_Bne _ _ _ _ HI H157) | exact (icfp_Blt _ _ _ _ HI H157) | exact (icfp_Bge _ _ _ _ HI H157) | exact (icfp_Bltu _ _ _ _ HI H157) | exact (icfp_Bgeu _ _ _ _ HI H157) ].
Qed.
Section Br.
Context {word : Interface.word 32} {BW : Bitwidth 32} {word_ok : word.ok word}.
Theorem br_Beq seed d (x y : word) rs1 rs2 imm : CombLFP P seed d -> IC d (Decode.Beq rs1 rs2 imm) -> norm 32 (read_signal d 204%nat) = word.unsigned x -> norm 32 (read_signal d 210%nat) = word.unsigned y ->
 Fw.Fl d (boolz (isa_branch_guard (Decode.Beq rs1 rs2 imm) x y)) (boolz (isa_branch_guard (Decode.Beq rs1 rs2 imm) x y)) 0.
Proof. intros HL HI ha hb. unfold IC in HI. cbn [IC] in HI. destruct HI as [_ [_ [_ [h174 [h175 [HF0 HF1]]]]]].
 pose proof (Ex.Beq_isa seed d x y rs1 rs2 imm HL h174 h175 ha hb) as [Hp _].
 destruct (Dq.bit_cases (read_signal d 149%nat)) as [Hb|Hb].
 - pose proof (HF0 Hb) as HF. rewrite Hb in Hp. assert (E0 : Cm.Beq_pcsrc 0 = 0) by reflexivity. rewrite E0 in Hp. rewrite <- Hp. exact HF.
 - pose proof (HF1 Hb) as HF. rewrite Hb in Hp. assert (E1 : Cm.Beq_pcsrc 1 = 1) by reflexivity. rewrite E1 in Hp. rewrite <- Hp. exact HF.
Qed.
Theorem br_Bne seed d (x y : word) rs1 rs2 imm : CombLFP P seed d -> IC d (Decode.Bne rs1 rs2 imm) -> norm 32 (read_signal d 204%nat) = word.unsigned x -> norm 32 (read_signal d 210%nat) = word.unsigned y ->
 Fw.Fl d (boolz (isa_branch_guard (Decode.Bne rs1 rs2 imm) x y)) (boolz (isa_branch_guard (Decode.Bne rs1 rs2 imm) x y)) 0.
Proof. intros HL HI ha hb. unfold IC in HI. cbn [IC] in HI. destruct HI as [_ [_ [_ [h174 [h175 [HF0 HF1]]]]]].
 pose proof (Ex.Bne_isa seed d x y rs1 rs2 imm HL h174 h175 ha hb) as [Hp _].
 destruct (Dq.bit_cases (read_signal d 149%nat)) as [Hb|Hb].
 - pose proof (HF0 Hb) as HF. rewrite Hb in Hp. assert (E0 : Cm.Bne_pcsrc 0 = 1) by reflexivity. rewrite E0 in Hp. rewrite <- Hp. exact HF.
 - pose proof (HF1 Hb) as HF. rewrite Hb in Hp. assert (E1 : Cm.Bne_pcsrc 1 = 0) by reflexivity. rewrite E1 in Hp. rewrite <- Hp. exact HF.
Qed.
Theorem br_Blt seed d (x y : word) rs1 rs2 imm : CombLFP P seed d -> IC d (Decode.Blt rs1 rs2 imm) -> norm 32 (read_signal d 204%nat) = word.unsigned x -> norm 32 (read_signal d 210%nat) = word.unsigned y ->
 Fw.Fl d (boolz (isa_branch_guard (Decode.Blt rs1 rs2 imm) x y)) (boolz (isa_branch_guard (Decode.Blt rs1 rs2 imm) x y)) 0.
Proof. intros HL HI ha hb. unfold IC in HI. cbn [IC] in HI. destruct HI as [_ [_ [_ [h174 [h175 [HF0 HF1]]]]]].
 pose proof (Ex.Blt_isa seed d x y rs1 rs2 imm HL h174 h175 ha hb) as [Hp _].
 destruct (Dq.bit_cases (read_signal d 148%nat)) as [Hb|Hb].
 - pose proof (HF0 Hb) as HF. rewrite Hb in Hp. assert (E0 : Cm.Blt_pcsrc 0 = 0) by reflexivity. rewrite E0 in Hp. rewrite <- Hp. exact HF.
 - pose proof (HF1 Hb) as HF. rewrite Hb in Hp. assert (E1 : Cm.Blt_pcsrc 1 = 1) by reflexivity. rewrite E1 in Hp. rewrite <- Hp. exact HF.
Qed.
Theorem br_Bge seed d (x y : word) rs1 rs2 imm : CombLFP P seed d -> IC d (Decode.Bge rs1 rs2 imm) -> norm 32 (read_signal d 204%nat) = word.unsigned x -> norm 32 (read_signal d 210%nat) = word.unsigned y ->
 Fw.Fl d (boolz (isa_branch_guard (Decode.Bge rs1 rs2 imm) x y)) (boolz (isa_branch_guard (Decode.Bge rs1 rs2 imm) x y)) 0.
Proof. intros HL HI ha hb. unfold IC in HI. cbn [IC] in HI. destruct HI as [_ [_ [_ [h174 [h175 [HF0 HF1]]]]]].
 pose proof (Ex.Bge_isa seed d x y rs1 rs2 imm HL h174 h175 ha hb) as [Hp _].
 destruct (Dq.bit_cases (read_signal d 148%nat)) as [Hb|Hb].
 - pose proof (HF0 Hb) as HF. rewrite Hb in Hp. assert (E0 : Cm.Bge_pcsrc 0 = 1) by reflexivity. rewrite E0 in Hp. rewrite <- Hp. exact HF.
 - pose proof (HF1 Hb) as HF. rewrite Hb in Hp. assert (E1 : Cm.Bge_pcsrc 1 = 0) by reflexivity. rewrite E1 in Hp. rewrite <- Hp. exact HF.
Qed.
Theorem br_Bltu seed d (x y : word) rs1 rs2 imm : CombLFP P seed d -> IC d (Decode.Bltu rs1 rs2 imm) -> norm 32 (read_signal d 204%nat) = word.unsigned x -> norm 32 (read_signal d 210%nat) = word.unsigned y ->
 Fw.Fl d (boolz (isa_branch_guard (Decode.Bltu rs1 rs2 imm) x y)) (boolz (isa_branch_guard (Decode.Bltu rs1 rs2 imm) x y)) 0.
Proof. intros HL HI ha hb. unfold IC in HI. cbn [IC] in HI. destruct HI as [_ [_ [_ [h174 [h175 [HF0 HF1]]]]]].
 pose proof (Ex.Bltu_isa seed d x y rs1 rs2 imm HL h174 h175 ha hb) as [Hp _].
 destruct (Dq.bit_cases (read_signal d 148%nat)) as [Hb|Hb].
 - pose proof (HF0 Hb) as HF. rewrite Hb in Hp. assert (E0 : Cm.Bltu_pcsrc 0 = 0) by reflexivity. rewrite E0 in Hp. rewrite <- Hp. exact HF.
 - pose proof (HF1 Hb) as HF. rewrite Hb in Hp. assert (E1 : Cm.Bltu_pcsrc 1 = 1) by reflexivity. rewrite E1 in Hp. rewrite <- Hp. exact HF.
Qed.
Theorem br_Bgeu seed d (x y : word) rs1 rs2 imm : CombLFP P seed d -> IC d (Decode.Bgeu rs1 rs2 imm) -> norm 32 (read_signal d 204%nat) = word.unsigned x -> norm 32 (read_signal d 210%nat) = word.unsigned y ->
 Fw.Fl d (boolz (isa_branch_guard (Decode.Bgeu rs1 rs2 imm) x y)) (boolz (isa_branch_guard (Decode.Bgeu rs1 rs2 imm) x y)) 0.
Proof. intros HL HI ha hb. unfold IC in HI. cbn [IC] in HI. destruct HI as [_ [_ [_ [h174 [h175 [HF0 HF1]]]]]].
 pose proof (Ex.Bgeu_isa seed d x y rs1 rs2 imm HL h174 h175 ha hb) as [Hp _].
 destruct (Dq.bit_cases (read_signal d 148%nat)) as [Hb|Hb].
 - pose proof (HF0 Hb) as HF. rewrite Hb in Hp. assert (E0 : Cm.Bgeu_pcsrc 0 = 1) by reflexivity. rewrite E0 in Hp. rewrite <- Hp. exact HF.
 - pose proof (HF1 Hb) as HF. rewrite Hb in Hp. assert (E1 : Cm.Bgeu_pcsrc 1 = 0) by reflexivity. rewrite E1 in Hp. rewrite <- Hp. exact HF.
Qed.
End Br.
End BzTmplId.
Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.
Print Assumptions BzTmplId.IC.
Print Assumptions BzTmplId.ic_all.
Print Assumptions BzTmplId.ic_fp.
Print Assumptions BzTmplId.br_Beq.
Print Assumptions BzTmplId.br_Bne.
Print Assumptions BzTmplId.br_Blt.
Print Assumptions BzTmplId.br_Bge.
Print Assumptions BzTmplId.br_Bltu.
Print Assumptions BzTmplId.br_Bgeu.
