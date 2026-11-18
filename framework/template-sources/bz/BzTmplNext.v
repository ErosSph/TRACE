(** Bzeeno ID stage against the ISA step of the ID token (tools/cpu_tmpl_bznext.py; branch classes generated from the class table).
    For the ID token t (cut c, post state `post` of the checked ISA step) and the controller outputs of the driven rise state d:
      flush = 0 -> the ISA next pc is t + 4;   flush <> 0 -> the ISA next pc is the redirect target the RTL computes (wire 130).
    Branches use the operand wires 204/210 (hypothesis OpsOK: they carry the ISA register values of the cut), Jalr (base x0) the wire 204.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import coqutil.Z.BitOps coqutil.Z.bitblast coqutil.Z.prove_Zeq_bitwise Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVBankAlignment
 Ex.External.CPUJumpFamilyProgramDomain Ex.External.CPUJumpFamilyPostShape Ex.External.CPUISARegView Ex.External.CPUClassTableInverse Ex.External.CPUImmediateShapes
 Ex.External.CPUISAJalEffects Ex.External.CPUDatapathFacts Ex.External.CV32E40PReq41Instruction Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PDataOpProgramScope
 Ex.External.CV32E40PJumpFenceExecution Ex.External.CV32E40PBranchExecution Ex.External.CV32E40PBranchISACondition Ex.External.CPUISABranchFamilyEffects
 Ex.RvCore.FormalSpec riscv.Spec.Decode riscv.Utility.Utility GeneratedRuntimeInput.ConfiguredAST
 TmplBzInv.BzTmplInv TmplBzId.BzTmplId TmplBzIsa.BzTmplIsa TmplBzExIface.BzTmplExIface TmplBzFlow.BzTmplFlow
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVBankAlignment CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain CPUJumpFamilyPostShape.CPUJumpFamilyPostShape CV32E40PDataOpProgramScope.CV32E40PDataOpProgramScope CV32E40PReq41Instruction.CV32E40PReq41Instruction
 CV32E40PReq40StateRel.CV32E40PReq40StateRel CV32E40PBranchISACondition.CV32E40PBranchISACondition CV32E40PDataOpExecution.CV32E40PDataOpExecution CPUISARegView.CPUISARegView CPUImmediateShapes BzeenoLoadUseJalASTConfigured3122be4a95.
Local Open Scope Z_scope.
Module BzTmplNext.
Notation P := bzeeno_load_use_jal_program (only parsing).
Module Fw := TmplBzFlow.BzTmplFlow.BzTmplFlow.
Module Ex := TmplBzExIface.BzTmplExIface.BzTmplExIface.
Module Id := TmplBzId.BzTmplId.BzTmplId.
Module Inv := Ex.External.CPUClassTableInverse.CPUClassTableInverse.
Module JF := CV32E40PJumpFenceExecution.CV32E40PJumpFenceExecution.
Module BE := CV32E40PBranchExecution.CV32E40PBranchExecution.
Module JE := CPUISAJalEffects.CPUISAJalEffects.
Section Next.
Context {word : Interface.word 32} {BW : Bitwidth 32} {Registers : map.map Decode.Register word} {Mem : map.map word byte}
 {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.
Local Notation uw := word.unsigned.

(** The operand wires of the ID stage carry the ISA register values of the cut (branches: rs1, rs2; Jalr: rs1). *)
Definition OpsOK (d : State) (c : FormalSpec.State) (i : Decode.InstructionI) : Prop :=
 match i with
 | Decode.Beq rs1 rs2 _ | Decode.Bne rs1 rs2 _ | Decode.Blt rs1 rs2 _ | Decode.Bge rs1 rs2 _ | Decode.Bltu rs1 rs2 _ | Decode.Bgeu rs1 rs2 _ =>
     norm 32 (read_signal d 204%nat) = uw (formal_register_word c rs1) /\ norm 32 (read_signal d 210%nat) = uw (formal_register_word c rs2)
 | Decode.Jalr _ rs1 _ => norm 32 (read_signal d 204%nat) = uw (formal_register_word c rs1)
 | _ => True
 end.

Lemma bit_cases (x : Z) : norm 1 x = 0 \/ norm 1 x = 1.
Proof. pose proof (norm_bounds 1 x) as H. cbn in H. lia. Qed.

Lemma uw_add_of_Z (x : word) k : uw (word.add x (word.of_Z k : word)) = norm 32 (uw x + k).
Proof. rewrite word.unsigned_add, word.unsigned_of_Z. unfold word.wrap. rewrite ExtendedSVBankAlignment.norm_mod. change (2 ^ Z.of_nat 32) with (2 ^ 32). rewrite Z.add_mod_idemp_r by lia. reflexivity. Qed.

Lemma jalr_eq imm : norm 32 (Z.land (0 + imm) (Z.lnot 1)) = jalr_target imm.
Proof. unfold jalr_target. rewrite Z.add_0_l. rewrite norm_ones.
 replace (2 ^ 32 - 2) with (Z.land (Z.ones 32) (Z.lnot 1)) by (vm_compute; reflexivity).
 rewrite <- Z.land_ones by lia. ofnat. prove_Zeq_bitwise. Qed.

Lemma testbit0_aligned t : t mod 4 = 0 -> Z.testbit t 0 = false.
Proof. intro H. rewrite Z.bit0_odd. assert (E : t = 4 * (t / 4)) by (pose proof (Z.div_mod t 4 ltac:(lia)); lia).
 rewrite E, Z.odd_mul. reflexivity. Qed.


(** Branch classes (generated): the ISA next pc of the branch against the flush and the target wire. *)
Lemma np_Beq seed d t c post rs1 rs2 imm w :
 CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 32 (read_signal d 139%nat) = t ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Beq rs1 rs2 imm) ->
 Id.IC d (Decode.Beq rs1 rs2 imm) -> OpsOK d c (Decode.Beq rs1 rs2 imm) ->
 t = uw (getPc c) -> t mod 4 = 0 -> getNextPc c = JE.link c -> post = BE.branch_post c (Decode.Beq rs1 rs2 imm) ->
 (norm 1 (read_signal d 157%nat) = 0 -> uw (getPc post) = norm 32 (t + 4)) /\ (norm 1 (read_signal d 157%nat) <> 0 -> uw (getPc post) = norm 32 (read_signal d 130%nat)).
Proof. intros HL Hw Ht Hdec HI [Hx Hy] Htc Ht4 HN Hp.
 pose proof (Id.br_Beq seed d (formal_register_word c rs1) (formal_register_word c rs2) rs1 rs2 imm HL HI Hx Hy) as [A [B C]].
 destruct HI as [_ [_ [H168 _]]]. cbn in H168.
 destruct (Inv.inv_Beq w rs1 rs2 imm Hdec) as [[_ [_ Himm]] [Hop _]].
 assert (Hlink : uw (getNextPc c) = norm 32 (t + 4)) by (rewrite HN, JE.link_unsigned, ExtendedSVBankAlignment.norm_mod; rewrite Htc; reflexivity).
 assert (Hg : BE.reference_branch_taken c (Decode.Beq rs1 rs2 imm) = isa_branch_guard (Decode.Beq rs1 rs2 imm) (formal_register_word c rs1) (formal_register_word c rs2)) by reflexivity.
 destruct (isa_branch_guard (Decode.Beq rs1 rs2 imm) (formal_register_word c rs1) (formal_register_word c rs2)) eqn:Eg; cbn in A, B.
 - split.
   + intro H157. rewrite A in H157. discriminate H157.
   + intros _. rewrite Hp. unfold BE.branch_post. cbn [getPc]. unfold BE.branch_next_pc. rewrite Hg.
     unfold BE.reference_branch_target. cbn [BE.branch_immediate immediate_field]. rewrite uw_add_of_Z.
     assert (Hpc4 : Z.testbit (norm 32 (read_signal d 139%nat)) 0 = false) by (rewrite Ht; apply testbit0_aligned; exact Ht4).
     rewrite (Ex.Beq_e3 seed d w HL B C Hw Hop H168 Hpc4). rewrite Ht, <- Htc. rewrite Himm. reflexivity.
 - split.
   + intros _. rewrite Hp. unfold BE.branch_post. cbn [getPc]. unfold BE.branch_next_pc. rewrite Hg. exact Hlink.
   + intro H157. rewrite A in H157. contradiction.
Qed.

Lemma np_Bne seed d t c post rs1 rs2 imm w :
 CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 32 (read_signal d 139%nat) = t ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Bne rs1 rs2 imm) ->
 Id.IC d (Decode.Bne rs1 rs2 imm) -> OpsOK d c (Decode.Bne rs1 rs2 imm) ->
 t = uw (getPc c) -> t mod 4 = 0 -> getNextPc c = JE.link c -> post = BE.branch_post c (Decode.Bne rs1 rs2 imm) ->
 (norm 1 (read_signal d 157%nat) = 0 -> uw (getPc post) = norm 32 (t + 4)) /\ (norm 1 (read_signal d 157%nat) <> 0 -> uw (getPc post) = norm 32 (read_signal d 130%nat)).
Proof. intros HL Hw Ht Hdec HI [Hx Hy] Htc Ht4 HN Hp.
 pose proof (Id.br_Bne seed d (formal_register_word c rs1) (formal_register_word c rs2) rs1 rs2 imm HL HI Hx Hy) as [A [B C]].
 destruct HI as [_ [_ [H168 _]]]. cbn in H168.
 destruct (Inv.inv_Bne w rs1 rs2 imm Hdec) as [[_ [_ Himm]] [Hop _]].
 assert (Hlink : uw (getNextPc c) = norm 32 (t + 4)) by (rewrite HN, JE.link_unsigned, ExtendedSVBankAlignment.norm_mod; rewrite Htc; reflexivity).
 assert (Hg : BE.reference_branch_taken c (Decode.Bne rs1 rs2 imm) = isa_branch_guard (Decode.Bne rs1 rs2 imm) (formal_register_word c rs1) (formal_register_word c rs2)) by reflexivity.
 destruct (isa_branch_guard (Decode.Bne rs1 rs2 imm) (formal_register_word c rs1) (formal_register_word c rs2)) eqn:Eg; cbn in A, B.
 - split.
   + intro H157. rewrite A in H157. discriminate H157.
   + intros _. rewrite Hp. unfold BE.branch_post. cbn [getPc]. unfold BE.branch_next_pc. rewrite Hg.
     unfold BE.reference_branch_target. cbn [BE.branch_immediate immediate_field]. rewrite uw_add_of_Z.
     assert (Hpc4 : Z.testbit (norm 32 (read_signal d 139%nat)) 0 = false) by (rewrite Ht; apply testbit0_aligned; exact Ht4).
     rewrite (Ex.Bne_e3 seed d w HL B C Hw Hop H168 Hpc4). rewrite Ht, <- Htc. rewrite Himm. reflexivity.
 - split.
   + intros _. rewrite Hp. unfold BE.branch_post. cbn [getPc]. unfold BE.branch_next_pc. rewrite Hg. exact Hlink.
   + intro H157. rewrite A in H157. contradiction.
Qed.

Lemma np_Blt seed d t c post rs1 rs2 imm w :
 CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 32 (read_signal d 139%nat) = t ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Blt rs1 rs2 imm) ->
 Id.IC d (Decode.Blt rs1 rs2 imm) -> OpsOK d c (Decode.Blt rs1 rs2 imm) ->
 t = uw (getPc c) -> t mod 4 = 0 -> getNextPc c = JE.link c -> post = BE.branch_post c (Decode.Blt rs1 rs2 imm) ->
 (norm 1 (read_signal d 157%nat) = 0 -> uw (getPc post) = norm 32 (t + 4)) /\ (norm 1 (read_signal d 157%nat) <> 0 -> uw (getPc post) = norm 32 (read_signal d 130%nat)).
Proof. intros HL Hw Ht Hdec HI [Hx Hy] Htc Ht4 HN Hp.
 pose proof (Id.br_Blt seed d (formal_register_word c rs1) (formal_register_word c rs2) rs1 rs2 imm HL HI Hx Hy) as [A [B C]].
 destruct HI as [_ [_ [H168 _]]]. cbn in H168.
 destruct (Inv.inv_Blt w rs1 rs2 imm Hdec) as [[_ [_ Himm]] [Hop _]].
 assert (Hlink : uw (getNextPc c) = norm 32 (t + 4)) by (rewrite HN, JE.link_unsigned, ExtendedSVBankAlignment.norm_mod; rewrite Htc; reflexivity).
 assert (Hg : BE.reference_branch_taken c (Decode.Blt rs1 rs2 imm) = isa_branch_guard (Decode.Blt rs1 rs2 imm) (formal_register_word c rs1) (formal_register_word c rs2)) by reflexivity.
 destruct (isa_branch_guard (Decode.Blt rs1 rs2 imm) (formal_register_word c rs1) (formal_register_word c rs2)) eqn:Eg; cbn in A, B.
 - split.
   + intro H157. rewrite A in H157. discriminate H157.
   + intros _. rewrite Hp. unfold BE.branch_post. cbn [getPc]. unfold BE.branch_next_pc. rewrite Hg.
     unfold BE.reference_branch_target. cbn [BE.branch_immediate immediate_field]. rewrite uw_add_of_Z.
     assert (Hpc4 : Z.testbit (norm 32 (read_signal d 139%nat)) 0 = false) by (rewrite Ht; apply testbit0_aligned; exact Ht4).
     rewrite (Ex.Blt_e3 seed d w HL B C Hw Hop H168 Hpc4). rewrite Ht, <- Htc. rewrite Himm. reflexivity.
 - split.
   + intros _. rewrite Hp. unfold BE.branch_post. cbn [getPc]. unfold BE.branch_next_pc. rewrite Hg. exact Hlink.
   + intro H157. rewrite A in H157. contradiction.
Qed.

Lemma np_Bge seed d t c post rs1 rs2 imm w :
 CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 32 (read_signal d 139%nat) = t ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Bge rs1 rs2 imm) ->
 Id.IC d (Decode.Bge rs1 rs2 imm) -> OpsOK d c (Decode.Bge rs1 rs2 imm) ->
 t = uw (getPc c) -> t mod 4 = 0 -> getNextPc c = JE.link c -> post = BE.branch_post c (Decode.Bge rs1 rs2 imm) ->
 (norm 1 (read_signal d 157%nat) = 0 -> uw (getPc post) = norm 32 (t + 4)) /\ (norm 1 (read_signal d 157%nat) <> 0 -> uw (getPc post) = norm 32 (read_signal d 130%nat)).
Proof. intros HL Hw Ht Hdec HI [Hx Hy] Htc Ht4 HN Hp.
 pose proof (Id.br_Bge seed d (formal_register_word c rs1) (formal_register_word c rs2) rs1 rs2 imm HL HI Hx Hy) as [A [B C]].
 destruct HI as [_ [_ [H168 _]]]. cbn in H168.
 destruct (Inv.inv_Bge w rs1 rs2 imm Hdec) as [[_ [_ Himm]] [Hop _]].
 assert (Hlink : uw (getNextPc c) = norm 32 (t + 4)) by (rewrite HN, JE.link_unsigned, ExtendedSVBankAlignment.norm_mod; rewrite Htc; reflexivity).
 assert (Hg : BE.reference_branch_taken c (Decode.Bge rs1 rs2 imm) = isa_branch_guard (Decode.Bge rs1 rs2 imm) (formal_register_word c rs1) (formal_register_word c rs2)) by reflexivity.
 destruct (isa_branch_guard (Decode.Bge rs1 rs2 imm) (formal_register_word c rs1) (formal_register_word c rs2)) eqn:Eg; cbn in A, B.
 - split.
   + intro H157. rewrite A in H157. discriminate H157.
   + intros _. rewrite Hp. unfold BE.branch_post. cbn [getPc]. unfold BE.branch_next_pc. rewrite Hg.
     unfold BE.reference_branch_target. cbn [BE.branch_immediate immediate_field]. rewrite uw_add_of_Z.
     assert (Hpc4 : Z.testbit (norm 32 (read_signal d 139%nat)) 0 = false) by (rewrite Ht; apply testbit0_aligned; exact Ht4).
     rewrite (Ex.Bge_e3 seed d w HL B C Hw Hop H168 Hpc4). rewrite Ht, <- Htc. rewrite Himm. reflexivity.
 - split.
   + intros _. rewrite Hp. unfold BE.branch_post. cbn [getPc]. unfold BE.branch_next_pc. rewrite Hg. exact Hlink.
   + intro H157. rewrite A in H157. contradiction.
Qed.

Lemma np_Bltu seed d t c post rs1 rs2 imm w :
 CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 32 (read_signal d 139%nat) = t ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Bltu rs1 rs2 imm) ->
 Id.IC d (Decode.Bltu rs1 rs2 imm) -> OpsOK d c (Decode.Bltu rs1 rs2 imm) ->
 t = uw (getPc c) -> t mod 4 = 0 -> getNextPc c = JE.link c -> post = BE.branch_post c (Decode.Bltu rs1 rs2 imm) ->
 (norm 1 (read_signal d 157%nat) = 0 -> uw (getPc post) = norm 32 (t + 4)) /\ (norm 1 (read_signal d 157%nat) <> 0 -> uw (getPc post) = norm 32 (read_signal d 130%nat)).
Proof. intros HL Hw Ht Hdec HI [Hx Hy] Htc Ht4 HN Hp.
 pose proof (Id.br_Bltu seed d (formal_register_word c rs1) (formal_register_word c rs2) rs1 rs2 imm HL HI Hx Hy) as [A [B C]].
 destruct HI as [_ [_ [H168 _]]]. cbn in H168.
 destruct (Inv.inv_Bltu w rs1 rs2 imm Hdec) as [[_ [_ Himm]] [Hop _]].
 assert (Hlink : uw (getNextPc c) = norm 32 (t + 4)) by (rewrite HN, JE.link_unsigned, ExtendedSVBankAlignment.norm_mod; rewrite Htc; reflexivity).
 assert (Hg : BE.reference_branch_taken c (Decode.Bltu rs1 rs2 imm) = isa_branch_guard (Decode.Bltu rs1 rs2 imm) (formal_register_word c rs1) (formal_register_word c rs2)) by reflexivity.
 destruct (isa_branch_guard (Decode.Bltu rs1 rs2 imm) (formal_register_word c rs1) (formal_register_word c rs2)) eqn:Eg; cbn in A, B.
 - split.
   + intro H157. rewrite A in H157. discriminate H157.
   + intros _. rewrite Hp. unfold BE.branch_post. cbn [getPc]. unfold BE.branch_next_pc. rewrite Hg.
     unfold BE.reference_branch_target. cbn [BE.branch_immediate immediate_field]. rewrite uw_add_of_Z.
     assert (Hpc4 : Z.testbit (norm 32 (read_signal d 139%nat)) 0 = false) by (rewrite Ht; apply testbit0_aligned; exact Ht4).
     rewrite (Ex.Bltu_e3 seed d w HL B C Hw Hop H168 Hpc4). rewrite Ht, <- Htc. rewrite Himm. reflexivity.
 - split.
   + intros _. rewrite Hp. unfold BE.branch_post. cbn [getPc]. unfold BE.branch_next_pc. rewrite Hg. exact Hlink.
   + intro H157. rewrite A in H157. contradiction.
Qed.

Lemma np_Bgeu seed d t c post rs1 rs2 imm w :
 CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 32 (read_signal d 139%nat) = t ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.Bgeu rs1 rs2 imm) ->
 Id.IC d (Decode.Bgeu rs1 rs2 imm) -> OpsOK d c (Decode.Bgeu rs1 rs2 imm) ->
 t = uw (getPc c) -> t mod 4 = 0 -> getNextPc c = JE.link c -> post = BE.branch_post c (Decode.Bgeu rs1 rs2 imm) ->
 (norm 1 (read_signal d 157%nat) = 0 -> uw (getPc post) = norm 32 (t + 4)) /\ (norm 1 (read_signal d 157%nat) <> 0 -> uw (getPc post) = norm 32 (read_signal d 130%nat)).
Proof. intros HL Hw Ht Hdec HI [Hx Hy] Htc Ht4 HN Hp.
 pose proof (Id.br_Bgeu seed d (formal_register_word c rs1) (formal_register_word c rs2) rs1 rs2 imm HL HI Hx Hy) as [A [B C]].
 destruct HI as [_ [_ [H168 _]]]. cbn in H168.
 destruct (Inv.inv_Bgeu w rs1 rs2 imm Hdec) as [[_ [_ Himm]] [Hop _]].
 assert (Hlink : uw (getNextPc c) = norm 32 (t + 4)) by (rewrite HN, JE.link_unsigned, ExtendedSVBankAlignment.norm_mod; rewrite Htc; reflexivity).
 assert (Hg : BE.reference_branch_taken c (Decode.Bgeu rs1 rs2 imm) = isa_branch_guard (Decode.Bgeu rs1 rs2 imm) (formal_register_word c rs1) (formal_register_word c rs2)) by reflexivity.
 destruct (isa_branch_guard (Decode.Bgeu rs1 rs2 imm) (formal_register_word c rs1) (formal_register_word c rs2)) eqn:Eg; cbn in A, B.
 - split.
   + intro H157. rewrite A in H157. discriminate H157.
   + intros _. rewrite Hp. unfold BE.branch_post. cbn [getPc]. unfold BE.branch_next_pc. rewrite Hg.
     unfold BE.reference_branch_target. cbn [BE.branch_immediate immediate_field]. rewrite uw_add_of_Z.
     assert (Hpc4 : Z.testbit (norm 32 (read_signal d 139%nat)) 0 = false) by (rewrite Ht; apply testbit0_aligned; exact Ht4).
     rewrite (Ex.Bgeu_e3 seed d w HL B C Hw Hop H168 Hpc4). rewrite Ht, <- Htc. rewrite Himm. reflexivity.
 - split.
   + intros _. rewrite Hp. unfold BE.branch_post. cbn [getPc]. unfold BE.branch_next_pc. rewrite Hg. exact Hlink.
   + intro H157. rewrite A in H157. contradiction.
Qed.


Theorem np_branch seed d t c post op rs1 rs2 imm w :
 CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 32 (read_signal d 139%nat) = t ->
 Decode.decode Decode.RV32I w = Decode.IInstruction (CPUISABranchFamilyEffects.instruction op rs1 rs2 imm) ->
 Id.IC d (CPUISABranchFamilyEffects.instruction op rs1 rs2 imm) -> OpsOK d c (CPUISABranchFamilyEffects.instruction op rs1 rs2 imm) ->
 t = uw (getPc c) -> t mod 4 = 0 -> getNextPc c = JE.link c -> post = BE.branch_post c (CPUISABranchFamilyEffects.instruction op rs1 rs2 imm) ->
 (norm 1 (read_signal d 157%nat) = 0 -> uw (getPc post) = norm 32 (t + 4)) /\ (norm 1 (read_signal d 157%nat) <> 0 -> uw (getPc post) = norm 32 (read_signal d 130%nat)).
Proof. intros HL Hw Ht Hdec HI HO Htc Ht4 HN Hp. destruct op; cbn [CPUISABranchFamilyEffects.instruction] in *.
 - exact (np_Beq seed d t c post rs1 rs2 imm w HL Hw Ht Hdec HI HO Htc Ht4 HN Hp).
 - exact (np_Bne seed d t c post rs1 rs2 imm w HL Hw Ht Hdec HI HO Htc Ht4 HN Hp).
 - exact (np_Blt seed d t c post rs1 rs2 imm w HL Hw Ht Hdec HI HO Htc Ht4 HN Hp).
 - exact (np_Bge seed d t c post rs1 rs2 imm w HL Hw Ht Hdec HI HO Htc Ht4 HN Hp).
 - exact (np_Bltu seed d t c post rs1 rs2 imm w HL Hw Ht Hdec HI HO Htc Ht4 HN Hp).
 - exact (np_Bgeu seed d t c post rs1 rs2 imm w HL Hw Ht Hdec HI HO Htc Ht4 HN Hp).
Qed.

Lemma ic_data d i : DataOp21 i -> Id.IC d i -> Fw.Fl d 0 0 0.
Proof. intros H [_ [_ [_ I]]]. destruct i; cbn [DataOp21 dataop21b] in H; try discriminate; exact I. Qed.

(** The ISA next pc of the ID token against the RTL (any legal instruction of the checked domain). *)
Theorem next_pc seed d words (HC : check_program words = true) t c post i w :
 CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 32 (read_signal d 139%nat) = t ->
 Decode.decode Decode.RV32I w = Decode.IInstruction i -> BzTmplInv.iword words t = w ->
 Id.IC d i -> OpsOK d c i -> AtProgram words (Z.to_nat (t / 4)) c -> t = uw (getPc c) -> FormalSpec.run1 c = (Some tt, post) ->
 (norm 1 (read_signal d 157%nat) = 0 -> uw (getPc post) = norm 32 (t + 4)) /\ (norm 1 (read_signal d 157%nat) <> 0 -> uw (getPc post) = norm 32 (read_signal d 130%nat)).
Proof.
 intros HL Hw Ht Hdec Hiw HI HO HAt Htc Hrun.
 destruct (checked_post_shape words (Z.to_nat (t / 4)) c post HC HAt Hrun) as [i' [HD' Hfam]].
 destruct (checked_entry words (Z.to_nat (t / 4)) HC (proj1 HAt)) as [i0 [HD0 [HB0 [HL0 _]]]].
 assert (Hnth : w = nth (Z.to_nat (t / 4)) words 0) by (rewrite <- Hiw; unfold BzTmplInv.iword; exact (BzTmplIsa.norm32_small _ HB0)).
 pose proof Hdec as Hdec0. rewrite Hnth in Hdec. rewrite HD0 in Hdec. injection Hdec as Hi0. subst i0. rewrite HD0 in HD'. injection HD' as Hi'. subst i'.
 destruct HAt as [Hidx [Hpc [Hmem HNX]]].
 assert (Ht4 : t mod 4 = 0) by (rewrite Htc, Hpc; rewrite Z.mul_comm; apply Z.mod_mul; lia).
 assert (HN : getNextPc c = JE.link c) by exact HNX.
 assert (Hlink : uw (getNextPc c) = norm 32 (t + 4)) by (rewrite HN, JE.link_unsigned, ExtendedSVBankAlignment.norm_mod; rewrite Htc; reflexivity).
 destruct Hfam as [[HD Hafter]|[[r [imm [Hj Hafter]]]|[[r [imm [Hj Hafter]]]|[op [rs1 [rs2 [imm [Hj Hafter]]]]]]]].
 - destruct (ic_data _ _ HD HI) as [A [B C]]. split.
   + intros _. rewrite Hafter. unfold dataop_post. cbn [getPc]. exact Hlink.
   + intro H157. rewrite A in H157. contradiction.
 - subst i. destruct HI as [_ [_ [H168 HF]]]. cbn in HF. destruct HF as [A [B C]]. split.
   + intro H157. rewrite A in H157. discriminate H157.
   + intros _. destruct (Inv.inv_Jal w r imm Hdec0) as [[_ Himm] Hop].
     rewrite Hafter. unfold JF.jump_post. cbn [getPc]. unfold JF.reference_jump_target.
     rewrite uw_add_of_Z. rewrite (Ex.Jal_e3 seed d w HL B Hw Hop H168), Ht, <- Htc. rewrite Himm. reflexivity.
 - subst i. destruct HI as [_ [_ [H168 HF]]]. cbn in HF. destruct HF as [A [B C]]. split.
   + intro H157. rewrite A in H157. discriminate H157.
   + intros _. destruct (Inv.inv_Jalr w r 0 imm Hdec0) as [[_ [_ Himm]] [Hop _]].
     rewrite Hafter. unfold JF.jump_post. cbn [getPc]. rewrite jalr_x0_target_unsigned.
     rewrite (Ex.Jalr_e3 seed d w HL B C Hw Hop H168). simpl in HO. rewrite HO.
     rewrite (view_formal c 0). unfold isa_view. cbn [regs_view]. cbn. rewrite Himm. rewrite <- jalr_eq. reflexivity.
 - subst i. eapply np_branch; try eassumption; reflexivity.
Qed.
End Next.
End BzTmplNext.
Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.
Print Assumptions BzTmplNext.next_pc.
Print Assumptions BzTmplNext.jalr_eq.
Print Assumptions BzTmplNext.uw_add_of_Z.
