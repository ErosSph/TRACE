(** Mixed 21 data-op + six branch ROM scope and symbolic ISA preservation.
    This is ONLY the reference/program side, not CPU cycle preservation or
    infinite RTL refinement. Branch offsets are four-byte aligned; operands
    are obtained from real decode legality, never stipulated by the caller. *)
From Coq Require Import ZArith List Lia.
Require Import Ex.External.CV32E40PDataOpProgramScope Ex.External.CV32E40PDataOpExecution
  Ex.External.CV32E40PDataOpISAInvariant Ex.External.CV32E40PBranchExecution
  Ex.External.CV32E40PBranchTargetAlignment Ex.External.CV32E40PReq41Instruction
  Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PAddiNopROM
  Ex.External.CV32E40PAddiNopISAInvariant Ex.External.CV32E40PReq39Trace.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine riscv.Proofs.VerifyDecode.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte.
Import ListNotations CV32E40PDataOpProgramScope CV32E40PDataOpExecution
  CV32E40PDataOpISAInvariant CV32E40PBranchExecution CV32E40PBranchTargetAlignment
  CV32E40PReq41Instruction CV32E40PReq40StateRel CV32E40PAddiNopROM
  CV32E40PAddiNopISAInvariant CV32E40PReq39Trace.
Local Open Scope Z_scope.
Module CV32E40PBranchProgramScope.
Definition ScopedInstruction i := DataOp21 i \/
  (InFamily FamilyBranch i /\ branch_immediate i mod 4 = 0).
Definition GoodBranch code : Prop := exists i, InFamily FamilyBranch i /\
  branch_immediate i mod 4 = 0 /\
  Decode.decode Decode.RV32I (code mod 2^32) = Decode.IInstruction i.
Definition GoodDataBranch code := GoodDataOp code \/ GoodBranch code.
Definition DataBranchProgram image := Forall GoodDataBranch image.

Lemma branch_decoded_operands_legal code i : InFamily FamilyBranch i ->
  Decode.decode Decode.RV32I code = Decode.IInstruction i -> LegalOperands i.
Proof.
  intros HI HE.
  destruct (verify_decode Decode.RV32I code eq_refl) as [HV|HB]; [rewrite HE in HV|congruence].
  destruct i; cbn [InFamily family_of] in HI; try discriminate.
  all: cbv [verify respects_bounds apply_InstructionMapper Verifier map_SB
    verify_SB bitwidth verify_iset] in HV.
  all: unfold LegalOperands; cbn [destination_register source_registers];
    repeat constructor; unfold legal_reg; intuition lia.
Qed.
Lemma nop_in_data_branch_scope : GoodDataBranch nop.
Proof. left. exact nop_in_scope. Qed.
Theorem dataop_scope_included image : DataOpProgram image -> DataBranchProgram image.
Proof. intros H. induction H; constructor; auto. now left. Qed.
Lemma nth_data_branch_scope image n : DataBranchProgram image -> GoodDataBranch (nth n image nop).
Proof.
  intros H. induction H in n |- *; destruct n; cbn; auto using nop_in_data_branch_scope.
Qed.
Theorem arbitrary_address_data_branch_scope image pc : DataBranchProgram image ->
  GoodDataBranch (instruction_from_image image pc).
Proof.
  intros H. unfold instruction_from_image.
  destruct (andb (Z.leb 0 pc) (Z.eqb (pc mod 4) 0));
    auto using nth_data_branch_scope, nop_in_data_branch_scope.
Qed.
Lemma scoped_decoded_instruction code : GoodDataBranch code ->
  exists i, ScopedInstruction i /\ LegalOperands i /\
    Decode.decode Decode.RV32I (code mod 2^32) = Decode.IInstruction i.
Proof.
  intros [(i & HI & HD)|(i & HI & HA & HD)]; exists i.
  - split; [now left|]. split; [eapply decoded_operands_legal; eauto|exact HD].
  - split; [right; auto|]. split; [eapply branch_decoded_operands_legal; eauto|exact HD].
Qed.
Section ISA.
Context {word : Interface.word 32} {BW : Bitwidth 32}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.
#[local] Opaque nop_rom.
Theorem data_branch_current_instruction image (s : FormalSpec.State) :
  DataBranchProgram image -> ISAInvariant image s ->
  exists i, ScopedInstruction i /\ LegalOperands i /\ CurrentInstruction s i.
Proof.
  intros HP (HM & HA & HN).
  destruct (scoped_decoded_instruction _
    (arbitrary_address_data_branch_scope image (word.unsigned (getPc s)) HP))
    as (i & HI & HL & HD).
  exists i. split; [exact HI|]. split; [exact HL|].
  constructor; [exact HA|].
  exists (LittleEndian.split 4 (instruction_from_image image (word.unsigned (getPc s)))).
  split; [rewrite HM; now apply nop_rom_fetch|].
  rewrite LittleEndian.combine_split. exact HD.
Qed.
Theorem mixed_data_branch_step image (s : FormalSpec.State) :
  DataBranchProgram image -> ISAInvariant image s ->
  exists i s', ScopedInstruction i /\ CurrentInstruction s i /\
    FormalSpec.run1 s = (Some tt, s') /\ ISAInvariant image s' /\
    getInstMem s' = getInstMem s /\ getDataMem s' = getDataMem s.
Proof.
  intros HP HS. destruct (data_branch_current_instruction image s HP HS) as (i & HI & HL & HC).
  destruct HI as [HD|[HB HA]].
  - destruct (run1_preserves_shape image s i HD HL HC HS) as (s' & HR & HInv & HM).
    exists i, s'. split; [now left|]. auto.
  - destruct (four_byte_branch_run1_and_frame image s i HB HL HC HA HS)
      as (HR & HInv & HRegs & HROM & HRAM).
    exists i, (branch_post s i). split; [right; auto|]. auto.
Qed.
Theorem arbitrary_finite_data_branch_isa_progress image s n :
  DataBranchProgram image -> ISAInvariant image s ->
  exists s', ISARuns n s s' /\ ISAInvariant image s' /\
    getInstMem s' = getInstMem s /\ getDataMem s' = getDataMem s.
Proof.
  intros HP. induction n as [|n IH] in s |- *; intros HS.
  - exists s. split; [constructor|auto].
  - destruct (mixed_data_branch_step image s HP HS) as (i & s1 & HI & HC & HR & HInv & HROM & HRAM).
    destruct (IH s1 HInv) as (s' & HSteps & HFinal & HROM' & HRAM').
    exists s'. split; [econstructor; eauto|]. split; [exact HFinal|].
    split; congruence.
Qed.
End ISA.
Print Assumptions branch_decoded_operands_legal.
Print Assumptions data_branch_current_instruction.
Print Assumptions arbitrary_finite_data_branch_isa_progress.
End CV32E40PBranchProgramScope.
