(** Symbolic ISA branch execution for all six guards and arbitrary legal
    operands. Taken targets must be four-byte aligned: this is the declared
    RV32I-only/no-compressed scope, not a replacement for hardware freshness.
    CPU acceptance, flush and progress are separate global obligations. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CV32E40PReq41Instruction
  Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PDataOpExecution
  Ex.External.CV32E40PBranchISACondition Ex.External.CV32E40PAddiNopISAInvariant.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine.
Require Import riscv.Spec.Execute riscv.Spec.ExecuteI riscv.Utility.Monads.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
  coqutil.Map.Interface coqutil.Byte.
Import ListNotations CV32E40PReq41Instruction CV32E40PReq40StateRel
  CV32E40PDataOpExecution CV32E40PBranchISACondition CV32E40PAddiNopISAInvariant.
Local Open Scope Z_scope.
Module CV32E40PBranchExecution.
Definition branch_rs1 i := match i with
  | Decode.Beq a _ _ | Decode.Bne a _ _ | Decode.Blt a _ _
  | Decode.Bge a _ _ | Decode.Bltu a _ _ | Decode.Bgeu a _ _ => a
  | _ => 0 end.
Definition branch_rs2 i := match i with
  | Decode.Beq _ b _ | Decode.Bne _ b _ | Decode.Blt _ b _
  | Decode.Bge _ b _ | Decode.Bltu _ b _ | Decode.Bgeu _ b _ => b
  | _ => 0 end.
Definition branch_immediate i := match immediate_field i with
  | Some imm => imm | None => 0 end.

Section ISA.
Context {word : Interface.word 32} {BW : Bitwidth 32}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.
Definition reference_branch_taken (s : FormalSpec.State) i :=
  isa_branch_guard i (formal_register_word s (branch_rs1 i))
    (formal_register_word s (branch_rs2 i)).
Definition reference_branch_target (s : FormalSpec.State) i : word :=
  word.add (getPc s) (word.of_Z (branch_immediate i)).
Definition branch_next_pc (s : FormalSpec.State) i : word :=
  if reference_branch_taken s i then reference_branch_target s i else getNextPc s.
Definition TakenTargetAligned (s : FormalSpec.State) i : Prop :=
  reference_branch_taken s i = true ->
  word.unsigned (reference_branch_target s i) mod 4 = 0.
Definition branch_post (s : FormalSpec.State) i : FormalSpec.State :=
  {| getRegs := getRegs s;
     getPc := branch_next_pc s i;
     getNextPc := word.add (branch_next_pc s i) (word.of_Z 4);
     getInstMem := getInstMem s; getDataMem := getDataMem s |}.

Lemma aligned_guard_false (addr : word) : word.unsigned addr mod 4 = 0 ->
  negb (Utility.reg_eqb (Utility.remu addr (Utility.ZToReg 4)) (Utility.ZToReg 0)) = false.
Proof.
  intros HA. change (negb (word.eqb (word.modu addr (word.of_Z 4)) (word.of_Z 0)) = false).
  rewrite word.unsigned_eqb, word.unsigned_modu.
  2: { rewrite word.unsigned_of_Z. unfold word.wrap.
       rewrite Z.mod_small by lia. lia. }
  rewrite !word.unsigned_of_Z. unfold word.wrap.
  change (4 mod 2^32) with 4. change (0 mod 2^32) with 0.
  rewrite HA. reflexivity.
Qed.

Theorem execute_branch_exact (s : FormalSpec.State) i :
  InFamily FamilyBranch i -> LegalOperands i -> TakenTargetAligned s i ->
  ISAStep s i (branch_post s i).
Proof.
  intros HI HL HT. destruct s as [regs pc npc imem dmem].
  destruct i; cbn [InFamily family_of] in HI; try discriminate.
  all: unfold LegalOperands in HL; cbn [destination_register source_registers] in HL;
    destruct HL as [_ HS];
    repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end.
  all: unfold ISAStep; cbn [Execute.execute ExecuteI.execute];
    unfold Machine.getRegister, Machine.getPC, Machine.setPC, Machine.endCycleNormal;
    cbn [IsRiscvProgram]; unfold branch_post, branch_next_pc, reference_branch_target,
      TakenTargetAligned, reference_branch_taken, formal_register_word in *;
    cbn [branch_rs1 branch_rs2 branch_immediate immediate_field isa_branch_guard
      getRegs getPc getNextPc getInstMem getDataMem] in *.
  all: repeat match goal with |- context [Z.eq_dec ?r ?z] => destruct (Z.eq_dec r z) end;
    try contradiction.
  all: repeat match goal with
    | |- context [((0 <? ?r) && (?r <? 32))%bool] =>
      let HB := fresh "Hlegal" in
      assert (HB : ((0 <? r) && (r <? 32))%bool = true)
        by (apply andb_true_iff; split; apply Z.ltb_lt; unfold legal_reg in *; cbn in *; lia);
      rewrite HB
    end.
  all: cbn [Bind Return OState_Monad OStateOperations.get OStateOperations.put
    update withRegs withPc withNextPc getRegs getPc getNextPc getInstMem getDataMem] in *.
  all: repeat match goal with |- context [map.get ?rsmap ?r] =>
    let E := fresh "Eget" in destruct (map.get rsmap r) eqn:E;
    cbn [Bind Return OState_Monad OStateOperations.get OStateOperations.put
      update withRegs withPc withNextPc getRegs getPc getNextPc getInstMem getDataMem] in *;
    repeat match goal with H : map.get _ _ = _ |- _ => progress rewrite H in * end
    end.
  all: unfold Utility.fromImm, Utility.add in *.
  all: cbv beta iota zeta delta [MkMachineWidth.MachineWidth_XLEN] in *.
  all: unfold reference_branch_target in HT;
    cbn [branch_immediate immediate_field getPc] in HT.
  all: repeat match goal with
    | |- context [when ?guard _] => let E := fresh "Hguard" in destruct guard eqn:E;
      unfold when; cbn [Bind Return OState_Monad OStateOperations.get OStateOperations.put
        update withRegs withPc withNextPc getRegs getPc getNextPc getInstMem getDataMem] in *
    end.
  all: try reflexivity.
  all: rewrite aligned_guard_false by (apply HT; reflexivity).
  all: cbn [Bind Return OState_Monad OStateOperations.get OStateOperations.put
    update withPc withNextPc getPc getNextPc]; unfold OStateOperations.put; reflexivity.
Qed.

Theorem run1_branch_exact s i : InFamily FamilyBranch i -> LegalOperands i ->
  TakenTargetAligned s i -> CurrentInstruction s i ->
  FormalSpec.run1 s = (Some tt, branch_post s i).
Proof.
  intros HI HL HT HC. eapply current_instruction_run1_step;
    eauto using execute_branch_exact.
Qed.

Theorem branch_execution_preserves_architecture image s i :
  InFamily FamilyBranch i -> LegalOperands i -> TakenTargetAligned s i ->
  CurrentInstruction s i -> ISAInvariant image s ->
  FormalSpec.run1 s = (Some tt, branch_post s i) /\
  ISAInvariant image (branch_post s i) /\
  getRegs (branch_post s i) = getRegs s /\
  getInstMem (branch_post s i) = getInstMem s /\
  getDataMem (branch_post s i) = getDataMem s.
Proof.
  intros HI HL HT HC (HM & HA & HN).
  split; [now apply run1_branch_exact|].
  split; [|repeat split; reflexivity].
  unfold ISAInvariant, branch_post. cbn [getInstMem getPc getNextPc].
  split; [exact HM|]. split.
  - unfold branch_next_pc. destruct (reference_branch_taken s i) eqn:HG.
    + now apply HT.
    + rewrite HN. now apply aligned_successor.
  - rewrite word.unsigned_add, word.unsigned_of_Z.
    change (4 mod 2^32) with 4. reflexivity.
Qed.
End ISA.
Print Assumptions execute_branch_exact.
Print Assumptions run1_branch_exact.
Print Assumptions branch_execution_preserves_architecture.
End CV32E40PBranchExecution.
