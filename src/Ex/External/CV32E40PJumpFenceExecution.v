(** Symbolic ISA execution for JAL, JALR and FENCE.I. This is NOT an
    RTL flush/reissue/infinite refinement proof. Targets must be aligned
    to four bytes under the declared 32-bit-only instruction scope. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CV32E40PReq41Instruction
  Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PDataOpExecution
  Ex.External.CV32E40PBranchExecution Ex.External.CV32E40PAddiNopISAInvariant.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine.
Require Import riscv.Spec.Execute riscv.Spec.ExecuteI riscv.Utility.Monads
  riscv.Proofs.VerifyDecode.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
  coqutil.Map.Interface coqutil.Byte.
Import ListNotations CV32E40PReq41Instruction CV32E40PReq40StateRel
  CV32E40PDataOpExecution CV32E40PBranchExecution CV32E40PAddiNopISAInvariant.
Local Open Scope Z_scope.
Module CV32E40PJumpFenceExecution.

Lemma jump_decoded_operands_legal code i : InFamily FamilyJump i ->
  Decode.decode Decode.RV32I code = Decode.IInstruction i -> LegalOperands i.
Proof.
  intros HF HD.
  destruct (verify_decode Decode.RV32I code eq_refl) as [HV|HB];
    [rewrite HD in HV|congruence].
  destruct i; cbn [InFamily family_of] in HF; try discriminate.
  all: cbv [verify respects_bounds apply_InstructionMapper Verifier
    map_UJ map_I verify_UJ verify_I bitwidth verify_iset] in HV.
  all: unfold LegalOperands; cbn [destination_register source_registers];
    repeat constructor; unfold legal_reg; intuition lia.
Qed.
Section ISA.
Context {word : Interface.word 32} {BW : Bitwidth 32}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.

Definition reference_jump_target (s : FormalSpec.State) i : word :=
  match i with
  | Decode.Jal _ imm => word.add (getPc s) (word.of_Z imm)
  | Decode.Jalr _ rs imm => Utility.and
      (word.add (formal_register_word s rs) (word.of_Z imm))
      (Utility.lnot (Utility.ZToReg 1))
  | _ => getNextPc s end.
Definition JumpTargetAligned (s : FormalSpec.State) i :=
  word.unsigned (reference_jump_target s i) mod 4 = 0.
Definition jump_post (s : FormalSpec.State) i : FormalSpec.State :=
  {| getRegs := match destination_register i with
       | Some rd => if Z.eq_dec rd 0 then getRegs s else
           map.put (getRegs s) rd (word.add (getPc s) (word.of_Z 4))
       | None => getRegs s end;
     getPc := reference_jump_target s i;
     getNextPc := word.add (reference_jump_target s i) (word.of_Z 4);
     getInstMem := getInstMem s; getDataMem := getDataMem s |}.
Definition fence_i_post (s : FormalSpec.State) : FormalSpec.State :=
  {| getRegs := getRegs s; getPc := getNextPc s;
     getNextPc := word.add (getNextPc s) (word.of_Z 4);
     getInstMem := getInstMem s; getDataMem := getDataMem s |}.

Theorem execute_jump_exact (s : FormalSpec.State) i :
  InFamily FamilyJump i -> LegalOperands i -> JumpTargetAligned s i ->
  ISAStep s i (jump_post s i).
Proof.
  intros HF HL HA. destruct s as [regs pc npc imem dmem].
  destruct i; cbn [InFamily family_of] in HF; try discriminate.
  all: unfold LegalOperands in HL; cbn [destination_register source_registers] in HL;
    destruct HL as [HR HS];
    repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end.
  all: unfold ISAStep; cbn [Execute.execute ExecuteI.execute];
    unfold Machine.getRegister, Machine.getPC, Machine.setRegister,
      Machine.setPC, Machine.endCycleNormal;
    cbn [IsRiscvProgram]; unfold jump_post, JumpTargetAligned,
      reference_jump_target, formal_register_word in *;
    cbn [destination_register getRegs getPc getNextPc getInstMem getDataMem] in *.
  all: repeat match goal with
    | |- context [Z.eq_dec ?r ?z] => destruct (Z.eq_dec r z) end; try contradiction.
  all: repeat match goal with
    | |- context [((0 <? ?r) && (?r <? 32))%bool] =>
      let HB := fresh "Hlegal" in
      assert (HB : ((0 <? r) && (r <? 32))%bool = true)
        by (apply andb_true_iff; split; apply Z.ltb_lt;
          unfold legal_reg in *; cbn in *; lia);
      rewrite HB end.
  all: cbn [Bind Return OState_Monad OStateOperations.get OStateOperations.put
    update withRegs withPc withNextPc getRegs getPc getNextPc getInstMem getDataMem] in *.
  all: repeat match goal with |- context [map.get ?m ?r] =>
    let E := fresh "Eget" in destruct (map.get m r) eqn:E;
    cbn [Bind Return OState_Monad OStateOperations.get OStateOperations.put
      update withRegs withPc withNextPc getRegs getPc getNextPc getInstMem getDataMem] in *;
    repeat match goal with H : map.get _ _ = _ |- _ => progress rewrite H in * end end.
  all: unfold Utility.fromImm, Utility.add in *.
  all: cbv beta iota zeta delta [MkMachineWidth.MachineWidth_XLEN] in *.
  all: try reflexivity.
  all: pose proof (aligned_guard_false (BW:=BW) _ HA) as Hguard.
  all: cbv beta iota zeta delta [Utility.ZToReg Utility.reg_eqb Utility.remu
    Utility.and Utility.lnot Utility.xor Utility.maxUnsigned
    MkMachineWidth.MachineWidth_XLEN] in *.
  all: rewrite Hguard.
  all: cbn [Bind Return OState_Monad OStateOperations.get OStateOperations.put
    update withRegs withPc withNextPc getRegs getPc getNextPc getInstMem getDataMem];
    unfold OStateOperations.put; reflexivity.
Qed.

Theorem current_jump_run1_exact s i : InFamily FamilyJump i ->
  CurrentInstruction s i -> JumpTargetAligned s i ->
  FormalSpec.run1 s = (Some tt, jump_post s i).
Proof.
  intros HF HC HA. eapply current_instruction_run1_step; [exact HC|].
  apply execute_jump_exact; auto.
  destruct HC as [_ [bytes [_ HD]]].
  eapply jump_decoded_operands_legal; eauto.
Qed.
Theorem execute_fence_i_exact (s : FormalSpec.State) :
  ISAStep s Decode.Fence_i (fence_i_post s).
Proof. destruct s; reflexivity. Qed.
Theorem current_fence_i_run1_exact s : CurrentInstruction s Decode.Fence_i ->
  FormalSpec.run1 s = (Some tt, fence_i_post s).
Proof. intros HC. eapply current_instruction_run1_step;
  [exact HC|apply execute_fence_i_exact]. Qed.

Theorem jump_preserves_isa_shape image (s : FormalSpec.State) i :
  ISAInvariant image s -> JumpTargetAligned s i -> ISAInvariant image (jump_post s i).
Proof.
  intros (HROM & _ & _) HA. unfold ISAInvariant, jump_post.
  cbn [getInstMem getPc getNextPc]. split; [exact HROM|]. split; [exact HA|].
  rewrite word.unsigned_add, word.unsigned_of_Z.
  change (4 mod 2^32) with 4. reflexivity.
Qed.
Theorem fence_i_preserves_isa_shape image (s : FormalSpec.State) :
  ISAInvariant image s -> ISAInvariant image (fence_i_post s).
Proof.
  intros (HROM & HA & HN). unfold ISAInvariant, fence_i_post.
  cbn [getInstMem getPc getNextPc]. split; [exact HROM|]. split.
  - rewrite HN. now apply aligned_successor.
  - rewrite word.unsigned_add, word.unsigned_of_Z.
    change (4 mod 2^32) with 4. reflexivity.
Qed.
End ISA.
Print Assumptions jump_decoded_operands_legal.
Print Assumptions execute_jump_exact.
Print Assumptions current_jump_run1_exact.
Print Assumptions current_fence_i_run1_exact.
Print Assumptions jump_preserves_isa_shape.
Print Assumptions fence_i_preserves_isa_shape.
End CV32E40PJumpFenceExecution.
