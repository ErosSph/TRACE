(** A common REFERENCE-side run1 boundary for all 38 instruction classes.
    ExecutionReady is current ISA access/alignment evidence, NOT a future
    CPU result, cycle safety, reachability, or progress assumption.
    No RTL/ITree coverage is claimed by this module. The real CPU Joint
    must establish these conditions and its own post-state relations. *)
From Coq Require Import ZArith List.
Require Import Ex.External.CV32E40PReq41Instruction
  Ex.External.CV32E40PDataOpProgramScope Ex.External.CV32E40PDataOpExecution
  Ex.External.CV32E40PDataOpISAInvariant Ex.External.CV32E40PBranchExecution
  Ex.External.CV32E40PBranchProgramScope Ex.External.CV32E40PMemoryExecution
  Ex.External.CV32E40PJumpFenceExecution Ex.External.CV32E40PAddiNopISAInvariant.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte.
Import CV32E40PReq41Instruction CV32E40PDataOpProgramScope CV32E40PDataOpExecution
  CV32E40PDataOpISAInvariant CV32E40PBranchExecution CV32E40PBranchProgramScope
  CV32E40PMemoryExecution CV32E40PJumpFenceExecution CV32E40PAddiNopISAInvariant.
Local Open Scope Z_scope.
Module CV32E40PSupportedISAExecution.
Lemma dataop_family_exact i : InFamily FamilyDataOp i -> DataOp21 i.
Proof. destruct i; cbn [InFamily family_of DataOp21 dataop21b];
  intros HF; try discriminate; reflexivity. Qed.

Section ISA.
Context {word : Interface.word 32} {BW : Bitwidth 32}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.
Definition ExecutionReady (s : FormalSpec.State) i : Prop :=
  match family_of i with
  | Some FamilyDataOp => True
  | Some FamilyLoad => MemoryAligned s i /\ exists value, LoadOutcome s i value
  | Some FamilyStore => MemoryAligned s i /\ exists mem, StoreOutcome s i mem
  | Some FamilyBranch => TakenTargetAligned s i
  | Some FamilyJump => JumpTargetAligned s i
  | Some FamilyFenceI => True
  | None => False end.

Theorem supported_ready_run1_and_shape image (s : FormalSpec.State) i :
  Supported38 i -> CurrentInstruction s i -> ISAInvariant image s -> ExecutionReady s i ->
  exists s', FormalSpec.run1 s = (Some tt, s') /\ ISAInvariant image s' /\
    getInstMem s' = getInstMem s.
Proof.
  intros HS HC HI HR.
  unfold Supported38, supported38b in HS. unfold ExecutionReady in HR.
  destruct (family_of i) as [family|] eqn:HF; [|discriminate].
  assert (HFamily : InFamily family i) by exact HF.
  destruct family.
  - assert (HD : DataOp21 i) by (now apply dataop_family_exact).
    assert (HL : LegalOperands i).
    { destruct HC as [_ [bytes [_ HE]]]. eapply decoded_operands_legal; eauto. }
    destruct (run1_preserves_shape image s i HD HL HC HI) as (s' & HE & Hshape & Hrom & _).
    exists s'. auto.
  - destruct HR as [HA [value HO]]. exists (memory_post s i value (getDataMem s)).
    split; [now apply current_load_run1_exact|].
    split; [now apply memory_post_preserves_isa_shape|reflexivity].
  - destruct HR as [HA [mem HO]]. exists (memory_post s i (word.of_Z 0) mem).
    split; [now apply current_store_run1_exact|].
    split; [now apply memory_post_preserves_isa_shape|reflexivity].
  - assert (HL : LegalOperands i).
    { destruct HC as [_ [bytes [_ HE]]]. eapply branch_decoded_operands_legal; eauto. }
    destruct (branch_execution_preserves_architecture image s i HFamily HL HR HC HI)
      as (HE & Hshape & _ & Hrom & _).
    exists (branch_post s i). auto.
  - exists (jump_post s i). split; [now apply current_jump_run1_exact|].
    split; [now apply jump_preserves_isa_shape|reflexivity].
  - assert (HE : i = Decode.Fence_i).
    { destruct i; cbn [InFamily family_of] in HFamily; try discriminate; reflexivity. }
    subst i. exists (fence_i_post s). split; [now apply current_fence_i_run1_exact|].
    split; [now apply fence_i_preserves_isa_shape|reflexivity].
Qed.
End ISA.
Print Assumptions dataop_family_exact.
Print Assumptions supported_ready_run1_and_shape.
End CV32E40PSupportedISAExecution.
