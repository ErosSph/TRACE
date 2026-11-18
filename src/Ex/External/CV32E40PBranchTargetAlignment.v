(** Four-byte-aligned RV32I branch scope derives the actual reference target
    alignment, including negative offsets and 32-bit wraparound. No C ISA,
    architectural exception suppression, or assumed RTL redirect target. *)
From Coq Require Import ZArith Lia.
Require Import Ex.External.CV32E40PBranchExecution Ex.External.CV32E40PReq41Instruction
  Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PDataOpExecution
  Ex.External.CV32E40PAddiNopISAInvariant.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
  coqutil.Map.Interface coqutil.Byte.
Import CV32E40PBranchExecution CV32E40PReq41Instruction CV32E40PReq40StateRel
  CV32E40PDataOpExecution CV32E40PAddiNopISAInvariant.
Local Open Scope Z_scope.
Module CV32E40PBranchTargetAlignment.
Lemma aligned_wrapped_sum p imm : p mod 4 = 0 -> imm mod 4 = 0 ->
  ((p+imm) mod 2^32) mod 4 = 0.
Proof.
  intros HP HI. apply Z.mod_divide; [lia|].
  exists (p/4 + imm/4 - 1073741824*((p+imm)/4294967296)).
  change (2^32) with 4294967296. rewrite Z.mod_eq by lia.
  pose proof (Z.div_mod p 4 ltac:(lia)).
  pose proof (Z.div_mod imm 4 ltac:(lia)). nia.
Qed.
Section ISA.
Context {word : Interface.word 32} {BW : Bitwidth 32}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.
Theorem four_byte_scope_derives_target_alignment (s : FormalSpec.State) i :
  word.unsigned (getPc s) mod 4 = 0 -> branch_immediate i mod 4 = 0 ->
  word.unsigned (reference_branch_target s i) mod 4 = 0.
Proof.
  intros HP HI. unfold reference_branch_target.
  rewrite word.unsigned_add, word.unsigned_of_Z. unfold word.wrap.
  rewrite Z.add_mod_idemp_r by lia. now apply aligned_wrapped_sum.
Qed.
Theorem four_byte_scope_derives_taken_target (s : FormalSpec.State) i :
  CurrentInstruction s i -> branch_immediate i mod 4 = 0 -> TakenTargetAligned s i.
Proof.
  intros HC HI HG. apply four_byte_scope_derives_target_alignment; [exact (current_pc_aligned s i HC)|exact HI].
Qed.
Theorem four_byte_branch_run1_and_frame image s i :
  InFamily FamilyBranch i -> LegalOperands i -> CurrentInstruction s i ->
  branch_immediate i mod 4 = 0 -> ISAInvariant image s ->
  FormalSpec.run1 s = (Some tt, branch_post s i) /\
  ISAInvariant image (branch_post s i) /\
  getRegs (branch_post s i) = getRegs s /\
  getInstMem (branch_post s i) = getInstMem s /\
  getDataMem (branch_post s i) = getDataMem s.
Proof.
  intros HI HL HC HOffset HInv. apply branch_execution_preserves_architecture;
    try assumption. now apply four_byte_scope_derives_taken_target.
Qed.
End ISA.
Print Assumptions aligned_wrapped_sum.
Print Assumptions four_byte_scope_derives_target_alignment.
Print Assumptions four_byte_branch_run1_and_frame.
End CV32E40PBranchTargetAlignment.
