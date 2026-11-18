(** Post-state shape of the successful ISA step inside the checked jump-family ROM domain (generic, no RTL).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CPUJumpFamilyProgramDomain Ex.External.CPUProgramROM Ex.External.CPUOriginalADDFrontier
 Ex.External.CPUISAJalEffects Ex.External.CPUISAJalSuccessfulState
 Ex.External.CPUISAExecutionEffects Ex.External.CPUOriginalISAReference
 Ex.External.CV32E40PDataOpExecution Ex.External.CV32E40PDataOpISAInvariant
 Ex.External.CV32E40PDataOpProgramScope Ex.External.CV32E40PReq41Instruction
 Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PJumpFenceExecution
 Ex.External.CPUDataControlProgramDomain Ex.External.CPUISABranchFamilyEffects
 Ex.External.CPUBranchFamilyProgramDomain Ex.External.CV32E40PBranchExecution Ex.External.CPUISABranchFamilyFields
 Ex.RvCore.FormalSpec Ex.RvCore.Machine coqutil.Word.Interface
 coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 riscv.Utility.Utility riscv.Spec.Decode riscv.Spec.ExecuteI riscv.Utility.Monads riscv.Proofs.VerifyDecode.
Import CPUJumpFamilyProgramDomain ListNotations CPUISAExecutionEffects CPUOriginalISAReference
 CV32E40PDataOpExecution CV32E40PDataOpProgramScope CV32E40PReq41Instruction.
Local Open Scope Z_scope.
Module CPUJumpFamilyPostShape.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.

(** The successful ISA step from a checked program point is exactly the post state of the instruction's family
    ([dataop_post], [jump_post], [branch_post]).  Design independent; no RTL state. *)
Theorem checked_post_shape words index(before after:FormalSpec.State):
 check_program words=true ->AtProgram words index before ->
 FormalSpec.run1 before=(Some tt,after) ->
 exists i,Decode.decode Decode.RV32I(nth index words 0)=Decode.IInstruction i /\
  ((DataOp21 i /\after=dataop_post before i)
   \/(exists rd imm,i=Decode.Jal rd imm /\after=CV32E40PJumpFenceExecution.jump_post before i)
   \/(exists rd imm,i=Decode.Jalr rd 0 imm /\after=CV32E40PJumpFenceExecution.jump_post before i)
   \/(exists op rs1 rs2 imm,i=CPUISABranchFamilyEffects.instruction op rs1 rs2 imm /\after=CV32E40PBranchExecution.branch_post before i)).
Proof. intros HC HAt HRun.
 destruct(checked_current_instruction words index before HC HAt)as[i[HD[HCurrent[HL HT]]]].
 exists i;split;[exact HD|].
 destruct(legal_instruction_sound i HL)as[HData|[[rd[imm HEq]]|[[op[rs1[rs2[imm HEq]]]]|[rd[imm HEq]]]]].
 - left;split;[exact HData|].
   pose proof(run1_exact before i HData
     (CV32E40PDataOpISAInvariant.decoded_operands_legal(nth index words 0)i HData HD)HCurrent)as HExact.
   rewrite HRun in HExact;injection HExact as HAfter;exact HAfter.
 - right;left;exists rd,imm;split;[exact HEq|]. subst i.
   pose proof(CV32E40PJumpFenceExecution.current_jump_run1_exact before(Decode.Jal rd imm)eq_refl HCurrent)as HJ.
   assert(HTD:CPUISAJalEffects.TargetDomain before imm).
   { pose proof(checked_length words HC);cbn[successors CPUBranchFamilyProgramDomain.successors]in HT;destruct(Forall_inv HT)as[HB HA].
     unfold CPUISAJalEffects.TargetDomain;rewrite(proj1(proj2 HAt)).
     cbn[CPUDataControlProgramDomain.next_address]in HB,HA;split;[lia|exact HA]. }
   pose proof(CPUISAJalEffects.current_jal_run1_total before rd imm HCurrent HTD)as HExact.
   rewrite HRun in HExact;injection HExact as HAfter;exact HAfter.
 - right;right;right;exists op,rs1,rs2,imm;split;[exact HEq|]. subst i.
   pose proof(CV32E40PBranchExecution.run1_branch_exact before(CPUISABranchFamilyEffects.instruction op rs1 rs2 imm)
      (CPUBranchFamilyProgramDomain.branch_in_family op rs1 rs2 imm)
      (CPUBranchFamilyProgramDomain.branch_operands_legal(nth index words 0)op rs1 rs2 imm HD)
      (branch_taken_target_aligned words index before op rs1 rs2 imm HC HAt(ltac:(destruct op;exact HT)))
      HCurrent)as HExact.
   rewrite HRun in HExact;injection HExact as HAfter;exact HAfter.
 - right;right;left;exists rd,imm;split;[exact HEq|]. subst i.
   assert(HAligned:CV32E40PJumpFenceExecution.JumpTargetAligned before(Decode.Jalr rd 0 imm)).
   { unfold CV32E40PJumpFenceExecution.JumpTargetAligned;rewrite jalr_x0_target_unsigned.
     cbn[successors]in HT;exact(proj2(Forall_inv HT)). }
   pose proof(CV32E40PJumpFenceExecution.current_jump_run1_exact before(Decode.Jalr rd 0 imm)eq_refl HCurrent HAligned)as HExact.
   rewrite HRun in HExact;injection HExact as HAfter;exact HAfter.
Qed.

(** The normalised (32-bit) ROM word at the program point decodes to the current instruction. *)
Theorem checked_decode_normalized words index(before:FormalSpec.State) i:
 check_program words=true ->AtProgram words index before ->CurrentInstruction before i ->
 Decode.decode Decode.RV32I((nth index words 0)mod 2^32)=Decode.IInstruction i.
Proof. intros HC HAt HCur. pose proof(checked_length words HC)as HLen.
 destruct HAt as[HIdx[HP[HM HN]]].
 destruct(CPUProgramROM.dense_image_little_endian_load words(getPc before)index ltac:(lia) HP)as[tup[HL HV]].
 destruct HCur as[_[bytes[HB HD]]].
 rewrite HM in HB. rewrite HL in HB. injection HB as E. rewrite <- E in HD. rewrite <- HV. exact HD. Qed.
End ISA.
End CPUJumpFamilyPostShape.
Print Assumptions CPUJumpFamilyPostShape.checked_post_shape.
Print Assumptions CPUJumpFamilyPostShape.checked_decode_normalized.
