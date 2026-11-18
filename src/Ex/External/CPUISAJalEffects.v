(** Pure original-ISA JAL link/frame/domain facts. No RTL or CPU INV. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CPUISAInstructionExecution
 Ex.External.CPUISAExecutionEffects Ex.External.CPUISARegisterUpdate Ex.External.CPURegisterEffectRelation
 Ex.External.CPUOriginalISAReference Ex.External.CV32E40PJumpFenceExecution
 Ex.External.CV32E40PReq41Instruction Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 riscv.Utility.Monads riscv.Spec.ExecuteI.
Import ListNotations CPUISAInstructionExecution CPUISAExecutionEffects CPUISARegisterUpdate
 CPURegisterEffectRelation CPUOriginalISAReference.
Local Open Scope Z_scope.
Module CPUISAJalEffects.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.

Definition link(before:FormalSpec.State):word:=word.add(getPc before)(word.of_Z 4).
Definition target(before:FormalSpec.State)imm:word:=word.add(getPc before)(word.of_Z imm).
Definition NextPCAligned(before:FormalSpec.State):Prop:=getNextPc before=link before.
Definition TargetDomain(before:FormalSpec.State)imm:Prop:=
 0<=word.unsigned(getPc before)+imm<2^32 /\(word.unsigned(getPc before)+imm)mod 4=0.

Theorem link_unsigned before:word.unsigned(link before)=(word.unsigned(getPc before)+4)mod 2^32.
Proof. unfold link;rewrite word.unsigned_add,word.unsigned_of_Z;unfold word.wrap;
 change(4 mod 2^32)with 4;reflexivity. Qed.
Theorem next_pc_aligned_unsigned before:
 NextPCAligned before <->word.unsigned(getNextPc before)=(word.unsigned(getPc before)+4)mod 2^32.
Proof. unfold NextPCAligned;rewrite <-link_unsigned;split;[now intros->|apply word.unsigned_inj]. Qed.
Theorem link_is_next before:NextPCAligned before ->link before=getNextPc before.
Proof. intro H;symmetry;exact H. Qed.
Theorem target_unsigned before imm:
 0<=word.unsigned(getPc before)+imm<2^32 ->word.unsigned(target before imm)=word.unsigned(getPc before)+imm.
Proof. intro HB;unfold target;rewrite word.unsigned_add,word.unsigned_of_Z;unfold word.wrap.
 rewrite Z.add_mod_idemp_r by discriminate;apply Z.mod_small;exact HB. Qed.
Theorem domain_target_aligned before rd imm:TargetDomain before imm ->
 CV32E40PJumpFenceExecution.JumpTargetAligned before(Decode.Jal rd imm).
Proof. intros[HB HA];unfold CV32E40PJumpFenceExecution.JumpTargetAligned,
 CV32E40PJumpFenceExecution.reference_jump_target;
 change(word.unsigned(target before imm)mod 4=0);rewrite(target_unsigned before imm HB);exact HA. Qed.
Theorem end_cycle_next_pc_aligned before after:
 Machine.endCycleNormal before=(Some tt,after) ->NextPCAligned after.
Proof. destruct before;intro H;inversion H;reflexivity. Qed.
Theorem run1_next_pc_aligned before after:
 FormalSpec.run1 before=(Some tt,after) ->NextPCAligned after.
Proof. unfold FormalSpec.run1;intro H.
 apply bind_success in H;destruct H as[pc[s1[HP H]]].
 apply bind_success in H;destruct H as[bytes[s2[HF H]]].
 apply bind_success in H;destruct H as[value[middle[HE HEnd]]].
 exact(end_cycle_next_pc_aligned middle after HEnd). Qed.

Context {Token:Type}.
Variables token_pc token_word:Token->Z.
Theorem instruction_effect_next_pc_aligned token before after:
 instruction_effect token_pc token_word token before=Some after ->NextPCAligned after.
Proof. intro HS;exact(run1_next_pc_aligned before after(proj2(proj2(instruction_effect_sound _ _ _ _ _ HS)))). Qed.
Theorem link_at_token token before after:
 instruction_effect token_pc token_word token before=Some after ->
 word.unsigned(link before)=(token_pc token+4)mod 2^32.
Proof. intro HS;destruct(instruction_effect_sound token_pc token_word token before after HS)as[HP _].
 rewrite link_unsigned,HP;reflexivity. Qed.
Theorem next_link_at_token token before after:
 instruction_effect token_pc token_word token before=Some after ->NextPCAligned before ->
 word.unsigned(getNextPc before)=(token_pc token+4)mod 2^32.
Proof. intros HS HA;rewrite HA;exact(link_at_token token before after HS). Qed.

Theorem original_jal_post token before after rd imm:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jal rd imm) ->
 CV32E40PJumpFenceExecution.JumpTargetAligned before(Decode.Jal rd imm) ->
 after=CV32E40PJumpFenceExecution.jump_post before(Decode.Jal rd imm).
Proof. intros HS HD HA.
 destruct(token_execute token_pc token_word token before after(Decode.Jal rd imm)HS HD)as[middle[HE HEnd]].
 pose proof(CV32E40PJumpFenceExecution.jump_decoded_operands_legal(token_word token)(Decode.Jal rd imm)eq_refl HD)as HLegal.
 pose proof(CV32E40PJumpFenceExecution.execute_jump_exact before(Decode.Jal rd imm)eq_refl HLegal HA)as HExact.
 unfold CV32E40PReq41Instruction.ISAStep in HExact.
 change(Bind(ExecuteI.execute(Decode.Jal rd imm))(fun _=>Machine.endCycleNormal)before=
 (Some tt,CV32E40PJumpFenceExecution.jump_post before(Decode.Jal rd imm)))in HExact.
 cbn[Bind OState_Monad]in HExact;rewrite HE in HExact.
 change(Machine.endCycleNormal middle=(Some tt,CV32E40PJumpFenceExecution.jump_post before(Decode.Jal rd imm)))in HExact.
 rewrite HEnd in HExact;injection HExact;auto.
Qed.

Theorem original_jal_register_effect token before after rd imm:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jal rd imm) ->
 CV32E40PJumpFenceExecution.JumpTargetAligned before(Decode.Jal rd imm) ->
 ISAProjectedRegisterEffects before after(register_operations rd(link before)).
Proof. intros HS HD HA;rewrite(original_jal_post token before after rd imm HS HD HA).
 apply updated_registers;unfold CV32E40PJumpFenceExecution.jump_post;reflexivity. Qed.

Theorem original_jal_frame token before after rd imm:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jal rd imm) ->
 CV32E40PJumpFenceExecution.JumpTargetAligned before(Decode.Jal rd imm) ->
 FormalSpec.run1 before=(Some tt,after) /\getPc after=target before imm /\
 getNextPc after=word.add(target before imm)(word.of_Z 4) /\
 getInstMem after=getInstMem before /\getDataMem after=getDataMem before.
Proof. intros HS HD HA;pose proof(proj2(proj2(instruction_effect_sound token_pc token_word token before after HS)))as HR.
 split;[exact HR|];rewrite(original_jal_post token before after rd imm HS HD HA);repeat split;reflexivity. Qed.

Theorem original_jal_domain token before after rd imm:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jal rd imm) ->
 NextPCAligned before ->TargetDomain before imm ->
 word.unsigned(getPc after)=word.unsigned(getPc before)+imm /\
 word.unsigned(getNextPc after)=(word.unsigned(getPc before)+imm+4)mod 2^32 /\
 NextPCAligned after /\ISAProjectedRegisterEffects before after(register_operations rd(getNextPc before)).
Proof. intros HS HD HNext HTarget;pose proof(domain_target_aligned before rd imm HTarget)as HA.
 destruct(original_jal_frame token before after rd imm HS HD HA)as[HR[HP[HN[HI HM]]]].
 split;[rewrite HP;exact(target_unsigned before imm(proj1 HTarget))|];split.
 - rewrite HN,word.unsigned_add,word.unsigned_of_Z;unfold word.wrap;change(4 mod 2^32)with 4.
   rewrite(target_unsigned before imm(proj1 HTarget));reflexivity.
 - split;[exact(run1_next_pc_aligned before after HR)|].
   rewrite HNext;exact(original_jal_register_effect token before after rd imm HS HD HA).
Qed.
End ISA.

Section Total.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.
Theorem current_jal_run1_total before rd imm:
 CV32E40PReq41Instruction.CurrentInstruction before(Decode.Jal rd imm) ->TargetDomain before imm ->
 FormalSpec.run1 before=(Some tt,CV32E40PJumpFenceExecution.jump_post before(Decode.Jal rd imm)).
Proof. intros HC HT;apply CV32E40PJumpFenceExecution.current_jump_run1_exact;
 [reflexivity|exact HC|exact(domain_target_aligned before rd imm HT)]. Qed.
Theorem token_jal_total {Token:Type}(token_pc token_word:Token->Z)token before rd imm bytes:
 token_pc token=word.unsigned(getPc before) ->fetched_word before=Some bytes ->
 token_word token=LittleEndian.combine 4 bytes ->
 CV32E40PReq41Instruction.CurrentInstruction before(Decode.Jal rd imm) ->TargetDomain before imm ->
 instruction_effect token_pc token_word token before=
 Some(CV32E40PJumpFenceExecution.jump_post before(Decode.Jal rd imm)).
Proof. intros HP HF HW HC HT;eapply instruction_effect_complete;[exact HP|exact HF|exact HW|].
 exact(current_jal_run1_total before rd imm HC HT). Qed.
End Total.
End CPUISAJalEffects.
