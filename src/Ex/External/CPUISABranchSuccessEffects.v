(** Extract BEQ effects from successful ORIGINAL execution.
    Success already selects the non-exception branch, so no target-alignment
    premise is needed. No RTL state or hardware invariant is imported. *)
From Coq Require Import ZArith List.
Require Import Ex.External.CPUISAInstructionExecution Ex.External.CPUISAExecutionEffects
 Ex.External.CPURegisterEffectRelation Ex.External.CPUOriginalISAReference
 Ex.External.CPUOriginalADDFrontier Ex.External.CPUISAJalEffects Ex.External.PicoISARF
 Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface
 coqutil.Byte riscv.Utility.Monads riscv.Utility.Utility riscv.Spec.ExecuteI.
Import CPUISAInstructionExecution CPUISAExecutionEffects CPURegisterEffectRelation
 CPUOriginalISAReference CPUOriginalADDFrontier.
Local Open Scope Z_scope.

Module CPUISABranchSuccessEffects.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.

(** The value returned by a successful original register read is the
    architectural view used by every register relation. *)
Theorem original_read_value (before after:FormalSpec.State) rs value:
 Machine.getRegister rs before=(Some value,after) ->
 word.unsigned value=ISAView before rs.
Proof.
 unfold ISAView,PicoISARF.isa_value,Machine.getRegister;cbn[IsRiscvProgram].
 destruct(Z.eq_dec rs 0)as[->|HZ].
 - intro H;inversion H;subst;cbn;rewrite word.unsigned_of_Z_0;reflexivity.
 - destruct((0<?rs)&&(rs<?32))%bool;[|discriminate].
   cbn[Bind Return OState_Monad OStateOperations.get].
   apply Z.eqb_neq in HZ;rewrite HZ.
   destruct(map.get(getRegs before)rs);intro H;inversion H;subst;
   [reflexivity|apply word.unsigned_of_Z_0].
Qed.

Theorem set_pc_fields (before after:FormalSpec.State) target:
 Machine.setPC target before=(Some tt,after) ->
 getRegs after=getRegs before /\getPc after=getPc before /\getNextPc after=target /\
 getInstMem after=getInstMem before /\getDataMem after=getDataMem before.
Proof. destruct before;intro H;inversion H;repeat split;reflexivity. Qed.

Theorem successful_beq_fields (before after:FormalSpec.State) rs1 rs2 imm:
 ExecuteI.execute(Decode.Beq rs1 rs2 imm)before=(Some tt,after) ->
 getRegs after=getRegs before /\getPc after=getPc before /\
 getNextPc after=(if ISAView before rs1=?ISAView before rs2
  then word.add(getPc before)(word.of_Z imm) else getNextPc before) /\
 getInstMem after=getInstMem before /\getDataMem after=getDataMem before.
Proof.
 intro H;cbn[ExecuteI.execute]in H.
 apply bind_success in H;destruct H as[x[s1[HX H]]].
 pose proof(original_read_value before s1 rs1 x HX)as VX.
 pose proof(original_read_preserves before s1 rs1 x HX);subst s1.
 apply bind_success in H;destruct H as[y[s2[HY H]]].
 pose proof(original_read_value before s2 rs2 y HY)as VY.
 pose proof(original_read_preserves before s2 rs2 y HY);subst s2.
 apply bind_success in H;destruct H as[pc[s3[HP H]]].
 pose proof(original_pc_read_preserves before s3 pc HP);subst s3.
 assert(HPC:pc=getPc before)by(inversion HP;reflexivity);subst pc.
 rewrite <-VX,<-VY.
 change(reg_eqb x y)with(word.eqb x y)in H.
 rewrite word.unsigned_eqb in H.
 unfold when in H;destruct(word.unsigned x=?word.unsigned y).
 - cbv beta zeta in H.
   match type of H with context[if ?guard then _ else _]=>destruct guard end.
   + discriminate H.
   + exact(set_pc_fields before after _ H).
 - cbn[Return OState_Monad]in H;inversion H;subst;repeat split;reflexivity.
Qed.

Context {Token:Type}.
Variables token_pc token_word:Token->Z.

(** Token-level effect after the original end of cycle. At an instruction
    boundary nextPC is PC+4 (proved for every successful run1 by
    [CPUISAJalEffects.instruction_effect_next_pc_aligned]). *)
Theorem successful_token_beq_fields token before after rs1 rs2 imm:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Beq rs1 rs2 imm) ->
 CPUISAJalEffects.NextPCAligned before ->
 getRegs after=getRegs before /\
 getPc after=(if ISAView before rs1=?ISAView before rs2
  then CPUISAJalEffects.target before imm else CPUISAJalEffects.link before) /\
 getNextPc after=word.add(getPc after)(word.of_Z 4) /\
 getInstMem after=getInstMem before /\getDataMem after=getDataMem before.
Proof.
 intros HS HD HA.
 destruct(token_execute token_pc token_word token before after _ HS HD)as[middle[HE HEnd]].
 destruct(successful_beq_fields before middle rs1 rs2 imm HE)as[HR[HP[HN[HI HM]]]].
 destruct(original_end_cycle_frontier middle after HEnd)as[HP'[HN'[HI' HM']]].
 assert(HRegs:getRegs after=getRegs middle)by(destruct middle;inversion HEnd;reflexivity).
 split;[exact(eq_trans HRegs HR)|].
 split;[rewrite HP',HN;unfold CPUISAJalEffects.target,CPUISAJalEffects.link;
  destruct(_=?_);[reflexivity|exact HA]|].
 split;[rewrite HN',HP';reflexivity|].
 exact(conj(eq_trans HI' HI)(eq_trans HM' HM)).
Qed.

(** BEQ never writes a register: the architectural view is unchanged. *)
Theorem successful_token_beq_register_frame token before after rs1 rs2 imm:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Beq rs1 rs2 imm) ->
 forall i,ISAView after i=ISAView before i.
Proof.
 intros HS HD i.
 destruct(token_execute token_pc token_word token before after _ HS HD)as[middle[HE HEnd]].
 destruct(successful_beq_fields before middle rs1 rs2 imm HE)as[HR _].
 assert(HRegs:getRegs after=getRegs middle)by(destruct middle;inversion HEnd;reflexivity).
 unfold ISAView;rewrite HRegs,HR;reflexivity.
Qed.
End ISA.
End CPUISABranchSuccessEffects.
Print Assumptions CPUISABranchSuccessEffects.original_read_value.
Print Assumptions CPUISABranchSuccessEffects.successful_beq_fields.
Print Assumptions CPUISABranchSuccessEffects.successful_token_beq_fields.
Print Assumptions CPUISABranchSuccessEffects.successful_token_beq_register_frame.
