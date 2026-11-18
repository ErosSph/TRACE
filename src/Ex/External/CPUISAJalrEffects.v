(** Effects of a successful ORIGINAL JALR execution. Success excludes the
    misaligned-target exception, so no alignment premise is needed. The
    target is stated over the architectural register view [reg_word]; the
    link is the original nextPC relation, as for JAL. Pure ISA; no RTL. *)
From Coq Require Import ZArith List Lia.
Require Import Ex.External.CPUISAInstructionExecution Ex.External.CPUISAExecutionEffects
 Ex.External.CPUISARegisterUpdate Ex.External.CPURegisterEffectRelation
 Ex.External.CPUOriginalISAReference Ex.External.CPUOriginalADDFrontier
 Ex.External.CPUISAJalEffects Ex.External.CPUISABranchSuccessEffects Ex.External.CPUISABranchFamilyEffects Ex.External.PicoISARF
 Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface
 coqutil.Byte riscv.Utility.Monads riscv.Utility.Utility riscv.Spec.ExecuteI.
Import CPUISAInstructionExecution CPUISAExecutionEffects CPUISARegisterUpdate
 CPURegisterEffectRelation CPUOriginalISAReference CPUOriginalADDFrontier.
Local Open Scope Z_scope.

Module CPUISAJalrEffects.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.

(** The original target: (x[rs1] + imm) with bit 0 cleared. *)
Definition target(before:FormalSpec.State)rs1 imm:word:=
 Utility.and(word.add(CPUISABranchFamilyEffects.reg_word before rs1)(word.of_Z imm))(Utility.lnot(Utility.ZToReg 1)).

Theorem successful_jalr_fields (before after:FormalSpec.State) rd rs1 imm:
 ExecuteI.execute(Decode.Jalr rd rs1 imm)before=(Some tt,after) ->
 ISAProjectedRegisterEffects before after(register_operations rd(word.add(getPc before)(word.of_Z 4))) /\
 getPc after=getPc before /\getNextPc after=target before rs1 imm /\
 getInstMem after=getInstMem before /\getDataMem after=getDataMem before /\
 word.unsigned(target before rs1 imm)mod 4=0.
Proof.
 intro H;cbn[ExecuteI.execute]in H.
 apply bind_success in H;destruct H as[x[s1[HXr H]]].
 pose proof(CPUISABranchFamilyEffects.read_word before s1 rs1 x HXr)as VX.
 pose proof(original_read_preserves before s1 rs1 x HXr);subst s1.
 apply bind_success in H;destruct H as[pc[s2[HP H]]].
 pose proof(original_pc_read_preserves before s2 pc HP);subst s2.
 assert(HPC:pc=getPc before)by(inversion HP;reflexivity);subst pc x.
 cbv beta zeta in H.
 match type of H with context[if ?guard then _ else _]=>destruct guard eqn:HG end;[discriminate H|].
 apply bind_success in H;destruct H as[[] [written[HW HT]]].
 pose proof(original_set_register before written rd(word.add(getPc before)(word.of_Z 4))HW)as HR.
 destruct(original_write_frame before written rd(word.add(getPc before)(word.of_Z 4))HW)as[HPCFrame[HN[HI HM]]].
 destruct(CPUISABranchSuccessEffects.set_pc_fields written after _ HT)as[HRegs[HP'[HN'[HI' HM']]]].
 split;[intros address HA;unfold ISAView;rewrite HRegs;exact(HR address HA)|].
 split;[exact(eq_trans HP' HPCFrame)|].
 split;[exact HN'|].
 split;[exact(eq_trans HI' HI)|].
 split;[exact(eq_trans HM' HM)|].
 apply Bool.negb_false_iff in HG.
 change(word.eqb(word.modu(target before rs1 imm)(word.of_Z 4))(word.of_Z 0)=true)in HG.
 rewrite word.unsigned_eqb in HG;apply Z.eqb_eq in HG.
 rewrite word.unsigned_modu_nowrap in HG by(rewrite word.unsigned_of_Z_nowrap by lia;lia).
 rewrite word.unsigned_of_Z_nowrap in HG by lia;rewrite word.unsigned_of_Z_0 in HG;exact HG.
Qed.

Context {Token:Type}.
Variables token_pc token_word:Token->Z.

Theorem successful_token_jalr_fields token before after rd rs1 imm:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jalr rd rs1 imm) ->
 getPc after=target before rs1 imm /\
 getNextPc after=word.add(getPc after)(word.of_Z 4) /\
 getInstMem after=getInstMem before /\getDataMem after=getDataMem before /\
 word.unsigned(target before rs1 imm)mod 4=0.
Proof.
 intros HS HD.
 destruct(token_execute token_pc token_word token before after _ HS HD)as[middle[HE HEnd]].
 destruct(successful_jalr_fields before middle rd rs1 imm HE)as[_[_[HN[HI[HM HA]]]]].
 destruct(original_end_cycle_frontier middle after HEnd)as[HP'[HN'[HI' HM']]].
 split;[exact(eq_trans HP' HN)|].
 split;[rewrite HN',HP';reflexivity|].
 exact(conj(eq_trans HI' HI)(conj(eq_trans HM' HM)HA)).
Qed.

Theorem original_token_jalr_effect token before after rd rs1 imm:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jalr rd rs1 imm) ->
 ISAProjectedRegisterEffects before after
  (register_operations rd(word.add(getPc before)(word.of_Z 4))).
Proof.
 intros HS HD.
 destruct(token_execute token_pc token_word token before after _ HS HD)as[middle[HE HEnd]].
 destruct(successful_jalr_fields before middle rd rs1 imm HE)as[HR _].
 intros address HA;unfold ISAView.
 rewrite(end_cycle_register_frame middle after HEnd);exact(HR address HA).
Qed.

End ISA.
End CPUISAJalrEffects.
Print Assumptions CPUISAJalrEffects.successful_jalr_fields.
Print Assumptions CPUISAJalrEffects.successful_token_jalr_fields.
Print Assumptions CPUISAJalrEffects.original_token_jalr_effect.
