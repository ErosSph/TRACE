(** Effects of a successful ORIGINAL execution of any of the six conditional
    branches. The condition is the accepted [isa_branch_guard] applied to the
    architectural register views; success excludes the misaligned-target
    exception, so no alignment premise is needed. Generalises the accepted BEQ
    lemmas [CPUISABranchSuccessEffects] / [CPUISABranchTargetAligned]. *)
From Coq Require Import ZArith List Lia.
Require Import Ex.External.CPUISAInstructionExecution Ex.External.CPUISAExecutionEffects
 Ex.External.CPURegisterEffectRelation Ex.External.CPUOriginalISAReference
 Ex.External.CPUOriginalADDFrontier Ex.External.CPUISAJalEffects Ex.External.PicoISARF
 Ex.External.CPUISABranchSuccessEffects
 Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface
 coqutil.Byte riscv.Utility.Monads riscv.Utility.Utility riscv.Spec.ExecuteI.
Import CPUISAInstructionExecution CPUISAExecutionEffects CPURegisterEffectRelation
 CPUOriginalISAReference CPUOriginalADDFrontier.
Local Open Scope Z_scope.

Module CPUISABranchFamilyEffects.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.

(** The six conditional branches, as decoded instructions. *)
Inductive Op:=BranchEq|BranchNe|BranchLt|BranchGe|BranchLtu|BranchGeu.
Definition instruction op rs1 rs2 imm:Decode.InstructionI:=match op with
 |BranchEq=>Decode.Beq rs1 rs2 imm|BranchNe=>Decode.Bne rs1 rs2 imm
 |BranchLt=>Decode.Blt rs1 rs2 imm|BranchGe=>Decode.Bge rs1 rs2 imm
 |BranchLtu=>Decode.Bltu rs1 rs2 imm|BranchGeu=>Decode.Bgeu rs1 rs2 imm end.
(** Exactly the original ExecuteI conditions. *)
Definition guard op(a b:word):bool:=match op with
 |BranchEq=>reg_eqb a b|BranchNe=>negb(reg_eqb a b)
 |BranchLt=>signed_less_than a b|BranchGe=>negb(signed_less_than a b)
 |BranchLtu=>ltu a b|BranchGeu=>negb(ltu a b) end.
Definition reg_word(before:FormalSpec.State)rs:word:=word.of_Z(ISAView before rs).
Definition branch_taken op(before:FormalSpec.State)rs1 rs2:bool:=guard op(reg_word before rs1)(reg_word before rs2).

Lemma read_word (before after:FormalSpec.State) rs value:
 Machine.getRegister rs before=(Some value,after) ->value=reg_word before rs.
Proof. intro H;unfold reg_word;rewrite <-(CPUISABranchSuccessEffects.original_read_value before after rs value H).
 symmetry;apply word.of_Z_unsigned. Qed.


Theorem successful_branch_fields (before after:FormalSpec.State) op rs1 rs2 imm:
 ExecuteI.execute(instruction op rs1 rs2 imm)before=(Some tt,after) ->
 getRegs after=getRegs before /\getPc after=getPc before /\
 getNextPc after=(if branch_taken op before rs1 rs2
  then word.add(getPc before)(word.of_Z imm) else getNextPc before) /\
 getInstMem after=getInstMem before /\getDataMem after=getDataMem before /\
 (branch_taken op before rs1 rs2=true ->(word.unsigned(getPc before)+imm)mod 4=0).
Proof.
 intro H;unfold branch_taken.
 destruct op;cbn[instruction ExecuteI.execute]in H;cbn[guard];
 apply bind_success in H;destruct H as[x[s1[HXr H]]];
 pose proof(read_word before s1 rs1 x HXr)as VX;
 pose proof(original_read_preserves before s1 rs1 x HXr);subst s1;
 apply bind_success in H;destruct H as[y[s2[HYr H]]];
 pose proof(read_word before s2 rs2 y HYr)as VY;
 pose proof(original_read_preserves before s2 rs2 y HYr);subst s2;
 apply bind_success in H;destruct H as[pc[s3[HP H]]];
 pose proof(original_pc_read_preserves before s3 pc HP);subst s3;
 assert(HPC:pc=getPc before)by(inversion HP;reflexivity);subst pc x y;
 unfold when in H;cbv beta zeta in H;
 (lazymatch type of H with(if ?c then _ else _)_=_=>destruct c eqn:HC end;
 [match type of H with context[if ?g then _ else _]=>destruct g eqn:HG end;[discriminate H|];
  destruct(CPUISABranchSuccessEffects.set_pc_fields before after _ H)as[HR[HPc[HN[HI HM]]]];
  split;[exact HR|split;[exact HPc|split;[exact HN|split;[exact HI|split;[exact HM|intros _]]]]];
  apply Bool.negb_false_iff in HG;
  change(word.eqb(word.modu(word.add(getPc before)(word.of_Z imm))(word.of_Z 4))(word.of_Z 0)=true)in HG;
  rewrite word.unsigned_eqb in HG;apply Z.eqb_eq in HG;
  rewrite word.unsigned_modu_nowrap in HG by(rewrite word.unsigned_of_Z_nowrap by lia;lia);
  rewrite word.unsigned_of_Z_nowrap in HG by lia;rewrite word.unsigned_of_Z_0 in HG;
  rewrite word.unsigned_add,word.unsigned_of_Z in HG;unfold word.wrap in HG;
  rewrite Z.add_mod_idemp_r in HG by lia;
  rewrite <-(Znumtheory.Zmod_div_mod 4(2^32)_ ltac:(lia) ltac:(lia) ltac:(exists(2^30);reflexivity))in HG;
  exact HG
 |cbn[Return OState_Monad]in H;inversion H;subst;repeat split;try reflexivity;discriminate]).
Qed.

Context {Token:Type}.
Variables token_pc token_word:Token->Z.

Theorem successful_token_branch_fields token before after op rs1 rs2 imm:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(instruction op rs1 rs2 imm) ->
 CPUISAJalEffects.NextPCAligned before ->
 getRegs after=getRegs before /\
 getPc after=(if branch_taken op before rs1 rs2
  then CPUISAJalEffects.target before imm else CPUISAJalEffects.link before) /\
 getNextPc after=word.add(getPc after)(word.of_Z 4) /\
 getInstMem after=getInstMem before /\getDataMem after=getDataMem before.
Proof.
 intros HS HD HA.
 destruct(token_execute token_pc token_word token before after _ HS HD)as[middle[HE HEnd]].
 destruct(successful_branch_fields before middle op rs1 rs2 imm HE)as[HR[HP[HN[HI[HM _]]]]].
 destruct(original_end_cycle_frontier middle after HEnd)as[HP'[HN'[HI' HM']]].
 assert(HRegs:getRegs after=getRegs middle)by(destruct middle;inversion HEnd;reflexivity).
 split;[exact(eq_trans HRegs HR)|].
 split;[rewrite HP',HN;unfold CPUISAJalEffects.target,CPUISAJalEffects.link;
  destruct(branch_taken op before rs1 rs2);[reflexivity|exact HA]|].
 split;[rewrite HN',HP';reflexivity|].
 exact(conj(eq_trans HI' HI)(eq_trans HM' HM)).
Qed.

Theorem successful_token_branch_taken_aligned token before after op rs1 rs2 imm:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(instruction op rs1 rs2 imm) ->
 branch_taken op before rs1 rs2=true ->
 (word.unsigned(getPc before)+imm)mod 4=0.
Proof.
 intros HS HD HT.
 destruct(token_execute token_pc token_word token before after _ HS HD)as[middle[HE _]].
 exact(proj2(proj2(proj2(proj2(proj2(successful_branch_fields before middle op rs1 rs2 imm HE)))))HT).
Qed.

Theorem successful_token_branch_register_frame token before after op rs1 rs2 imm:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(instruction op rs1 rs2 imm) ->
 forall i,ISAView after i=ISAView before i.
Proof.
 intros HS HD i.
 destruct(token_execute token_pc token_word token before after _ HS HD)as[middle[HE HEnd]].
 destruct(successful_branch_fields before middle op rs1 rs2 imm HE)as[HR _].
 assert(HRegs:getRegs after=getRegs middle)by(destruct middle;inversion HEnd;reflexivity).
 unfold ISAView;rewrite HRegs,HR;reflexivity.
Qed.
End ISA.
End CPUISABranchFamilyEffects.
Print Assumptions CPUISABranchFamilyEffects.successful_branch_fields.
Print Assumptions CPUISABranchFamilyEffects.successful_token_branch_fields.
Print Assumptions CPUISABranchFamilyEffects.successful_token_branch_taken_aligned.
Print Assumptions CPUISABranchFamilyEffects.successful_token_branch_register_frame.
