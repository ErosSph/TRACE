(** Closed original-ISA ROM domain: 21 data operations, JAL and the six
    conditional branches. A branch has two successors (fall-through and
    target); both are checked statically. Generalises the accepted
    [CPUBranchProgramDomain] (BEQ only), which it contains. The accepted 21-data/JAL [CPUDataControlProgramDomain] is left
    unchanged and is included by [baseline_program_accepted].
    Checking this property makes no claim about CPU implementation coverage. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CPUProgramROM Ex.External.CPUOriginalADDFrontier
 Ex.External.CPUISAJalEffects Ex.External.CPUISAJalSuccessfulState
 Ex.External.CPUISAExecutionEffects Ex.External.CPUOriginalISAReference
 Ex.External.CV32E40PDataOpExecution Ex.External.CV32E40PDataOpISAInvariant
 Ex.External.CV32E40PDataOpProgramScope Ex.External.CV32E40PReq41Instruction
 Ex.External.CV32E40PBranchExecution Ex.External.CPUDataControlProgramDomain
 Ex.External.CPUISABranchFamilyEffects Ex.External.CPUISABranchFamilyFields Ex.External.CPUBranchProgramDomain
 Ex.RvCore.FormalSpec Ex.RvCore.Machine coqutil.Word.Interface
 coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 riscv.Spec.Decode riscv.Spec.ExecuteI riscv.Utility.Monads riscv.Proofs.VerifyDecode.
Import ListNotations CPUISAExecutionEffects CPUOriginalISAReference
 CV32E40PDataOpExecution CV32E40PDataOpProgramScope CV32E40PReq41Instruction.
Local Open Scope Z_scope.
Module CPUBranchFamilyProgramDomain.

Definition branch_instruction i := CPUISABranchFamilyFields.is_branch i.
Definition legal_instruction i :=
 CPUDataControlProgramDomain.legal_instruction i || branch_instruction i.
Definition successors index i : list Z :=
 match i with
 |Decode.Beq _ _ imm|Decode.Bne _ _ imm|Decode.Blt _ _ imm|Decode.Bge _ _ imm|Decode.Bltu _ _ imm|Decode.Bgeu _ _ imm=>
   [4*Z.of_nat index+4;4*Z.of_nat index+imm]
 |_=>[CPUDataControlProgramDomain.next_address index i] end.
Definition target_ok (words:list Z) address :=
 (0 <=? address)&&(address <? 4*Z.of_nat(length words))&&(address mod 4 =? 0).
Definition entry_ok words index :=
 let code:=nth index words 0 in
 match Decode.decode Decode.RV32I code with
 |Decode.IInstruction i=>
  (0 <=? code)&&(code <? 2^32)&&legal_instruction i&&forallb(target_ok words)(successors index i)
 |_=>false end.
Definition check_program words :=
 (0 <? Z.of_nat(length words))&&(Z.of_nat(length words) <=? 101)&&
 forallb(entry_ok words)(seq 0(length words)).

Lemma successors_branch index op rs1 rs2 imm:
 successors index(CPUISABranchFamilyEffects.instruction op rs1 rs2 imm)=[4*Z.of_nat index+4;4*Z.of_nat index+imm].
Proof. destruct op;reflexivity. Qed.
Lemma branch_immediate_instruction op rs1 rs2 imm:
 CV32E40PBranchExecution.branch_immediate(CPUISABranchFamilyEffects.instruction op rs1 rs2 imm)=imm.
Proof. destruct op;reflexivity. Qed.
Lemma branch_in_family op rs1 rs2 imm:InFamily FamilyBranch(CPUISABranchFamilyEffects.instruction op rs1 rs2 imm).
Proof. destruct op;reflexivity. Qed.

Lemma legal_instruction_sound i:
 legal_instruction i=true ->
 DataOp21 i \/(exists rd imm,i=Decode.Jal rd imm) \/exists op rs1 rs2 imm,i=CPUISABranchFamilyEffects.instruction op rs1 rs2 imm.
Proof. unfold legal_instruction;rewrite orb_true_iff;intros[H|H].
 - destruct(CPUDataControlProgramDomain.legal_instruction_sound i H)as[HD|HJ];[left|right;left];assumption.
 - right;right;exact(CPUISABranchFamilyFields.branch_cases i H). Qed.

(** The accepted BEQ domain is a subset of this one. *)
Theorem beq_program_accepted words:
 CPUBranchProgramDomain.check_program words=true ->check_program words=true.
Proof. unfold CPUBranchProgramDomain.check_program,check_program;
 rewrite !andb_true_iff;intros[[HP HL]HE];split;[exact(conj HP HL)|].
 rewrite forallb_forall in HE|-*;intros index HI;specialize(HE index HI).
 unfold CPUBranchProgramDomain.entry_ok in HE;unfold entry_ok.
 destruct(Decode.decode Decode.RV32I(nth index words 0));try discriminate.
 rewrite !andb_true_iff in HE;destruct HE as[[[H0 H32]HI0]HA].
 rewrite !andb_true_iff;split;[split;[split;[exact H0|exact H32]|]|].
 - unfold CPUBranchProgramDomain.legal_instruction in HI0;unfold legal_instruction;rewrite orb_true_iff in HI0|-*.
   destruct HI0 as[H|H];[left;exact H|right;destruct iInstruction;try discriminate;reflexivity].
 - unfold CPUBranchProgramDomain.successors in HA;unfold successors;destruct iInstruction;try exact HA;exfalso;
   cbn[CPUBranchProgramDomain.legal_instruction CPUDataControlProgramDomain.legal_instruction CPUBranchProgramDomain.beq_instruction dataop21b orb]in HI0;
   discriminate. Qed.

(** The accepted baseline domain is a subset of this one. *)
Theorem baseline_program_accepted words:
 CPUDataControlProgramDomain.check_program words=true ->check_program words=true.
Proof. unfold CPUDataControlProgramDomain.check_program,check_program;
 rewrite !andb_true_iff;intros[[HP HL]HE];split;[exact(conj HP HL)|].
 rewrite forallb_forall in HE|-*;intros index HI;specialize(HE index HI).
 unfold CPUDataControlProgramDomain.entry_ok in HE;unfold entry_ok.
 destruct(Decode.decode Decode.RV32I(nth index words 0));try discriminate.
 rewrite !andb_true_iff in HE;destruct HE as[[[[[H0 H32]HI0]HN0]HNH]HA].
 assert(HB:branch_instruction iInstruction=false).
 { destruct iInstruction;cbn[CPUDataControlProgramDomain.legal_instruction dataop21b]in HI0;
   try discriminate;reflexivity. }
 assert(HS:successors index iInstruction=[CPUDataControlProgramDomain.next_address index iInstruction]).
 { destruct iInstruction;cbn[branch_instruction CPUISABranchFamilyFields.is_branch]in HB;try discriminate;reflexivity. }
 rewrite HS;cbn[forallb];unfold target_ok,legal_instruction;rewrite HI0.
 rewrite !andb_true_iff;repeat split;try assumption;reflexivity. Qed.

Theorem checked_entry words index:
 check_program words=true ->(index<length words)%nat ->
 exists i,Decode.decode Decode.RV32I(nth index words 0)=Decode.IInstruction i /\
 0<=nth index words 0<2^32 /\legal_instruction i=true /\
 Forall(fun a=>0<=a<4*Z.of_nat(length words) /\a mod 4=0)(successors index i).
Proof. unfold check_program;rewrite !andb_true_iff;intros[[HP HL]HE]HI.
 apply forallb_forall with(x:=index)in HE;[|apply in_seq;lia].
 unfold entry_ok in HE;destruct(Decode.decode Decode.RV32I(nth index words 0))eqn:HD;try discriminate.
 rewrite !andb_true_iff in HE;destruct HE as[[[H0 H32]HI0]HS].
 apply Z.leb_le in H0;apply Z.ltb_lt in H32.
 exists iInstruction;refine(conj eq_refl(conj(conj H0 H32)(conj HI0 _))).
 apply Forall_forall;intros a HA;rewrite forallb_forall in HS;specialize(HS a HA).
 unfold target_ok in HS;rewrite !andb_true_iff in HS;destruct HS as[[HA0 HAH]HAM].
 apply Z.leb_le in HA0;apply Z.ltb_lt in HAH;apply Z.eqb_eq in HAM;lia. Qed.

Lemma checked_length words:check_program words=true ->Z.of_nat(length words)<=101.
Proof. unfold check_program;rewrite !andb_true_iff;intros[[_ H]_];now apply Z.leb_le. Qed.

Lemma branch_operands_legal code op rs1 rs2 imm:
 Decode.decode Decode.RV32I code=Decode.IInstruction(CPUISABranchFamilyEffects.instruction op rs1 rs2 imm) ->
 LegalOperands(CPUISABranchFamilyEffects.instruction op rs1 rs2 imm).
Proof.
 intro HE;destruct op;cbn[CPUISABranchFamilyEffects.instruction]in HE|-*;(destruct(verify_decode Decode.RV32I code eq_refl)as[HV|HB];[rewrite HE in HV|congruence]);
 cbv[verify respects_bounds apply_InstructionMapper Verifier map_SB verify_SB bitwidth verify_iset]in HV;
 unfold LegalOperands;cbn[destination_register source_registers];
 (split;[exact I|repeat apply Forall_cons;try apply Forall_nil;unfold CV32E40PReq40StateRel.CV32E40PReq40StateRel.legal_reg;lia]).
Qed.

Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.

Definition AtProgram:=CPUDataControlProgramDomain.AtProgram.

Theorem checked_current_instruction words index(before:FormalSpec.State):
 check_program words=true ->AtProgram words index before ->
 exists i,Decode.decode Decode.RV32I(nth index words 0)=Decode.IInstruction i /\
 CV32E40PReq41Instruction.CurrentInstruction before i /\legal_instruction i=true /\
 Forall(fun a=>0<=a<4*Z.of_nat(length words) /\a mod 4=0)(successors index i).
Proof. intros HC[HI[HP[HM HN]]].
 destruct(checked_entry words index HC HI)as[i[HD[HW[HL HT]]]].
 assert(HLength:Z.of_nat(length words)<=2^30)by(pose proof(checked_length words HC);lia).
 destruct(CPUProgramROM.dense_image_little_endian_load words(getPc before)index HLength HP)as[bytes[HF HV]].
 rewrite Z.mod_small in HV by exact HW.
 exists i;split;[exact HD|];split.
 - constructor.
   + rewrite HP;apply Z.mod_divide;[lia|exists(Z.of_nat index);ring].
   + exists bytes;split;[rewrite HM;exact HF|].
     exact(eq_trans(f_equal(Decode.decode Decode.RV32I)HV)HD).
 - exact(conj HL HT). Qed.

(** Statically checked branch targets are aligned whenever the branch is taken. *)
Lemma branch_taken_target_aligned words index(before:FormalSpec.State) op rs1 rs2 imm:
 check_program words=true ->AtProgram words index before ->
 Forall(fun a=>0<=a<4*Z.of_nat(length words) /\a mod 4=0)(successors index(CPUISABranchFamilyEffects.instruction op rs1 rs2 imm)) ->
 CV32E40PBranchExecution.TakenTargetAligned before(CPUISABranchFamilyEffects.instruction op rs1 rs2 imm).
Proof. intros HC[_[HP _]]HT _.
 pose proof(checked_length words HC)as HLen.
 rewrite successors_branch in HT;destruct(Forall_inv(Forall_inv_tail HT))as[HB HA].
 unfold CV32E40PBranchExecution.reference_branch_target;rewrite branch_immediate_instruction.
 rewrite word.unsigned_add,word.unsigned_of_Z;unfold word.wrap.
 rewrite Z.add_mod_idemp_r by lia;rewrite HP,(Z.mod_small _ (2^32)) by lia;exact HA. Qed.

Theorem checked_run1_total words index(before:FormalSpec.State):
 check_program words=true ->AtProgram words index before ->
 exists after,FormalSpec.run1 before=(Some tt,after).
Proof. intros HC HAt;destruct(checked_current_instruction words index before HC HAt)
 as[i[HD[HCurrent[HL HT]]]].
 destruct(legal_instruction_sound i HL)as[HI|[[rd[imm HE]]|[op[rs1[rs2[imm HE]]]]]].
 - exists(dataop_post before i);apply run1_exact;[exact HI| |exact HCurrent].
   exact(CV32E40PDataOpISAInvariant.decoded_operands_legal(nth index words 0)i HI HD).
 - subst i;eexists;eapply CPUISAJalEffects.current_jal_run1_total;[exact HCurrent|].
   pose proof(checked_length words HC);cbn[successors]in HT;destruct(Forall_inv HT)as[HB HA].
   unfold CPUISAJalEffects.TargetDomain;rewrite(proj1(proj2 HAt)).
   cbn[CPUDataControlProgramDomain.next_address]in HB,HA;split;[lia|exact HA].
 - subst i;exists(CV32E40PBranchExecution.branch_post before(CPUISABranchFamilyEffects.instruction op rs1 rs2 imm)).
   apply CV32E40PBranchExecution.run1_branch_exact;[exact(branch_in_family op rs1 rs2 imm)| |
    exact(branch_taken_target_aligned words index before op rs1 rs2 imm HC HAt HT)|exact HCurrent].
   exact(branch_operands_legal(nth index words 0)op rs1 rs2 imm HD). Qed.

Lemma successor_index (words:list Z) a:
 0<=a<4*Z.of_nat(length words) ->a mod 4=0 ->
 exists next,(next<length words)%nat /\a=4*Z.of_nat next.
Proof. intros HB HA;exists(Z.to_nat(a/4)).
 assert(HQ:0<=a/4)by(apply Z.div_pos;lia).
 pose proof(Z.div_mod a 4 ltac:(lia))as HE.
 split;[apply Nat2Z.inj_lt;rewrite Z2Nat.id by exact HQ;nia|rewrite Z2Nat.id by exact HQ;lia]. Qed.

Theorem checked_run1_stays_in_program words index(before after:FormalSpec.State):
 check_program words=true ->AtProgram words index before ->
 FormalSpec.run1 before=(Some tt,after) ->
 exists next,AtProgram words next after /\getDataMem after=getDataMem before.
Proof. intros HC HAt HRun.
 destruct(checked_current_instruction words index before HC HAt)as[i[HD[HCurrent[HL HT]]]].
 pose proof(checked_length words HC)as HLength.
 destruct HAt as[HIndex[HP[HM HN]]].
 assert(HFields:exists a,In a(successors index i) /\word.unsigned(getPc after)=a /\
   getInstMem after=getInstMem before /\getDataMem after=getDataMem before).
 { destruct(legal_instruction_sound i HL)as[HData|[[rd[imm HEq]]|[op[rs1[rs2[imm HEq]]]]]].
   - pose proof(run1_exact before i HData
     (CV32E40PDataOpISAInvariant.decoded_operands_legal(nth index words 0)i HData HD)HCurrent)as HExact.
     rewrite HRun in HExact;injection HExact as HAfter;subst after.
     assert(HS:successors index i=[4*Z.of_nat index+4]).
     { destruct i;cbn[DataOp21 dataop21b]in HData;try discriminate;reflexivity. }
     rewrite HS in HT|-*;destruct(Forall_inv HT)as[HB _].
     exists(4*Z.of_nat index+4);split;[left;reflexivity|].
     change(word.unsigned(getNextPc before)=4*Z.of_nat index+4 /\
       getInstMem before=getInstMem before /\getDataMem before=getDataMem before).
     rewrite HN;unfold CPUISAJalEffects.link;rewrite word.unsigned_add,word.unsigned_of_Z;unfold word.wrap.
     rewrite Z.add_mod_idemp_r by lia;rewrite HP,(Z.mod_small _ (2^32)) by lia;repeat split;reflexivity.
   - subst i;pose proof HRun as HStep.
     rewrite(CV32E40PReq41Instruction.run1_current_instruction before _ HCurrent)in HStep.
     change(Bind(ExecuteI.execute(Decode.Jal rd imm))(fun _=>Machine.endCycleNormal)before=(Some tt,after))in HStep.
     apply bind_success in HStep;destruct HStep as[[] [middle[HE HEnd]]].
     destruct(CPUOriginalADDFrontier.original_end_cycle_frontier middle after HEnd)as[HPC[HNext[HROM HRAM]]].
     destruct(CPUISAJalSuccessfulState.successful_jal_fields before middle rd imm HE)as[_[HF[HR HDM]]].
     cbn[successors]in HT|-*;destruct(Forall_inv HT)as[HB _].
     cbn[CPUDataControlProgramDomain.next_address]in HB|-*.
     exists(4*Z.of_nat index+imm);split;[left;reflexivity|].
     split;[|exact(conj(eq_trans HROM HR)(eq_trans HRAM HDM))].
     rewrite HPC,HF,word.unsigned_add,word.unsigned_of_Z;unfold word.wrap.
     rewrite Z.add_mod_idemp_r by lia;rewrite HP,(Z.mod_small _ (2^32)) by lia;reflexivity.
   - subst i.
     pose proof(CV32E40PBranchExecution.run1_branch_exact before(CPUISABranchFamilyEffects.instruction op rs1 rs2 imm)
      (branch_in_family op rs1 rs2 imm)
      (branch_operands_legal(nth index words 0)op rs1 rs2 imm HD)
      (branch_taken_target_aligned words index before op rs1 rs2 imm HC(conj HIndex(conj HP(conj HM HN)))HT)
      HCurrent)as HExact.
     rewrite HRun in HExact;injection HExact as HAfter;subst after.
     rewrite successors_branch in HT|-*;destruct(Forall_inv HT)as[HB0 _];destruct(Forall_inv(Forall_inv_tail HT))as[HB1 _].
     cbn[CV32E40PBranchExecution.branch_post getPc getInstMem getDataMem].
     unfold CV32E40PBranchExecution.branch_next_pc.
     destruct(CV32E40PBranchExecution.reference_branch_taken before(CPUISABranchFamilyEffects.instruction op rs1 rs2 imm)).
     + exists(4*Z.of_nat index+imm);split;[right;left;reflexivity|split;[|split;reflexivity]].
       unfold CV32E40PBranchExecution.reference_branch_target;rewrite branch_immediate_instruction.
       rewrite word.unsigned_add,word.unsigned_of_Z;unfold word.wrap.
       rewrite Z.add_mod_idemp_r by lia;rewrite HP,(Z.mod_small _ (2^32)) by lia;reflexivity.
     + exists(4*Z.of_nat index+4);split;[left;reflexivity|split;[|split;reflexivity]].
       rewrite HN;unfold CPUISAJalEffects.link;rewrite word.unsigned_add,word.unsigned_of_Z;unfold word.wrap.
       rewrite Z.add_mod_idemp_r by lia;rewrite HP,(Z.mod_small _ (2^32)) by lia;reflexivity. }
 destruct HFields as[a[HIn[HPAfter[HIFrame HDFrame]]]].
 assert(HA:0<=a<4*Z.of_nat(length words) /\a mod 4=0)by(rewrite Forall_forall in HT;exact(HT a HIn)).
 destruct(successor_index words a(proj1 HA)(proj2 HA))as[next[HI HAddress]].
 exists next;split;[|exact HDFrame].
 unfold AtProgram,CPUDataControlProgramDomain.AtProgram;refine(conj HI(conj _(conj _ _))).
 - exact(eq_trans HPAfter HAddress).
 - exact(eq_trans HIFrame HM).
 - exact(CPUISAJalEffects.run1_next_pc_aligned before after HRun).
Qed.
End ISA.
End CPUBranchFamilyProgramDomain.
Print Assumptions CPUBranchFamilyProgramDomain.legal_instruction_sound.
Print Assumptions CPUBranchFamilyProgramDomain.baseline_program_accepted.
Print Assumptions CPUBranchFamilyProgramDomain.beq_program_accepted.
Print Assumptions CPUBranchFamilyProgramDomain.checked_entry.
Print Assumptions CPUBranchFamilyProgramDomain.checked_length.
Print Assumptions CPUBranchFamilyProgramDomain.branch_operands_legal.
Print Assumptions CPUBranchFamilyProgramDomain.checked_current_instruction.
Print Assumptions CPUBranchFamilyProgramDomain.branch_taken_target_aligned.
Print Assumptions CPUBranchFamilyProgramDomain.checked_run1_total.
Print Assumptions CPUBranchFamilyProgramDomain.checked_run1_stays_in_program.
Print Assumptions CPUBranchFamilyProgramDomain.successors_branch.
