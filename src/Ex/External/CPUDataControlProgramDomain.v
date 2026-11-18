(** Closed original-ISA ROM domain: 21 data operations and JAL.
    Checking this property makes no claim about CPU implementation coverage. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CPUProgramROM Ex.External.CPUOriginalADDFrontier
 Ex.External.CPUISAJalEffects Ex.External.CPUISAJalSuccessfulState
 Ex.External.CPUISAExecutionEffects Ex.External.CPUOriginalISAReference
 Ex.External.CV32E40PDataOpExecution Ex.External.CV32E40PDataOpISAInvariant
 Ex.External.CV32E40PDataOpProgramScope Ex.External.CV32E40PReq41Instruction
 Ex.RvCore.FormalSpec Ex.RvCore.Machine coqutil.Word.Interface
 coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 riscv.Spec.Decode riscv.Spec.ExecuteI riscv.Utility.Monads.
Import ListNotations CPUISAExecutionEffects CPUOriginalISAReference
 CV32E40PDataOpExecution CV32E40PDataOpProgramScope.
Local Open Scope Z_scope.
Module CPUDataControlProgramDomain.

Definition legal_instruction i := dataop21b i ||
 match i with Decode.Jal _ _=>true|_=>false end.
Definition next_address index i :=
 match i with Decode.Jal _ imm=>4*Z.of_nat index+imm|_=>4*Z.of_nat index+4 end.
Definition entry_ok words index :=
 let code:=nth index words 0 in
 match Decode.decode Decode.RV32I code with
 |Decode.IInstruction i=>
  (0 <=? code)&&(code <? 2^32)&&legal_instruction i&&
  (0 <=? next_address index i)&&(next_address index i <? 4*Z.of_nat(length words))&&
  (next_address index i mod 4 =? 0)
 |_=>false end.
Definition check_program words :=
 (0 <? Z.of_nat(length words))&&(Z.of_nat(length words) <=? 101)&&
 forallb(entry_ok words)(seq 0(length words)).

Lemma legal_instruction_sound i:
 legal_instruction i=true ->DataOp21 i \/ exists rd imm,i=Decode.Jal rd imm.
Proof. destruct i;cbn[legal_instruction dataop21b];try discriminate;intro H;
 first[left;reflexivity|right;repeat eexists]. Qed.

Theorem checked_entry words index:
 check_program words=true ->(index<length words)%nat ->
 exists i,Decode.decode Decode.RV32I(nth index words 0)=Decode.IInstruction i /\
 0<=nth index words 0<2^32 /\legal_instruction i=true /\
 0<=next_address index i<4*Z.of_nat(length words) /\next_address index i mod 4=0.
Proof. unfold check_program;rewrite !andb_true_iff;intros[[HP HL]HE]HI.
 apply forallb_forall with(x:=index)in HE;[|apply in_seq;lia].
 unfold entry_ok in HE;destruct(Decode.decode Decode.RV32I(nth index words 0))eqn:HD;try discriminate.
 apply andb_true_iff in HE as[HE HA];apply Z.eqb_eq in HA.
 repeat rewrite andb_true_iff in HE;destruct HE as[[[[H0 H32]HI0]HNext0]HNextHi].
 apply Z.leb_le in H0,HNext0;apply Z.ltb_lt in H32,HNextHi.
 exists iInstruction;exact(conj eq_refl(conj(conj H0 H32)(conj HI0(conj(conj HNext0 HNextHi)HA)))).
Qed.

Theorem checked_successor words index i:
 check_program words=true ->(index<length words)%nat ->
 Decode.decode Decode.RV32I(nth index words 0)=Decode.IInstruction i ->
 exists next,(next<length words)%nat /\next_address index i=4*Z.of_nat next.
Proof. intros HC HI HD;destruct(checked_entry words index HC HI)as[j[HJ[HW[HL[HB HA]]]]].
 rewrite HD in HJ;injection HJ as E;subst j.
 exists(Z.to_nat(next_address index i/4)).
 assert(HQ:0<=next_address index i/4)by(apply Z.div_pos;lia).
 rewrite Z2Nat.id by exact HQ.
 pose proof(Z.div_mod(next_address index i)4 ltac:(lia))as HE.
 split;[apply Nat2Z.inj_lt;rewrite Z2Nat.id by exact HQ;nia|nia]. Qed.

Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.

Definition AtProgram words index(before:FormalSpec.State):=
 (index<length words)%nat /\word.unsigned(getPc before)=4*Z.of_nat index /\
 getInstMem before=FormalSpec.formal_initial_imem(CPUProgramROM.entries words) /\
 CPUISAJalEffects.NextPCAligned before.

Theorem checked_current_instruction words index(before:FormalSpec.State):
 check_program words=true ->AtProgram words index before ->
 exists i,Decode.decode Decode.RV32I(nth index words 0)=Decode.IInstruction i /\
 CV32E40PReq41Instruction.CurrentInstruction before i /\legal_instruction i=true /\
 0<=next_address index i<4*Z.of_nat(length words) /\next_address index i mod 4=0.
Proof. intros HC[HI[HP[HM HN]]].
 destruct(checked_entry words index HC HI)as[i[HD[HW[HL[HT HA]]]]].
 assert(HLength:Z.of_nat(length words)<=2^30).
 { unfold check_program in HC;repeat rewrite andb_true_iff in HC.
   destruct HC as[[_ HC]_];apply Z.leb_le in HC;lia. }
 destruct(CPUProgramROM.dense_image_little_endian_load words(getPc before)index HLength HP)as[bytes[HF HV]].
 rewrite Z.mod_small in HV by exact HW.
 exists i;split;[exact HD|];split.
 - constructor.
   + rewrite HP;apply Z.mod_divide;[lia|exists(Z.of_nat index);ring].
   + exists bytes;split;[rewrite HM;exact HF|].
     exact(eq_trans(f_equal(Decode.decode Decode.RV32I)HV)HD).
 - exact(conj HL(conj HT HA)). Qed.

Theorem checked_run1_total words index(before:FormalSpec.State):
 check_program words=true ->AtProgram words index before ->
 exists after,FormalSpec.run1 before=(Some tt,after).
Proof. intros HC HAt;destruct(checked_current_instruction words index before HC HAt)
 as[i[HD[HCurrent[HL[HT HA]]]]].
 destruct(legal_instruction_sound i HL)as[HI|[rd[imm HE]]].
 - exists(dataop_post before i);apply run1_exact;[exact HI| |exact HCurrent].
   exact(CV32E40PDataOpISAInvariant.decoded_operands_legal(nth index words 0)i HI HD).
 - subst i;eexists;eapply CPUISAJalEffects.current_jal_run1_total;[exact HCurrent|].
   unfold CPUISAJalEffects.TargetDomain;rewrite(proj1(proj2 HAt)).
   assert(HLength:Z.of_nat(length words)<=101).
   { unfold check_program in HC;repeat rewrite andb_true_iff in HC.
     destruct HC as[[_ HC]_];now apply Z.leb_le in HC. }
   split;[cbn[next_address]in HT;lia|exact HA]. Qed.

Theorem checked_run1_stays_in_program words index(before after:FormalSpec.State):
 check_program words=true ->AtProgram words index before ->
 FormalSpec.run1 before=(Some tt,after) ->
 exists next,AtProgram words next after /\getDataMem after=getDataMem before.
Proof. intros HC HAt HRun.
 destruct(checked_current_instruction words index before HC HAt)as[i[HD[HCurrent[HL[HT HA]]]]].
 destruct(checked_successor words index i HC(proj1 HAt)HD)as[next[HI HAddress]].
 destruct HAt as[HIndex[HP[HM HN]]].
 assert(HFields:getPc after=word.add(getPc before)(word.of_Z
   (match i with Decode.Jal _ imm=>imm|_=>4 end)) /\
   getInstMem after=getInstMem before /\getDataMem after=getDataMem before).
 { destruct(legal_instruction_sound i HL)as[HData|[rd[imm HEq]]].
   - pose proof(run1_exact before i HData
     (CV32E40PDataOpISAInvariant.decoded_operands_legal(nth index words 0)i HData HD)HCurrent)as HExact.
     rewrite HRun in HExact;injection HExact as HAfter;subst after.
     assert(HOffset:(match i with Decode.Jal _ imm=>imm|_=>4 end)=4).
     { destruct i;cbn[DataOp21 dataop21b]in HData;try discriminate;reflexivity. }
     rewrite HOffset;change(getNextPc before=word.add(getPc before)(word.of_Z 4) /\
       getInstMem before=getInstMem before /\getDataMem before=getDataMem before).
     exact(conj HN(conj eq_refl eq_refl)).
   - subst i;pose proof HRun as HStep.
     rewrite(CV32E40PReq41Instruction.run1_current_instruction before _ HCurrent)in HStep.
     change(Bind(ExecuteI.execute(Decode.Jal rd imm))(fun _=>Machine.endCycleNormal)before=(Some tt,after))in HStep.
     apply bind_success in HStep;destruct HStep as[[] [middle[HE HEnd]]].
     destruct(CPUOriginalADDFrontier.original_end_cycle_frontier middle after HEnd)as[HPC[HNext[HROM HRAM]]].
     destruct(CPUISAJalSuccessfulState.successful_jal_fields before middle rd imm HE)as[_[HF[HR HDM]]].
     exact(conj(eq_trans HPC HF)(conj(eq_trans HROM HR)(eq_trans HRAM HDM))). }
 destruct HFields as[HPAfter[HIFrame HDFrame]].
 assert(HLength:Z.of_nat(length words)<=101).
 { unfold check_program in HC;repeat rewrite andb_true_iff in HC.
   destruct HC as[[_ HC]_];now apply Z.leb_le in HC. }
 assert(HUnsigned:word.unsigned(getPc after)=next_address index i).
 { rewrite HPAfter,word.unsigned_add,word.unsigned_of_Z;unfold word.wrap.
   rewrite Z.add_mod_idemp_r by lia;rewrite HP.
   destruct i;cbn[next_address]in HT|-*;apply Z.mod_small;lia. }
 exists next;split;[|exact HDFrame].
 unfold AtProgram;refine(conj HI(conj _(conj _ _))).
 - exact(eq_trans HUnsigned HAddress).
 - exact(eq_trans HIFrame HM).
 - exact(CPUISAJalEffects.run1_next_pc_aligned before after HRun).
Qed.
End ISA.
End CPUDataControlProgramDomain.
Print Assumptions CPUDataControlProgramDomain.legal_instruction_sound.
Print Assumptions CPUDataControlProgramDomain.checked_entry.
Print Assumptions CPUDataControlProgramDomain.checked_successor.
Print Assumptions CPUDataControlProgramDomain.checked_current_instruction.
Print Assumptions CPUDataControlProgramDomain.checked_run1_total.
Print Assumptions CPUDataControlProgramDomain.checked_run1_stays_in_program.
