(** Original execution preserves the checked 21-data-op/JAL/branch/JALR(x0) ROM domain.
    This file has no RTL state or future CPU correctness hypothesis. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CPUJumpFamilyProgramDomain Ex.External.CPUISABranchFamilyEffects Ex.External.CPUProgramROM
 Ex.External.CPUGeneratedJointTemplate Ex.External.CPUOriginalISAReference
 Ex.External.CPUISAJalEffects Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte.
Import CPUJumpFamilyProgramDomain CPUGeneratedJointTemplate CPUOriginalISAReference.
Local Open Scope Z_scope.
Module CPUJumpFamilyProgramExecution.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.

Theorem checked_original_initial words:check_program words=true ->
 AtProgram words 0(FormalSpec.initial_state(FormalSpec.formal_initial_imem(CPUProgramROM.entries words))).
Proof. intro HC;unfold AtProgram;split.
 - unfold check_program in HC;repeat rewrite andb_true_iff in HC.
   destruct HC as[[HC _]_];apply Z.ltb_lt in HC;lia.
 - split.
   + change(word.unsigned(@word.of_Z 32 word 0)=0);rewrite word.unsigned_of_Z;reflexivity.
   + split;[reflexivity|apply CPUISAJalEffects.next_pc_aligned_unsigned].
     change(word.unsigned(@word.of_Z 32 word 4)=(word.unsigned(@word.of_Z 32 word 0)+4)mod 2^32).
     rewrite !word.unsigned_of_Z;reflexivity.
Qed.

Theorem checked_original_chain_domain words{Token:Type}(token_pc token_word:Token->Z)
 tokens(before after:FormalSpec.State)index:
 check_program words=true ->AtProgram words index before ->
 EffectChain(instruction_effect token_pc token_word)before tokens after ->
 exists next,AtProgram words next after /\getDataMem after=getDataMem before.
Proof. intros HP HA HE;revert index HA.
 induction HE;intros index HA.
 - exists index;exact(conj HA eq_refl).
 - pose proof(proj2(proj2(instruction_effect_sound token_pc token_word t a b H)))as HR.
   destruct(checked_run1_stays_in_program words index a b HP HA HR)as[next[HN HM]].
   destruct(IHHE next HN)as[last[HL HM']].
   exists last;exact(conj HL(eq_trans HM' HM)).
Qed.

Theorem checked_original_ledger_domain words{Token:Type}(token_pc token_word:Token->Z)
 tokens(frontier:FormalSpec.State):
 check_program words=true ->
 EffectChain(instruction_effect token_pc token_word)
 (FormalSpec.initial_state(FormalSpec.formal_initial_imem(CPUProgramROM.entries words)))tokens frontier ->
 exists index,AtProgram words index frontier.
Proof. intros HC HS;destruct(checked_original_chain_domain words token_pc token_word tokens _ frontier 0
 HC(checked_original_initial words HC)HS)as[index[HI HM]];exists index;exact HI.
Qed.

Theorem checked_original_frontier_total words{Token:Type}(token_pc token_word:Token->Z)
 tokens(frontier:FormalSpec.State):
 check_program words=true ->
 EffectChain(instruction_effect token_pc token_word)
 (FormalSpec.initial_state(FormalSpec.formal_initial_imem(CPUProgramROM.entries words)))tokens frontier ->
 exists index after,AtProgram words index frontier /\FormalSpec.run1 frontier=(Some tt,after) /\
 (exists next,AtProgram words next after) /\getDataMem after=getDataMem frontier.
Proof. intros HC HS;destruct(checked_original_ledger_domain words token_pc token_word tokens frontier HC HS)as[index HI].
 destruct(checked_run1_total words index frontier HC HI)as[after HR].
 destruct(checked_run1_stays_in_program words index frontier after HC HI HR)as[next[HN HM]].
 exists index,after;exact(conj HI(conj HR(conj(ex_intro _ next HN)HM))).
Qed.
End ISA.
End CPUJumpFamilyProgramExecution.
Print Assumptions CPUJumpFamilyProgramExecution.checked_original_initial.
Print Assumptions CPUJumpFamilyProgramExecution.checked_original_chain_domain.
Print Assumptions CPUJumpFamilyProgramExecution.checked_original_ledger_domain.
Print Assumptions CPUJumpFamilyProgramExecution.checked_original_frontier_total.
