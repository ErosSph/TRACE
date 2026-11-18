(** Relate a packed byte bank to the ORIGINAL byte-addressed ISA memory.
    Addresses outside the physical bank retain the original zero background.
    No finite enumeration of FormalSpec.zeroed is performed. *)
From Coq Require Import ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Ex.RvCore.FormalSpec
 Ex.External.CPUGeneratedJointTemplate Ex.External.CPUOriginalISAReference Ex.External.CPUOriginalADDFrontier
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte.
Import ExtendedSV ExtendedSVWordInvariant.
Local Open Scope Z_scope.
Module CPUByteBankRelation.
Section Memory.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Mem:map.map word byte}.

Definition bank_byte width root capacity state (address:word):byte:=
 if word.unsigned address <? Z.of_nat capacity then
 byte.of_Z(norm 8(Z.shiftr(norm width(read_signal state root))(8*word.unsigned address)))
 else Byte.x00.

Definition Related width root capacity state (memory:Mem):Prop:=
 forall address,map.get memory address=Some(bank_byte width root capacity state address).

Theorem same_bank_and_memory width root capacity before after oldmem newmem:
 read_signal after root=read_signal before root ->newmem=oldmem ->
 Related width root capacity before oldmem ->Related width root capacity after newmem.
Proof.
 intros HR HM HI;subst newmem;intro address.
 unfold bank_byte;rewrite HR;exact(HI address).
Qed.

Theorem zeroed_bank width root capacity state
 {word_ok:word.ok word}{mem_ok:map.ok Mem}:
 read_signal state root=0 ->Related width root capacity state FormalSpec.zeroed.
Proof.
 intros HZ address;rewrite FormalSpec.zeroed_access.
 unfold bank_byte;rewrite HZ;destruct(word.unsigned address <? Z.of_nat capacity);[|reflexivity].
 unfold norm;rewrite Z.land_0_l,Z.shiftr_0_l,Z.land_0_l;reflexivity.
Qed.
End Memory.
Section OriginalISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.

Theorem original_ADD_chain_memory_frame {Token:Type}(pc code:Token->Z)
 (before after:FormalSpec.State)tokens:
 List.Forall(fun token=>exists rd rs1 rs2,
 Decode.decode Decode.RV32I(code token)=Decode.IInstruction(Decode.Add rd rs1 rs2))tokens ->
 CPUGeneratedJointTemplate.EffectChain(CPUOriginalISAReference.instruction_effect pc code)before tokens after ->
 getDataMem after=getDataMem before.
Proof.
 intros HC HE;induction HE.
 - reflexivity.
 - inversion HC as[|token rest HD HT];subst.
   destruct HD as[rd[rs1[rs2 HD]]].
   pose proof(CPUOriginalADDFrontier.original_token_ADD_frontier pc code t a b rd rs1 rs2 H HD)as[_[_[_ HM]]].
   exact(eq_trans(IHHE HT)HM).
Qed.
End OriginalISA.
End CPUByteBankRelation.
Print Assumptions CPUByteBankRelation.same_bank_and_memory.
Print Assumptions CPUByteBankRelation.zeroed_bank.
Print Assumptions CPUByteBankRelation.original_ADD_chain_memory_frame.
