(** Actual ISA reads after a certified pending prefix. The physical RF need
    only describe the committed state; pending writes are resolved separately. *)
From Coq Require Import ZArith List Lia.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine
 Ex.External.PicoISARF Ex.External.CPURegisterEffectRelation
 Ex.External.CPUISAOwnedEffects Ex.External.CPUOwnedOperandReference
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Map.Interface
 coqutil.Word.Bitwidth coqutil.Byte riscv.Utility.Utility riscv.Utility.Monads.
Import CPURegisterEffectRelation CPUISAOwnedEffects CPUOwnedOperandReference.
Local Open Scope Z_scope.
Module CPUISAOperandValue.
Section Read.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}.

Lemma original_read_value (before after:FormalSpec.State) address value:
 Machine.getRegister address before=(Some value,after) ->
 word.unsigned value=ISAView before address.
Proof.
 unfold Machine.getRegister;cbn[IsRiscvProgram].
 destruct(Z.eq_dec address 0)as[HZ|HN].
 - subst address;intro H;inversion H;subst.
   change(word.unsigned(word.of_Z 0:word)=0).
   rewrite word.unsigned_of_Z;reflexivity.
 - destruct((0<?address)&&(address<?32))%bool;[|discriminate].
   cbn[Bind Return OState_Monad OStateOperations.get].
   unfold ISAView,PicoISARF.isa_value.
   assert(HZ:(address=?0)=false)by(now apply Z.eqb_neq).
   rewrite HZ;destruct(map.get(getRegs before)address)eqn:HR;
   intro H;inversion H;subst;[reflexivity|].
   change(word.unsigned(word.of_Z 0:word)=0).
   rewrite word.unsigned_of_Z;reflexivity.
Qed.

Theorem read_after_certified_prefix {Token:Type}(token_pc token_word:Token->Z)
 initial batches before after address value:
 CertifiedBatches token_pc token_word initial batches before ->
 0<=address<32 ->
 Machine.getRegister address before=(Some value,after) ->
 word.unsigned value=
 if address=?0 then 0 else owner_value 32(ISAView initial)batches address.
Proof.
 intros HC HA HR;rewrite(original_read_value before after address value HR).
 exact(batches_operand token_pc token_word initial batches before address HC HA).
Qed.

(** The generator's physical obligation is source selection, not RF equality
    with the speculative state. The empty-source branch uses committed RF. *)
Theorem selected_source_matches_read {Token:Type}(token_pc token_word:Token->Z)
 initial batches before after address value (physical:Z->Z) observed:
 CertifiedBatches token_pc token_word initial batches before ->
 RegisterRelated physical initial ->0<=address<32 ->
 Machine.getRegister address before=(Some value,after) ->
 observed=(if address=?0 then 0 else
   match latest_owner 32 batches address with
   |Some(WriteOf _ _ v)=>v|None=>physical address end) ->
 observed=word.unsigned value.
Proof.
 intros HC HP HA HR HE.
 rewrite(read_after_certified_prefix token_pc token_word initial batches
   before after address value HC HA HR),HE.
 unfold owner_value;destruct(address=?0)eqn:HZ;[reflexivity|].
 destruct(latest_owner 32 batches address)as[[owner index v]|];[reflexivity|].
 specialize(HP address HA);unfold project_x0 in HP;now rewrite HZ in HP.
Qed.
End Read.
End CPUISAOperandValue.
Print Assumptions CPUISAOperandValue.original_read_value.
Print Assumptions CPUISAOperandValue.read_after_certified_prefix.
Print Assumptions CPUISAOperandValue.selected_source_matches_read.
