(** Connect ready/unready hardware slots to original ISA effect batches.
    Slots are oldest first. Their correspondence and the actual selector
    equation remain hardware obligations, not assumed reachable invariants. *)
From Coq Require Import List ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVRegisterBank
 Ex.External.CPUReadyOperand Ex.External.PendingRegisterScoreboard
 Ex.External.CPUOrderedOperandReference Ex.External.CPUOwnedOperandReference
 Ex.External.CPUISAValueRequirements Ex.External.CPUISAOperandValue
 Ex.External.CPUISAOwnedEffects Ex.External.CPURegisterEffectRelation
 Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte.
Import ListNotations ExtendedSV ExtendedSVRegisterBank CPUReadyOperand
 PendingRegisterScoreboard CPUOrderedOperandReference CPUOwnedOperandReference
 CPUISAValueRequirements CPUISAOperandValue CPUISAOwnedEffects CPURegisterEffectRelation.
Local Open Scope Z_scope.
Module CPUISAReadyBatches.

(** ResetBank is not discarded: for this particular source query it writes
    the queried lane. This is a reference conversion, not a hardware slot map. *)
Definition operation_write width address (op:BankOperation):option(Z*Z):=
 match op with
 |WriteLane rd value=>Some(rd,norm width value)
 |ResetBank total value=>Some(address,lane_read width value address)
 end.
Definition batch_writes {Token:Type} width address
 (batches:list(Token*list BankOperation)):=
 map(operation_write width address)(flat_map snd batches).

Lemma operations_newest width address operations:
 newest address(concat(map stage_writes(map(operation_write width address)operations)))=
 option_map snd(latest_write width operations address).
Proof.
 induction operations as[|op rest IH];[reflexivity|].
 destruct op as[rd data|total data];cbn[map concat operation_write stage_writes app newest latest_write fst snd];
 rewrite IH;destruct(latest_write width rest address)as[[position value]|];
 cbn[option_map snd];try reflexivity.
 - destruct(address=?rd);reflexivity.
 - now rewrite Z.eqb_refl.
Qed.

Lemma batches_newest {Token:Type} width address (batches:list(Token*list BankOperation)):
 newest address(concat(map stage_writes(batch_writes width address batches)))=
 option_map(fun w=>match w with WriteOf _ _ v=>v end)(latest_owner width batches address).
Proof.
 pose proof(flatten_preserves_operand width batches (fun _=>0) address) as H0.
 pose proof(flatten_preserves_operand width batches (fun _=>1) address) as H1.
 unfold batch_writes;rewrite operations_newest.
 rewrite ordered_effects_lookup in H0,H1.
 unfold operand_value,owner_value in H0,H1.
 destruct(latest_write width(flat_map snd batches)address)as[[index value]|];
 destruct(latest_owner width batches address)as[[owner index' value']|];
 cbn[option_map snd];congruence.
Qed.

Theorem ready_slots_select_latest {Token:Type} physical
 (batches:list(Token*list BankOperation)) address slots observed:
 Forall2 SlotRelated slots(batch_writes 32 address batches)->
 resolve 0 physical address slots=Some observed ->
 observed=selected_value physical batches address.
Proof.
 intros HS HR. unfold resolve in HR;unfold selected_value.
 destruct(address=?0);[now inversion HR|].
 pose proof(lookup_related address slots _ HS)as HL.
 rewrite batches_newest in HL.
 destruct(lookup address slots)as[[v|]|];cbn[LookupRelated]in HL;try discriminate.
 - destruct(latest_owner 32 batches address)as[[owner index value]|];
   cbn[option_map]in HL;inversion HL;now inversion HR.
 - destruct(latest_owner 32 batches address)as[[owner index value]|];
   cbn[option_map]in HL;[discriminate|now inversion HR].
Qed.

Section OriginalRead.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}{word_ok:word.ok word}{Token:Type}.
Theorem actual_ready_selector_matches_read (token_pc token_word:Token->Z)
 initial batches before after address value physical slots observed:
 CertifiedBatches token_pc token_word initial batches before ->
 RegisterRelated physical initial ->0<=address<32 ->
 Machine.getRegister address before=(Some value,after) ->
 Forall2 SlotRelated slots(batch_writes 32 address batches) ->
 resolve 0 physical address slots=Some observed ->
 observed=word.unsigned value.
Proof.
 intros HC HP HA HR HS HE.
 exact(selected_source_matches_read token_pc token_word initial batches before
   after address value physical observed HC HP HA HR
   (ready_slots_select_latest physical batches address slots observed HS HE)).
Qed.
End OriginalRead.
End CPUISAReadyBatches.
Print Assumptions CPUISAReadyBatches.ready_slots_select_latest.
Print Assumptions CPUISAReadyBatches.actual_ready_selector_matches_read.
