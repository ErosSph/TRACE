(** A two-producer forwarding template, ordered oldest then youngest.
    Mapping actual RTL fields and token age to this template is a separate
    checked obligation. An unavailable youngest match blocks consumption. *)
From Coq Require Import ZArith List Bool.
Require Import Ex.External.CPUReadyOperand Ex.External.CPUISAReadyBatches
 Ex.External.CPUISAOwnedEffects Ex.External.CPURegisterEffectRelation
 Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Map.Interface
 coqutil.Word.Bitwidth coqutil.Byte.
Import ListNotations CPUReadyOperand CPUISAReadyBatches CPUISAOwnedEffects CPURegisterEffectRelation.
Local Open Scope Z_scope.
Module CPUTwoStageReadySelection.

Definition eligible (write:bool)(rd address:Z):=write && negb(rd=?0) && (address=?rd).
Definition slot (write:bool)(rd:Z)(ready:bool)(value:Z):@Slot Z:=
 if write && negb(rd=?0) then Some(rd,if ready then Some value else None)else None.
Definition slots (ow:bool)(od:Z)(ol:bool)(ov om:Z)(yw:bool)(yd:Z)(yl:bool)(yv:Z) :=
 [slot ow od true(if ol then om else ov);slot yw yd(negb yl)yv].
Definition operand (physical:Z->Z)(address:Z)(ow:bool)(od:Z)(ol:bool)(ov om:Z)(yw:bool)(yd:Z)(yl:bool)(yv:Z) :=
 if eligible yw yd address && negb yl then yv else
 if eligible ow od address && negb ol then ov else
 if eligible ow od address && ol then om else physical address.

Definition selected_code ow od ol yw yd yl address:Z:=
 if eligible yw yd address && negb yl then 1 else
 if eligible ow od address && negb ol then 2 else
 if eligible ow od address && ol then 3 else 0.

Lemma eligible_zero write rd:eligible write rd 0=false.
Proof. unfold eligible;rewrite(Z.eqb_sym 0 rd);destruct write,(rd=?0);reflexivity. Qed.

Lemma single_lookup address write rd ready value:
 lookup address[slot write rd ready value]=
 if eligible write rd address then Some(if ready then Some value else None)else None.
Proof. unfold slot,eligible;destruct write,(rd=?0);cbn;destruct(address=?rd);reflexivity. Qed.

Lemma pair_lookup address (old young:@Slot Z):
 lookup address[old;young]=match lookup address[young]with
 |Some value=>Some value|None=>lookup address[old]end.
Proof. reflexivity. Qed.

Theorem admitted_selection physical address ow od ol ov om yw yd yl yv:
 physical 0=0 ->(eligible yw yd address && yl)=false ->
 resolve 0 physical address(slots ow od ol ov om yw yd yl yv)=
 Some(operand physical address ow od ol ov om yw yd yl yv).
Proof.
 intros Hzero Hready;unfold resolve;destruct(address=?0)eqn:HZ.
 - apply Z.eqb_eq in HZ;subst address;unfold operand;rewrite !eligible_zero;cbn;now rewrite Hzero.
 - unfold slots;rewrite pair_lookup,!single_lookup;unfold operand.
   destruct(eligible yw yd address),yl,(eligible ow od address),ol;
   cbn in Hready|-*;try discriminate;reflexivity.
Qed.

Section OriginalISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}{word_ok:word.ok word}{Token:Type}.
Theorem selected_operand_matches_original_read (token_pc token_word:Token->Z)
 initial batches before after address value physical ow od ol ov om yw yd yl yv:
 CertifiedBatches token_pc token_word initial batches before ->
 RegisterRelated physical initial ->0<=address<32 ->
 Machine.getRegister address before=(Some value,after) ->
 Forall2 SlotRelated(slots ow od ol ov om yw yd yl yv)(batch_writes 32 address batches) ->
 physical 0=0 ->(eligible yw yd address && yl)=false ->
 operand physical address ow od ol ov om yw yd yl yv=word.unsigned value.
Proof.
 intros HC HR HA Hread HS Hzero Hready.
 exact(actual_ready_selector_matches_read token_pc token_word initial batches before after address value
 physical _ _ HC HR HA Hread HS(admitted_selection physical address ow od ol ov om yw yd yl yv Hzero Hready)).
Qed.
End OriginalISA.
End CPUTwoStageReadySelection.
Print Assumptions CPUTwoStageReadySelection.admitted_selection.
Print Assumptions CPUTwoStageReadySelection.selected_operand_matches_original_read.
