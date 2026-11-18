(** Operand clauses for an automatically constructed R. Oldest-first slots
    distinguish no matching writer from a matching writer not yet ready.
    This library does not assume or establish CPU token ownership. *)
From Coq Require Import ZArith List.
Require Import Ex.External.PendingRegisterScoreboard.
Import ListNotations PendingRegisterScoreboard.
Local Open Scope Z_scope.
Module CPUReadyOperand.
Section Operand.
Context {V:Type} (zero:V).
Definition Slot:=option(Z*option V).
Definition SlotRelated (slot:Slot)(write:option(Z*V)):Prop:=
 match slot,write with
 |None,None=>True
 |Some(rd,value),Some(rd',expected)=>rd=rd'/\
    match value with None=>True|Some actual=>actual=expected end
 |_,_=>False end.

(** None = no writer, Some None = youngest matching writer unavailable. *)
Fixpoint lookup rs (slots:list Slot):option(option V):=
 match slots with
 |[]=>None
 |slot::rest=>match lookup rs rest with
   |Some value=>Some value
   |None=>match slot with
     |None=>None
     |Some(rd,value)=>if rs=?rd then Some value else None end end end.
Definition LookupRelated (actual:option(option V))(expected:option V):Prop:=
 match actual with
 |None=>expected=None
 |Some None=>exists v,expected=Some v
 |Some(Some v)=>expected=Some v end.

Theorem lookup_related rs slots writes:
 Forall2 SlotRelated slots writes ->
 LookupRelated(lookup rs slots)(newest rs(concat(map stage_writes writes))).
Proof.
 intro H;induction H as[|slot write slots writes HW HT IH].
 - reflexivity.
 - cbn [lookup]. destruct(lookup rs slots)as[[value|]|]eqn:HL.
   + cbn [LookupRelated]in IH|-*.
     destruct slot as[[rd val]|],write as[[rd' exp]|];cbn [SlotRelated]in HW;try contradiction;
       cbn [map concat stage_writes app newest fst snd];now rewrite IH.
   + cbn [LookupRelated]in IH|-*. destruct IH as[value HE].
     exists value.
     destruct slot as[[rd val]|],write as[[rd' exp]|];cbn [SlotRelated]in HW;try contradiction;
       cbn [map concat stage_writes app newest fst snd];now rewrite HE.
   + cbn [LookupRelated]in IH.
     destruct slot as[[rd val]|],write as[[rd' exp]|];cbn [SlotRelated]in HW;try contradiction.
     * destruct HW as[HR HV];subst rd'.
       cbn [map concat stage_writes app newest fst snd]. rewrite IH.
       destruct(rs=?rd);[destruct val;cbn [LookupRelated]in *;[now subst|eauto]|reflexivity].
     * exact IH.
Qed.

Definition resolve (rf:Z->V) rs slots:option V:=
 if rs=?0 then Some zero else
 match lookup rs slots with None=>Some(rf rs)|Some value=>value end.

Theorem resolved_operand rf slots writes rs value:
 Forall2 SlotRelated slots writes ->rf 0=zero ->
 resolve rf rs slots=Some value ->
 overlay zero rf(concat(map stage_writes writes))rs=value.
Proof.
 intros HS Hzero HR. unfold resolve in HR. destruct(rs=?0)eqn:HZ.
 - apply Z.eqb_eq in HZ;subst rs. inversion HR;subst value.
   now apply overlay_zero.
 - apply Z.eqb_neq in HZ. rewrite newest_pending_source by exact HZ.
   pose proof(lookup_related rs slots writes HS)as HL.
   destruct(lookup rs slots)as[[v|]|];cbn [LookupRelated]in HL;try discriminate;
     rewrite HL;inversion HR;reflexivity.
Qed.

Example unavailable_youngest_blocks rf rd older:
 rd<>0 ->resolve rf rd[Some(rd,Some older);Some(rd,None)]=None.
Proof. intro H. unfold resolve;cbn [lookup].
 rewrite Z.eqb_refl. apply Z.eqb_neq in H. now rewrite H. Qed.

Example available_youngest_overrides rf rd newer:
 rd<>0 ->resolve rf rd[Some(rd,None);Some(rd,Some newer)]=Some newer.
Proof. intro H. unfold resolve;cbn [lookup].
 rewrite Z.eqb_refl. apply Z.eqb_neq in H. now rewrite H. Qed.

Example immutable_zero rf slots:resolve rf 0 slots=Some zero.
Proof. reflexivity. Qed.
End Operand.
End CPUReadyOperand.
Print Assumptions CPUReadyOperand.resolved_operand.
