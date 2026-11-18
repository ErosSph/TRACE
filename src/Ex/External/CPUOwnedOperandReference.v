(** Chronological per-instruction effects retain their owning token.
    Empty and multi-write batches are supported; no instruction/operation
    index equality is assumed. ISA batch validity remains an input obligation. *)
From Coq Require Import List ZArith.
Require Import Lang.ExtendedSVRegisterBank Ex.External.CPURegisterEffectRelation
 Ex.External.CPUOrderedOperandReference.
Import ListNotations ExtendedSVRegisterBank CPURegisterEffectRelation CPUOrderedOperandReference.
Module CPUOwnedOperandReference.
Section Tokens.
Context {Token:Type}.
Inductive OwnedWrite := WriteOf(owner:Token)(operation_index:nat)(value:Z).
Fixpoint latest_owner width (batches:list(Token*list BankOperation)) address :=
 match batches with
 | []=>None
 | (token,operations)::rest=>
   match latest_owner width rest address with
   | Some found=>Some found
   | None=>match latest_write width operations address with
     | Some(index,value)=>Some(WriteOf token index value)|None=>None end
   end
 end.
Definition owner_value width base batches address :=
 match latest_owner width batches address with
 | Some(WriteOf _ _ value)=>value|None=>base address end.

Theorem flatten_preserves_operand width batches base address :
 operation_effects width base(flat_map (@snd Token (list BankOperation))batches)address=
 owner_value width base batches address.
Proof.
 revert base;induction batches as[|[token operations]rest IH];intro base;[reflexivity|].
 cbn[flat_map snd];rewrite operations_append,IH.
 unfold owner_value;cbn[latest_owner].
 destruct(latest_owner width rest address)as[[owner index value]|];[reflexivity|].
 rewrite ordered_effects_lookup;unfold operand_value.
 destruct(latest_write width operations address)as[[index value]|];reflexivity.
Qed.

Theorem selected_owner_origin width batches address owner index value :
 latest_owner width batches address=Some(WriteOf owner index value) ->
 exists operations,In(owner,operations)batches /\
 latest_write width operations address=Some(index,value).
Proof.
 induction batches as[|[token operations]rest IH];[discriminate|].
 cbn[latest_owner];destruct(latest_owner width rest address)as[found|]eqn:HR.
 - intro HE;destruct(IH HE)as[ops [HI HW]];exists ops;split;[now right|exact HW].
 - destruct(latest_write width operations address)as[[i v]|]eqn:HW;[|discriminate].
   intro HE;inversion HE;subst;exists operations;split;[now left|exact HW].
Qed.

Theorem selected_owner_value width batches base address owner index value :
 latest_owner width batches address=Some(WriteOf owner index value) ->
 operation_effects width base(flat_map (@snd Token (list BankOperation))batches)address=value.
Proof. intro H;rewrite flatten_preserves_operand;unfold owner_value;now rewrite H. Qed.
End Tokens.

Example empty_instruction_does_not_shift_owner :
 latest_owner 32 [(10%nat,[WriteLane 1 4]);(11%nat,[]);(12%nat,[WriteLane 2 8])] 1=
 Some(WriteOf 10%nat 0%nat 4%Z).
Proof. reflexivity. Qed.
Example multiwrite_keeps_local_position :
 latest_owner 32 [(10%nat,[]);(12%nat,[WriteLane 1 3;WriteLane 1 9])] 1=
 Some(WriteOf 12%nat 1%nat 9%Z).
Proof. reflexivity. Qed.
End CPUOwnedOperandReference.
Print Assumptions CPUOwnedOperandReference.flatten_preserves_operand.
Print Assumptions CPUOwnedOperandReference.selected_owner_origin.
