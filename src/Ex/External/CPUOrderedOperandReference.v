(** Reference operand lookup from chronological register effects.
    No RTL control/age correctness is assumed to have been discharged. *)
From Coq Require Import List ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVRegisterBank
 Ex.External.CPURegisterEffectRelation Ex.RvCore.FormalSpec
 coqutil.Word.Interface coqutil.Map.Interface coqutil.Byte.
Import ListNotations ExtendedSV ExtendedSVRegisterBank CPURegisterEffectRelation.
Local Open Scope Z_scope.
Module CPUOrderedOperandReference.

(** Index is an operation position, NOT an instruction ID: an instruction may
    emit zero or several operations. Hardware tags require a separate mapping. *)
Fixpoint latest_write width (operations:list BankOperation) address : option(nat*Z) :=
 match operations with
 | []=>None
 | operation::rest=>
   match latest_write width rest address with
   | Some(index,value)=>Some(S index,value)
   | None=>match operation with
     | WriteLane target value=>if Z.eqb address target then Some(0%nat,norm width value) else None
     | ResetBank total value=>Some(0%nat,lane_read width value address)
     end
   end
 end.

Definition operand_value width base operations address :=
 match latest_write width operations address with
 | Some(_,value)=>value | None=>base address end.

Theorem ordered_effects_lookup width operations base address :
 operation_effects width base operations address =
 operand_value width base operations address.
Proof.
 revert base;induction operations as[|operation rest IH];intro base;[reflexivity|].
 cbn[operation_effects];rewrite IH;unfold operand_value;cbn[latest_write].
 destruct(latest_write width rest address)as[[index value]|];[reflexivity|].
 destruct operation as[target value|total value].
 - unfold operation_effect,abstract_write;destruct(Z.eqb address target);reflexivity.
 - reflexivity.
Qed.

Theorem selected_write_value width operations base address position value :
 latest_write width operations address=Some(position,value) ->
 operation_effects width base operations address=value.
Proof. intro H;rewrite ordered_effects_lookup;unfold operand_value;now rewrite H. Qed.

Theorem no_write_reads_base width operations base address :
 latest_write width operations address=None ->
 operation_effects width base operations address=base address.
Proof. intro H;rewrite ordered_effects_lookup;unfold operand_value;now rewrite H. Qed.

Definition architectural_operand base operations address :=
 if Z.eqb address 0 then 0 else operand_value 32 base operations address.

Theorem projected_effects_lookup operations base address :
 project_x0(operation_effects32 base operations)address=
 architectural_operand base operations address.
Proof.
 unfold project_x0,architectural_operand,operation_effects32.
 destruct(Z.eqb address 0);[reflexivity|apply ordered_effects_lookup].
Qed.

Theorem reference_operand_from_effects operations before after address :
 (forall i,0<=i<32 ->after i=project_x0(operation_effects32 before operations)i) ->
 0<=address<32 ->after address=architectural_operand before operations address.
Proof. intros H HA;rewrite H by exact HA;apply projected_effects_lookup. Qed.

Section OriginalISA.
Context {word:coqutil.Word.Interface.word 32}
 {Registers:map.map Z word}{Mem:map.map word byte}.
Theorem original_isa_operand (before after:FormalSpec.State) operations address :
 ISAProjectedRegisterEffects before after operations ->0<=address<32 ->
 ISAView after address=architectural_operand(ISAView before)operations address.
Proof. apply reference_operand_from_effects. Qed.
End OriginalISA.

Example youngest_same_address : latest_write 32 [WriteLane 1 4;WriteLane 2 8;WriteLane 1 9] 1=Some(2%nat,9).
Proof. reflexivity. Qed.
Example older_result_is_not_fresh : architectural_operand(fun _=>0)[WriteLane 1 4;WriteLane 1 9]1<>4.
Proof. discriminate. Qed.
Example zero_register_is_not_forwarded : architectural_operand(fun _=>7)[WriteLane 0 9]0=0.
Proof. reflexivity. Qed.
Example no_writer_uses_register_file : architectural_operand(fun _=>7)[WriteLane 2 9]1=7.
Proof. reflexivity. Qed.
End CPUOrderedOperandReference.
Print Assumptions CPUOrderedOperandReference.ordered_effects_lookup.
Print Assumptions CPUOrderedOperandReference.reference_operand_from_effects.
Print Assumptions CPUOrderedOperandReference.original_isa_operand.
