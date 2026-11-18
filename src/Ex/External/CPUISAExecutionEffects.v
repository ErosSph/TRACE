(** Extract effects from the ORIGINAL ISA execution, without a DUT invariant
    or a separately defined expected post-state. *)
From Coq Require Import ZArith List.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine
 Ex.External.CPUISARegisterUpdate Ex.External.CPURegisterEffectRelation
 Ex.External.CV32E40PReq41Instruction
 Ex.External.CPUISAOwnedEffects Ex.External.CPUOriginalISAReference
 coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Byte
 riscv.Utility.Monads riscv.Utility.Utility riscv.Spec.ExecuteI.
Import CPUISARegisterUpdate CPURegisterEffectRelation CV32E40PReq41Instruction
 CPUISAOwnedEffects CPUOriginalISAReference.
Local Open Scope Z_scope.
Module CPUISAExecutionEffects.

Lemma bind_success {S X Y:Type} (first:OState S X) (next:X->OState S Y)
 before value after:
 Bind first next before=(Some value,after) ->
 exists x middle,first before=(Some x,middle) /\ next x middle=(Some value,after).
Proof.
 cbn[Bind OState_Monad];destruct(first before)as[[x|]middle]eqn:HE;
 [intro H;exists x,middle;auto|discriminate].
Qed.

Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.

Lemma original_read_preserves (before after:FormalSpec.State) rs value:
 Machine.getRegister rs before=(Some value,after) -> after=before.
Proof.
 unfold Machine.getRegister;cbn[IsRiscvProgram].
 destruct(Z.eq_dec rs 0);[intro H;inversion H;reflexivity|].
 destruct((0<?rs)&&(rs<?32))%bool;[|discriminate].
 cbn[Bind Return OState_Monad OStateOperations.get].
 destruct(map.get(getRegs before)rs);intro H;inversion H;reflexivity.
Qed.

Lemma original_pc_read_preserves (before after:FormalSpec.State) value:
 Machine.getPC before=(Some value,after) -> after=before.
Proof. intro H;inversion H;reflexivity. Qed.

(** This recognizer restricts the theorem's domain only. Arithmetic result
    expressions are always obtained by reducing the original ExecuteI. *)
Definition data_operation i:bool:=match i with
 | Decode.Lui _ _ | Decode.Auipc _ _
 | Decode.Addi _ _ _ | Decode.Slti _ _ _ | Decode.Sltiu _ _ _
 | Decode.Xori _ _ _ | Decode.Ori _ _ _ | Decode.Andi _ _ _
 | Decode.Slli _ _ _ | Decode.Srli _ _ _ | Decode.Srai _ _ _
 | Decode.Add _ _ _ | Decode.Sub _ _ _ | Decode.Sll _ _ _
 | Decode.Slt _ _ _ | Decode.Sltu _ _ _ | Decode.Xor _ _ _
 | Decode.Srl _ _ _ | Decode.Sra _ _ _ | Decode.Or _ _ _
 | Decode.And _ _ _ =>true | _=>false end.

Ltac split_original_execution :=
 repeat match goal with
 | H: Bind _ _ _=(Some _,_) |- _ =>
   apply bind_success in H;
   let x:=fresh "value" in let s:=fresh "middle" in
   let HX:=fresh "primitive" in destruct H as[x [s [HX H]]]
 end;
 repeat match goal with
 | H:Machine.getRegister ?rs ?before=(Some ?v,?after) |- _ =>
   first [constr_eq before after;fail 1|idtac];
   let HE:=fresh "same_state" in
   pose proof(original_read_preserves before after rs v H)as HE;subst after
 | H:Machine.getPC ?before=(Some ?v,?after) |- _ =>
   first [constr_eq before after;fail 1|idtac];
   let HE:=fresh "same_state" in
   pose proof(original_pc_read_preserves before after v H)as HE;subst after
 end.

Theorem original_data_effect (before after:FormalSpec.State) i:
 data_operation i=true -> ExecuteI.execute i before=(Some tt,after) ->
 exists operations, ISAProjectedRegisterEffects before after operations.
Proof.
 destruct i;cbn[data_operation];try discriminate;
 intros _ H;cbn[ExecuteI.execute]in H;
 split_original_execution;extract_register_operations.
Qed.

(** Every binary register instruction with this actual monadic shape shares
    the extraction proof. Its operation f is supplied by ExecuteI, not RTL. *)
Theorem binary_register_effect (before after:FormalSpec.State) rd rs1 rs2
 (f:word->word->word):
 Bind (Machine.getRegister rs1) (fun x=>
 Bind (Machine.getRegister rs2) (fun y=>Machine.setRegister rd(f x y))) before
   =(Some tt,after) ->
 exists x y,
 Machine.getRegister rs1 before=(Some x,before) /\
 Machine.getRegister rs2 before=(Some y,before) /\
 ISAProjectedRegisterEffects before after(register_operations rd(f x y)).
Proof.
 intro H;apply bind_success in H;destruct H as[x [s1 [HX H]]].
 pose proof(original_read_preserves before s1 rs1 x HX);subst s1.
 apply bind_success in H;destruct H as[y [s2 [HY H]]].
 pose proof(original_read_preserves before s2 rs2 y HY);subst s2.
 exists x,y;split;[exact HX|];split;[exact HY|].
 now apply original_set_register.
Qed.

Theorem original_add_effect (before after:FormalSpec.State) rd rs1 rs2:
 ExecuteI.execute(Decode.Add rd rs1 rs2)before=(Some tt,after) ->
 exists x y,
 Machine.getRegister rs1 before=(Some x,before) /\
 Machine.getRegister rs2 before=(Some y,before) /\
 ISAProjectedRegisterEffects before after(register_operations rd(Utility.add x y)).
Proof. apply binary_register_effect. Qed.

Theorem original_sub_effect (before after:FormalSpec.State) rd rs1 rs2:
 ExecuteI.execute(Decode.Sub rd rs1 rs2)before=(Some tt,after) ->
 exists x y,
 Machine.getRegister rs1 before=(Some x,before) /\
 Machine.getRegister rs2 before=(Some y,before) /\
 ISAProjectedRegisterEffects before after(register_operations rd(Utility.sub x y)).
Proof. apply binary_register_effect. Qed.

Lemma end_cycle_register_frame (before after:FormalSpec.State):
 Machine.endCycleNormal before=(Some tt,after) ->getRegs after=getRegs before.
Proof. destruct before;intro H;inversion H;reflexivity. Qed.

Theorem run1_data_effect {mem_ok:map.ok Mem} (before after:FormalSpec.State) i:
 CurrentInstruction before i ->data_operation i=true ->
 FormalSpec.run1 before=(Some tt,after) ->
 exists operations, ISAProjectedRegisterEffects before after operations.
Proof.
 intros HC HD HR;rewrite(run1_current_instruction before i HC)in HR.
 apply bind_success in HR;destruct HR as[[] [middle [HE HEND]]].
 change(ExecuteI.execute i before=(Some tt,middle))in HE.
 destruct(original_data_effect before middle i HD HE)as[operations HO].
 exists operations;intros address HA.
 unfold ISAView;rewrite(end_cycle_register_frame middle after HEND).
 exact(HO address HA).
Qed.

Theorem prepend_original_data_batch {mem_ok:map.ok Mem}{Token:Type}
 (token_pc token_word:Token->Z) token before middle final i rest:
 CurrentInstruction before i ->data_operation i=true ->
 instruction_effect token_pc token_word token before=Some middle ->
 CertifiedBatches token_pc token_word middle rest final ->
 exists operations,CertifiedBatches token_pc token_word before
   ((token,operations)::rest) final.
Proof.
 intros HC HD HS HT.
 destruct(instruction_effect_sound token_pc token_word token before middle HS)
   as[_ [_ HR]].
 destruct(run1_data_effect before middle i HC HD HR)as[operations HO].
 exists operations;econstructor;eassumption.
Qed.
End ISA.
End CPUISAExecutionEffects.
Print Assumptions CPUISAExecutionEffects.original_add_effect.
Print Assumptions CPUISAExecutionEffects.original_sub_effect.
Print Assumptions CPUISAExecutionEffects.original_data_effect.
Print Assumptions CPUISAExecutionEffects.run1_data_effect.
Print Assumptions CPUISAExecutionEffects.prepend_original_data_batch.
