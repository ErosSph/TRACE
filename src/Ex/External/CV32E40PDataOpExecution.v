(** Symbolic ISA execution, not a CPU pipeline preservation theorem. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CV32E40PDataOpProgramScope
 Ex.External.CV32E40PReq41Instruction Ex.External.CV32E40PReq40StateRel
 Ex.External.CV32E40PAddiNopISAInvariant.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine.
Require Import riscv.Spec.Execute riscv.Spec.ExecuteI riscv.Utility.Monads.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte.
Import ListNotations CV32E40PDataOpProgramScope CV32E40PReq41Instruction
 CV32E40PReq40StateRel CV32E40PAddiNopISAInvariant.
Local Open Scope Z_scope.
Module CV32E40PDataOpExecution.
 Definition LegalOperands i :=
   (match destination_register i with Some rd => legal_reg rd | None => True end) /\
   Forall legal_reg (source_registers i).
 Section ISA.
 Context {word : Interface.word 32} {BW : Bitwidth 32}.
 Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
 Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.

 (** Pure ISA result; never supplied by a CPU certificate. *)
 Definition result_word (s : FormalSpec.State) i : word :=
   let reg := formal_register_word s in
   match i with
   | Decode.Lui _ imm => word.of_Z imm
   | Decode.Auipc _ imm => word.add (word.of_Z imm) (getPc s)
   | Decode.Addi _ rs imm => word.add (reg rs) (word.of_Z imm)
   | Decode.Slti _ rs imm => if word.lts (reg rs) (word.of_Z imm) then word.of_Z 1 else word.of_Z 0
   | Decode.Sltiu _ rs imm => if word.ltu (reg rs) (word.of_Z imm) then word.of_Z 1 else word.of_Z 0
   | Decode.Xori _ rs imm => word.xor (reg rs) (word.of_Z imm)
   | Decode.Ori _ rs imm => word.or (reg rs) (word.of_Z imm)
   | Decode.Andi _ rs imm => word.and (reg rs) (word.of_Z imm)
   | Decode.Slli _ rs sh => Utility.sll (reg rs) sh
   | Decode.Srli _ rs sh => Utility.srl (reg rs) sh
   | Decode.Srai _ rs sh => Utility.sra (reg rs) sh
   | Decode.Add _ a b => word.add (reg a) (reg b)
   | Decode.Sub _ a b => word.sub (reg a) (reg b)
   | Decode.Sll _ a b => Utility.sll (reg a) (Utility.regToShamt (reg b))
   | Decode.Slt _ a b => if word.lts (reg a) (reg b) then word.of_Z 1 else word.of_Z 0
   | Decode.Sltu _ a b => if word.ltu (reg a) (reg b) then word.of_Z 1 else word.of_Z 0
   | Decode.Xor _ a b => word.xor (reg a) (reg b)
   | Decode.Srl _ a b => Utility.srl (reg a) (Utility.regToShamt (reg b))
   | Decode.Sra _ a b => Utility.sra (reg a) (Utility.regToShamt (reg b))
   | Decode.Or _ a b => word.or (reg a) (reg b)
   | Decode.And _ a b => word.and (reg a) (reg b)
   | _ => word.of_Z 0
   end.
 Definition dataop_post (s : FormalSpec.State) i : FormalSpec.State :=
   {| getRegs := match destination_register i with
       | Some rd => if Z.eq_dec rd 0 then getRegs s else map.put (getRegs s) rd (result_word s i)
       | None => getRegs s end;
      getPc := getNextPc s; getNextPc := word.add (getNextPc s) (word.of_Z 4);
      getInstMem := getInstMem s; getDataMem := getDataMem s |}.

 Theorem execute_exact (s : FormalSpec.State) i :
   DataOp21 i -> LegalOperands i -> ISAStep s i (dataop_post s i).
 Proof.
   intros HD HL. destruct s as [regs pc npc imem dmem].
   destruct i; cbn [DataOp21 dataop21b] in HD; try discriminate.
   all: unfold LegalOperands in HL;
     cbn [destination_register source_registers] in HL;
     destruct HL as [HR HS];
     repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end.
   all: unfold ISAStep; cbn [Execute.execute ExecuteI.execute];
     unfold Machine.getRegister, Machine.setRegister, Machine.getPC, Machine.endCycleNormal;
     cbn [IsRiscvProgram]; unfold dataop_post, result_word, formal_register_word;
     cbn [destination_register getRegs getPc getNextPc getInstMem getDataMem].
   all: repeat match goal with
     | |- context [Z.eq_dec ?r ?z] => destruct (Z.eq_dec r z)
     end; try contradiction.
   all: repeat match goal with
     | |- context [((0 <? ?r) && (?r <? 32))%bool] =>
       let HB := fresh "HB" in
       assert (HB : ((0 <? r) && (r <? 32))%bool = true)
         by (apply andb_true_iff; split; apply Z.ltb_lt; unfold legal_reg in *; cbn in *; lia);
       rewrite HB
     end.
   all: cbn [Bind Return OState_Monad OStateOperations.get OStateOperations.put
     update withRegs withPc withNextPc getRegs getPc getNextPc getInstMem getDataMem].
   all: repeat match goal with |- context [map.get ?rsmap ?r] =>
     let E := fresh "Eget" in destruct (map.get rsmap r) eqn:E;
     cbn [Bind Return OState_Monad OStateOperations.get OStateOperations.put
       update withRegs withPc withNextPc getRegs getPc getNextPc getInstMem getDataMem];
     repeat match goal with H : map.get _ _ = _ |- _ => progress rewrite H end
     end.
   all: reflexivity.
 Qed.

 Theorem execute_success_frame (s : FormalSpec.State) i :
   DataOp21 i -> LegalOperands i ->
   exists s', ISAStep s i s' /\
     getPc s' = getNextPc s /\
     getNextPc s' = word.add (getNextPc s) (word.of_Z 4) /\
     getInstMem s' = getInstMem s /\ getDataMem s' = getDataMem s.
 Proof.
   intros HD HL. exists (dataop_post s i).
   split; [now apply execute_exact|]. repeat split; reflexivity.
 Qed.

 Theorem run1_exact s i : DataOp21 i -> LegalOperands i -> CurrentInstruction s i ->
   FormalSpec.run1 s = (Some tt, dataop_post s i).
 Proof. intros HD HL HC. eapply current_instruction_run1_step; eauto using execute_exact. Qed.

 Theorem post_register_read s i rd r : destination_register i = Some rd ->
   formal_register_word (dataop_post s i) r =
     if Z.eq_dec r 0 then word.of_Z 0 else
     if Z.eq_dec rd 0 then formal_register_word s r else
     if Z.eq_dec r rd then result_word s i else formal_register_word s r.
 Proof.
   intros Hrd. unfold formal_register_word, dataop_post. cbn [getRegs].
   rewrite Hrd. destruct (Z.eq_dec r 0); [reflexivity|].
   destruct (Z.eq_dec rd 0); [reflexivity|].
   destruct (Z.eq_dec r rd) as [->|Hne].
   - rewrite map.get_put_same. reflexivity.
   - rewrite map.get_put_diff by congruence. reflexivity.
 Qed.

 Theorem run1_preserves_shape image (s : FormalSpec.State) i :
   DataOp21 i -> LegalOperands i -> CurrentInstruction s i -> ISAInvariant image s ->
   exists s', FormalSpec.run1 s = (Some tt, s') /\ ISAInvariant image s' /\
     getInstMem s' = getInstMem s /\ getDataMem s' = getDataMem s.
 Proof.
   intros HD HL HC (HM & HA & HN).
   destruct (execute_success_frame s i HD HL) as (s' & HE & HP & HNP & HI & HMEM).
   exists s'. split; [eapply current_instruction_run1_step; eauto|].
   split; [|auto]. unfold ISAInvariant. rewrite HI, HP, HNP.
   split; [exact HM|]. split.
   - rewrite HN. apply aligned_successor. exact HA.
   - rewrite word.unsigned_add, word.unsigned_of_Z.
     change (4 mod 2^32) with 4. reflexivity.
 Qed.
 End ISA.
 Print Assumptions execute_exact.
 Print Assumptions execute_success_frame.
 Print Assumptions run1_preserves_shape.
End CV32E40PDataOpExecution.
