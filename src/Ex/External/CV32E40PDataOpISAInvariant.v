(** Arbitrary-length ISA execution for mixed data-op ROMs.
    This file makes NO CPU progress or refinement claim. *)
From Coq Require Import ZArith List Lia.
Require Import Ex.External.CV32E40PDataOpProgramScope
 Ex.External.CV32E40PDataOpExecution Ex.External.CV32E40PReq41Instruction
 Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PAddiNopISAInvariant.
Require Import Ex.RvCore.FormalSpec riscv.Proofs.VerifyDecode.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte.
Import CV32E40PDataOpProgramScope CV32E40PDataOpExecution CV32E40PReq41Instruction
 CV32E40PReq40StateRel CV32E40PAddiNopISAInvariant.
Local Open Scope Z_scope.
Module CV32E40PDataOpISAInvariant.
 Lemma decoded_operands_legal code i : DataOp21 i ->
   Decode.decode Decode.RV32I code = Decode.IInstruction i -> LegalOperands i.
 Proof.
   intros HD HE.
   destruct (verify_decode Decode.RV32I code eq_refl) as [HV|HB]; [rewrite HE in HV|congruence].
   destruct i; cbn [DataOp21 dataop21b] in HD; try discriminate.
   all: cbv [verify respects_bounds apply_InstructionMapper Verifier
     map_U map_I map_I_shift_66 map_R verify_U verify_I verify_I_shift_66 verify_R
     bitwidth verify_iset] in HV.
   all: unfold LegalOperands; cbn [destination_register source_registers];
     repeat constructor; unfold legal_reg; intuition lia.
 Qed.
 Section ISA.
 Context {word : Interface.word 32} {BW : Bitwidth 32}.
 Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
 Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.
 Theorem current_dataop_run1_exact (s : FormalSpec.State) i :
   DataOp21 i -> CurrentInstruction s i ->
   FormalSpec.run1 s = (Some tt, dataop_post s i).
 Proof.
   intros HD HC. apply run1_exact; auto.
   destruct HC as [_ [bytes [_ HE]]]. eapply decoded_operands_legal; eauto.
 Qed.
 Theorem mixed_program_step image (s : FormalSpec.State) :
   DataOpProgram image -> ISAInvariant image s ->
   exists i, DataOp21 i /\ CurrentInstruction s i /\
     FormalSpec.run1 s = (Some tt, dataop_post s i) /\
     ISAInvariant image (dataop_post s i).
 Proof.
   intros HP HS. destruct (scoped_current_instruction image s HP HS) as (i & HD & HC).
   assert (HL : LegalOperands i).
   { destruct HC as [_ [bytes [_ HE]]]. eapply decoded_operands_legal; eauto. }
   pose proof (current_dataop_run1_exact s i HD HC) as HE.
   destruct (run1_preserves_shape image s i HD HL HC HS) as (s' & HR & HI & _).
   rewrite HE in HR. inversion HR; subst.
   exists i. auto.
 Qed.
 Theorem arbitrary_finite_mixed_isa_progress image s n :
   DataOpProgram image -> ISAInvariant image s ->
   exists s', ISARuns n s s' /\ ISAInvariant image s' /\
     getDataMem s' = getDataMem s.
 Proof.
   intros HP. induction n as [|n IH] in s |- *; intros HS.
   - exists s. split; [constructor|auto].
   - destruct (mixed_program_step image s HP HS) as (i & HD & HC & HR & HI).
     destruct (IH (dataop_post s i) HI) as (s' & Hsteps & Hfinal & HM).
     exists s'. split; [econstructor; eauto|]. split; [exact Hfinal|exact HM].
 Qed.
 End ISA.
 Print Assumptions mixed_program_step.
 Print Assumptions arbitrary_finite_mixed_isa_progress.
End CV32E40PDataOpISAInvariant.
