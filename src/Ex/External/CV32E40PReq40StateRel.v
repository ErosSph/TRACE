(** Req40: parameterized architectural relation and ADDI run1 step.

    This file contains no CV32E40P fixture.  It gives the reusable ISA-side
    theorem and the state relation that a real next-commit RTL certificate
    must preserve.  The physical CV32E40P transition is connected in the
    companion file [CV32E40PReq40NextCommit]. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine.
Require Import Ex.External.BzeenoFormalSim.
Require Import riscv.Spec.Decode riscv.Spec.Execute riscv.Spec.ExecuteI.
Require Import riscv.Utility.Monads riscv.Utility.Utility.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Datatypes.HList.

Local Open Scope Z_scope.

Module CV32E40PReq40StateRel.

Section WithContext.
  Context {word : Interface.word 32} {BW : Bitwidth 32}.
  Context {Registers : map.map Decode.Register word}
          {Mem : map.map word byte}.
  Context {word_ok : word.ok word} {registers_ok : map.ok Registers}
          {mem_ok : map.ok Mem}.

  Definition legal_reg (r : Z) : Prop := 0 <= r < 32.
  Definition legal_addi_imm (imm : Z) : Prop := -2048 <= imm < 2048.

  Definition formal_register_word (s : FormalSpec.State) (r : Z) : word :=
    if Z.eq_dec r 0 then word.of_Z 0
    else match map.get (getRegs s) r with
         | Some w => w
         | None => word.of_Z 0
         end.

  Definition addi_result_word (s : FormalSpec.State) (rs1 imm : Z) : word :=
    word.add (formal_register_word s rs1)
      (word.of_Z imm).

  Definition addi_regs (s : FormalSpec.State) (rd rs1 imm : Z) :=
    if Z.eq_dec rd 0 then getRegs s
    else map.put (getRegs s) rd (addi_result_word s rs1 imm).

  Definition addi_isa_post (s : FormalSpec.State) (rd rs1 imm : Z)
      : FormalSpec.State :=
    {| getRegs := addi_regs s rd rs1 imm;
       getPc := getNextPc s;
       getNextPc := word.add (getNextPc s) (word.of_Z 4);
       getInstMem := getInstMem s;
       getDataMem := getDataMem s |}.

  (** [run1] fetches bytes before decoding.  Keeping the fetch tuple in the
      hypothesis avoids assuming any particular ROM representation while
      still requiring the actual FormalSpec fetch/decode path. *)
  (** A fetch/decode witness is logical evidence only; no client computes a
      byte tuple from it.  Keeping the record in [Prop] allows ROM
      correctness lemmas (which naturally return an existential proposition)
      to discharge this obligation without adding a choice axiom. *)
  Record ADDIAtPC (s : FormalSpec.State) (rd rs1 imm : Z) : Prop := {
    addi_pc_aligned : word.unsigned (getPc s) mod 4 = 0;
    addi_fetch_bytes : tuple byte 4;
    addi_fetch_ok :
      Memory.load_bytes 4 (getInstMem s) (getPc s) = Some addi_fetch_bytes;
    addi_decode_ok :
      Decode.decode Decode.RV32I (LittleEndian.combine 4 addi_fetch_bytes) =
        Decode.IInstruction (Decode.Addi rd rs1 imm)
  }.

  Theorem run1_addi_exact : forall s rd rs1 imm,
      legal_reg rd -> legal_reg rs1 -> legal_addi_imm imm ->
      ADDIAtPC s rd rs1 imm ->
      FormalSpec.run1 s = (Some tt, addi_isa_post s rd rs1 imm).
  Proof.
    intros [regs pc nextpc imem dmem] rd rs1 imm Hrd Hrs Himm Hfetch.
    destruct Hfetch as [Halign bytes Hload Hdecode].
    cbn [getPc getInstMem] in Halign, Hload.
    change (Decode.decode Decode.RV32I
      (LittleEndian.combine_deprecated 4 bytes) =
      Decode.IInstruction (Decode.Addi rd rs1 imm)) in Hdecode.
    unfold FormalSpec.run1.
    cbn [Monads.Bind Monads.OState_Monad].
    unfold Machine.getPC. cbn [IsRiscvProgram].
    cbn [Monads.Bind Monads.Return Monads.OState_Monad
         Monads.OStateOperations.get].
    unfold Machine.loadWord, Machine.loadN, Machine.assert_aligned,
      Machine.fail_if_None.
    cbn [IsRiscvProgram].
    unfold loadN, assert_aligned, fail_if_None.
    cbn [getPc getInstMem].
    assert (HAL : negb (reg_eqb (remu pc (ZToReg 4)) (ZToReg 0)) = false).
    { change (negb (word.eqb (word.modu pc (word.of_Z 4))
                    (word.of_Z 0)) = false).
      rewrite word.unsigned_eqb.
      rewrite word.unsigned_modu.
      2: { rewrite word.unsigned_of_Z. unfold word.wrap.
           rewrite Z.mod_small by lia. lia. }
      rewrite !word.unsigned_of_Z. unfold word.wrap.
      change (4 mod 2 ^ 32) with 4.
      change (0 mod 2 ^ 32) with 0.
      rewrite Halign. reflexivity. }
    rewrite HAL.
    cbn [Monads.Bind Monads.Return Monads.OState_Monad
         Monads.OStateOperations.get].
    cbn [getInstMem]. rewrite Hload. cbn.
    setoid_rewrite Hdecode.
    cbn [Execute.execute]. unfold ExecuteI.execute.
    cbn [Monads.Bind Monads.Return Monads.OState_Monad
         Monads.OStateOperations.get Monads.OStateOperations.put
         Machine.getRegister Machine.setRegister Machine.endCycleNormal].
    cbn [IsRiscvProgram].
    unfold Machine.getRegister, Machine.setRegister.
    cbn [IsRiscvProgram].
    unfold legal_reg in Hrd, Hrs.
    destruct (Z.eq_dec rs1 0) as [Hrs0 | Hrs0].
    - subst rs1. cbn.
      destruct (Z.eq_dec rd 0) as [Hrd0 | Hrd0].
      + subst rd. cbn [Monads.Bind Monads.Return Monads.OState_Monad
                       Monads.OStateOperations.get Monads.OStateOperations.put
                       update withPc withNextPc addi_isa_post addi_regs
                       withRegs getRegs getPc getNextPc getInstMem getDataMem
                       addi_result_word formal_register_word].
        reflexivity.
      + assert (HRD : ((0 <? rd) && (rd <? 32))%bool = true).
        { apply andb_true_iff. split; apply Z.ltb_lt; lia. }
        rewrite HRD.
        cbn [Monads.Bind Monads.Return Monads.OState_Monad
             Monads.OStateOperations.get Monads.OStateOperations.put
             update withPc withNextPc addi_isa_post addi_regs
             withRegs getRegs getPc getNextPc getInstMem getDataMem
             addi_result_word formal_register_word].
        destruct (Z.eq_dec rd 0); [contradiction|].
        cbn [Monads.OStateOperations.put withRegs withPc withNextPc
             getRegs getPc getNextPc getInstMem getDataMem].
        unfold Monads.OStateOperations.put. cbn [Monads.OState_Monad].
        unfold addi_isa_post, addi_regs, addi_result_word,
          formal_register_word. cbn [getRegs getNextPc getInstMem getDataMem].
        destruct (Z.eq_dec rd 0); [contradiction|].
        destruct (Z.eq_dec 0 0); [reflexivity|contradiction].
    - assert (HRS : ((0 <? rs1) && (rs1 <? 32))%bool = true).
      { apply andb_true_iff. split; apply Z.ltb_lt; lia. }
      rewrite HRS.
      cbn [Monads.Bind Monads.Return Monads.OState_Monad
           Monads.OStateOperations.get Monads.OStateOperations.put].
      destruct (map.get regs rs1) as [rs1w |] eqn:Hget; cbn.
      + destruct (Z.eq_dec rd 0) as [Hrd0 | Hrd0].
        * subst rd. rewrite Hget. cbn.
          unfold Monads.OStateOperations.put. cbn [Monads.OState_Monad].
          unfold addi_isa_post, addi_regs. cbn [getRegs getNextPc].
          reflexivity.
        * assert (HRD : ((0 <? rd) && (rd <? 32))%bool = true).
          { apply andb_true_iff. split; apply Z.ltb_lt; lia. }
          rewrite HRD.
          cbn [Monads.Bind Monads.Return Monads.OState_Monad
               Monads.OStateOperations.get update withRegs getRegs].
          unfold Monads.OStateOperations.put. cbn [Monads.OState_Monad].
          unfold addi_isa_post, addi_regs, addi_result_word,
            formal_register_word. cbn [getRegs getNextPc].
          destruct (Z.eq_dec rd 0); [contradiction|].
          destruct (Z.eq_dec rs1 0); [contradiction|].
          rewrite Hget. reflexivity.
      + destruct (Z.eq_dec rd 0) as [Hrd0 | Hrd0].
        * subst rd. rewrite Hget. cbn.
          unfold Monads.OStateOperations.put. cbn [Monads.OState_Monad].
          unfold addi_isa_post, addi_regs. cbn [getRegs getNextPc].
          reflexivity.
        * assert (HRD : ((0 <? rd) && (rd <? 32))%bool = true).
          { apply andb_true_iff. split; apply Z.ltb_lt; lia. }
          rewrite HRD.
          cbn [Monads.Bind Monads.Return Monads.OState_Monad
               Monads.OStateOperations.get update withRegs getRegs].
          unfold Monads.OStateOperations.put. cbn [Monads.OState_Monad].
          unfold addi_isa_post, addi_regs, addi_result_word,
            formal_register_word. cbn [getRegs getNextPc].
          destruct (Z.eq_dec rd 0); [contradiction|].
          destruct (Z.eq_dec rs1 0); [contradiction|].
          rewrite Hget. reflexivity.
  Qed.

  (** Architectural projection exported by a CPU-specific adapter.  ROM and
      RAM remain the actual FormalSpec map types, so preservation is
      extensional rather than a checksum comparison. *)
  Record RTLArchitecturalState := {
    rtl_arch_pc : Z;
    rtl_arch_next_pc : Z;
    rtl_arch_rf : Z -> Z;
    rtl_arch_imem : Mem;
    rtl_arch_dmem : Mem
  }.

  Definition isa_rf_value (isa : FormalSpec.State) (r : Z) : Z :=
    if Z.eq_dec r 0 then 0
    else BzeenoFormalSim.formal_reg_value (getRegs isa) r.

  Definition StateRel (rtl : RTLArchitecturalState)
      (isa : FormalSpec.State) : Prop :=
    rtl.(rtl_arch_pc) = word.unsigned (getPc isa) /\
    rtl.(rtl_arch_next_pc) = word.unsigned (getNextPc isa) /\
    (forall r, legal_reg r ->
       rtl.(rtl_arch_rf) r = isa_rf_value isa r) /\
    rtl.(rtl_arch_imem) = getInstMem isa /\
    rtl.(rtl_arch_dmem) = getDataMem isa.

  Definition rtl_addi_result (rtl : RTLArchitecturalState)
      (rs1 imm : Z) : Z :=
    (rtl.(rtl_arch_rf) rs1 + imm) mod 2 ^ 32.

  Definition rtl_addi_post (rtl : RTLArchitecturalState)
      (rd rs1 imm : Z) : RTLArchitecturalState :=
    {| rtl_arch_pc := rtl.(rtl_arch_next_pc);
       rtl_arch_next_pc := (rtl.(rtl_arch_next_pc) + 4) mod 2 ^ 32;
       rtl_arch_rf := fun r =>
         if Z.eq_dec rd 0 then rtl.(rtl_arch_rf) r
         else if Z.eq_dec r rd then rtl_addi_result rtl rs1 imm
              else rtl.(rtl_arch_rf) r;
       rtl_arch_imem := rtl.(rtl_arch_imem);
       rtl_arch_dmem := rtl.(rtl_arch_dmem) |}.

  Lemma addi_result_word_unsigned : forall isa rs1 imm,
      legal_reg rs1 ->
      word.unsigned (addi_result_word isa rs1 imm) =
        (isa_rf_value isa rs1 + imm) mod 2 ^ 32.
  Proof.
    intros isa rs1 imm Hrs.
    unfold addi_result_word.
    rewrite word.unsigned_add, word.unsigned_of_Z.
    unfold word.wrap.
    rewrite Z.add_mod_idemp_r by lia.
    f_equal.
    unfold formal_register_word, isa_rf_value.
    destruct (Z.eq_dec rs1 0) as [-> | Hnz].
    - rewrite word.unsigned_of_Z. unfold word.wrap. reflexivity.
    - destruct (map.get (getRegs isa) rs1) as [w |] eqn:Hget.
      + unfold BzeenoFormalSim.formal_reg_value. rewrite Hget. reflexivity.
      + unfold BzeenoFormalSim.formal_reg_value. rewrite Hget.
        rewrite word.unsigned_of_Z. unfold word.wrap. reflexivity.
  Qed.

  Lemma addi_isa_post_rf : forall isa rd rs1 imm r,
      legal_reg r ->
      isa_rf_value (addi_isa_post isa rd rs1 imm) r =
        if Z.eq_dec rd 0 then isa_rf_value isa r
        else if Z.eq_dec r rd
             then word.unsigned (addi_result_word isa rs1 imm)
             else isa_rf_value isa r.
  Proof.
    intros isa rd rs1 imm r Hr.
    unfold isa_rf_value, addi_isa_post. cbn [getRegs].
    destruct (Z.eq_dec r 0) as [-> | Hr0].
    - destruct (Z.eq_dec rd 0) as [-> | Hrd0]; [reflexivity|].
      destruct (Z.eq_dec 0 rd); [congruence|reflexivity].
    - destruct (Z.eq_dec rd 0) as [-> | Hrd0].
      + unfold addi_regs. destruct (Z.eq_dec 0 0); [reflexivity|contradiction].
      + unfold addi_regs. destruct (Z.eq_dec rd 0); [contradiction|].
        destruct (Z.eq_dec r rd) as [-> | Hneq].
        * unfold BzeenoFormalSim.formal_reg_value.
          rewrite map.get_put_same. reflexivity.
        * unfold BzeenoFormalSim.formal_reg_value.
          rewrite map.get_put_diff by exact Hneq. reflexivity.
  Qed.

  (** Pure architectural preservation theorem.  The companion RTL theorem
      proves that the real CV32E40P next-commit projection is exactly
      [rtl_addi_post]; clients never need to unfold [FormalSpec.run1] again. *)
  Theorem state_rel_addi_preserved : forall rtl isa rd rs1 imm,
      legal_reg rd -> legal_reg rs1 -> legal_addi_imm imm ->
      StateRel rtl isa ->
      StateRel (rtl_addi_post rtl rd rs1 imm)
        (addi_isa_post isa rd rs1 imm).
  Proof.
    intros rtl isa rd rs1 imm Hrd Hrs Himm Hrel.
    destruct Hrel as (Hpc & Hnext & Hrf & Himem & Hdmem).
    unfold StateRel, rtl_addi_post. cbn [rtl_arch_pc rtl_arch_next_pc
      rtl_arch_rf rtl_arch_imem rtl_arch_dmem].
    repeat split.
    - exact Hnext.
    - cbn [addi_isa_post getNextPc].
      rewrite word.unsigned_add, word.unsigned_of_Z.
      unfold word.wrap. rewrite Z.add_mod_idemp_r by lia.
      change (4 mod 2 ^ 32) with 4. now rewrite Hnext.
    - intros r Hr.
      rewrite addi_isa_post_rf by exact Hr.
      destruct (Z.eq_dec rd 0) as [Hrd0 | Hrd0]; [apply Hrf; exact Hr|].
      destruct (Z.eq_dec r rd) as [-> | Hneq].
      + unfold rtl_addi_result.
        rewrite addi_result_word_unsigned by exact Hrs.
        now rewrite Hrf by exact Hrs.
      + apply Hrf. exact Hr.
    - cbn [getInstMem]. exact Himem.
    - cbn [getDataMem]. exact Hdmem.
  Qed.

  Theorem state_rel_after_run1_addi : forall rtl isa rd rs1 imm,
      legal_reg rd -> legal_reg rs1 -> legal_addi_imm imm ->
      ADDIAtPC isa rd rs1 imm -> StateRel rtl isa ->
      exists isa',
        FormalSpec.run1 isa = (Some tt, isa') /\
        StateRel (rtl_addi_post rtl rd rs1 imm) isa'.
  Proof.
    intros rtl isa rd rs1 imm Hrd Hrs Himm Hfetch Hrel.
    exists (addi_isa_post isa rd rs1 imm). split.
    - now apply run1_addi_exact.
    - now apply state_rel_addi_preserved.
  Qed.

End WithContext.

End CV32E40PReq40StateRel.
