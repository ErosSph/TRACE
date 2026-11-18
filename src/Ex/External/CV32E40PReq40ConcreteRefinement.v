(** Req40 concrete critical test: two dependent ADDI commits are related to
    two consecutive [FormalSpec.run1] steps.  The second RTL pre-state is the
    first real scheduler post-state; no reset or fixture reconstruction occurs
    between the applications. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CV32E40PReq39Trace.
Require Import Ex.External.CV32E40PReq40StateRel.
Require Import Ex.External.CV32E40PReq40NextCommit.
Require Import Ex.External.CV32E40PReq40ConcreteTrace.
Require Import Ex.External.CV32E40PReq40Windows.
Require Import Ex.External.CV32E40PReq40ReachableRefinement.
Require Import Ex.External.CV32E40PReq40ReachableTrace.
Require Import Ex.External.CV32E40PReq40InitialProjection.
Require Import Ex.External.BzeenoFormalSim.
Require Import Ex.External.BzeenoBaselineDataOps.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine.
Require Import riscv.Utility.Words32Naive riscv.Utility.DefaultMemImpl32.
Require Import riscv.Utility.MkMachineWidth.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Map.Interface coqutil.Word.Interface.

Import ListNotations.
Import CV32E40PReq39Trace CV32E40PReq40StateRel.
Import CV32E40PReq40NextCommit CV32E40PReq40ConcreteTrace.
Import CV32E40PReq40Windows.
Import CV32E40PReq40ReachableRefinement CV32E40PReq40ReachableTrace.
Import CV32E40PReq40InitialProjection BzeenoBaselineDataOps.
Local Open Scope Z_scope.

Module CV32E40PReq40ConcreteRefinement.
  (** This composition file consumes opaque trace certificates.  It must not
      ask conversion to execute the complete CPU a second time. *)
  #[local] Opaque full_cycle_image.

  Definition isa0 : FormalSpec.State :=
    {| getRegs := map.empty;
       getPc := word.of_Z 0;
       getNextPc := word.of_Z 4;
       getInstMem := image_formal_imem two_addi_image;
       getDataMem := word_formal_dmem 0 |}.

  Definition isa1 : FormalSpec.State := addi_isa_post isa0 1 0 1.
  Definition isa2 : FormalSpec.State := addi_isa_post isa1 1 1 1.

  Lemma initial_state_related : CV32StateRel first_window isa0.
  Proof.
    destruct first_window_initial_projection as (Hpc & Hnext & Hrf & Hmem).
    unfold CV32StateRel.
    split.
    - rewrite Hpc. change (0 = word.unsigned
        (@word.of_Z 32 Words32Naive.word 0)).
      rewrite word.unsigned_of_Z. reflexivity.
    - split.
      + rewrite Hnext. change (4 = word.unsigned
          (@word.of_Z 32 Words32Naive.word 4)).
        rewrite word.unsigned_of_Z. reflexivity.
      + split.
        * intros r Hr. rewrite Hrf by exact Hr.
          unfold isa_rf_value, isa0. cbn [getRegs].
          destruct (Z.eq_dec r 0); [reflexivity|].
          unfold BzeenoFormalSim.formal_reg_value.
          rewrite map.get_empty. reflexivity.
        * split.
          -- reflexivity.
          -- unfold window_pre_dmem. unfold addi_pre_memory in Hmem.
             rewrite Hmem. reflexivity.
  Qed.

  Lemma image_program_ok :
      Forall (fun iv : Z * Z => 0 <= fst iv < 2 ^ 30)
        (image_program two_addi_image).
  Proof.
    cbn [image_program index_image_from two_addi_image].
    constructor; [change (0 <= 0 < 1073741824); lia|].
    constructor; [change (0 <= 1 < 1073741824); lia|].
    constructor.
  Qed.

  Lemma fetch_first : exists bytes,
      Memory.load_bytes 4 (getInstMem isa0) (getPc isa0) = Some bytes /\
      LittleEndian.combine 4 bytes = addi_x1_x0_1.
  Proof.
    pose proof (BzeenoFormalSim.formal_initial_rom_values_related
      (image_program two_addi_image) image_program_ok) as Hrom.
    unfold BzeenoFormalSim.rom_values_related in Hrom.
    destruct (Hrom (word.of_Z 0) 0
      ltac:(rewrite word.unsigned_of_Z; reflexivity))
      as (bytes & Hload & Hcombine).
    exists bytes. split; assumption.
  Qed.

  Lemma fetch_second : exists bytes,
      Memory.load_bytes 4 (getInstMem isa1) (getPc isa1) = Some bytes /\
      LittleEndian.combine 4 bytes = second_addi.
  Proof.
    pose proof (BzeenoFormalSim.formal_initial_rom_values_related
      (image_program two_addi_image) image_program_ok) as Hrom.
    unfold BzeenoFormalSim.rom_values_related in Hrom.
    destruct (Hrom (word.of_Z 4) 1
      ltac:(rewrite word.unsigned_of_Z; reflexivity))
      as (bytes & Hload & Hcombine).
    exists bytes. split; assumption.
  Qed.

  Lemma isa0_addi : ADDIAtPC isa0 1 0 1.
  Proof.
    destruct fetch_first as (bytes & Hload & Hcombine).
    econstructor.
    - change (word.unsigned (@word.of_Z 32 Words32Naive.word 0) mod 4 = 0).
      rewrite word.unsigned_of_Z. reflexivity.
    - exact Hload.
    - replace (Decode.decode Decode.RV32I (LittleEndian.combine 4 bytes))
        with (Decode.decode Decode.RV32I addi_x1_x0_1).
      + exact decode_addi.
      + f_equal. symmetry. exact Hcombine.
  Qed.

  Lemma isa1_addi : ADDIAtPC isa1 1 1 1.
  Proof.
    destruct fetch_second as (bytes & Hload & Hcombine).
    econstructor.
    - change (word.unsigned (@word.of_Z 32 Words32Naive.word 4) mod 4 = 0).
      rewrite word.unsigned_of_Z. reflexivity.
    - exact Hload.
    - replace (Decode.decode Decode.RV32I (LittleEndian.combine 4 bytes))
        with (Decode.decode Decode.RV32I second_addi).
      + vm_compute. reflexivity.
      + f_equal. symmetry. exact Hcombine.
  Qed.

  Theorem two_real_commits_refine_two_run1_steps :
      FormalSpec.run1 isa0 = (Some tt, isa1) /\
      CV32StateRel second_window isa1 /\
      FormalSpec.run1 isa1 = (Some tt, isa2) /\
      CV32StateRel final_window isa2.
  Proof.
    assert (Hrun0 : FormalSpec.run1 isa0 = (Some tt, isa1)).
    { unfold isa1. apply run1_addi_exact;
        try (unfold legal_reg, legal_addi_imm; lia).
      exact isa0_addi. }
    destruct (cv32e40p_reachable_addi_next_commit_preserves_StateRel
      first_window isa0 1 0 1 ltac:(unfold legal_reg; lia)
      ltac:(unfold legal_reg; lia) ltac:(unfold legal_addi_imm; lia)
      isa0_addi initial_state_related first_reachable_invariant)
      as (mid & Hrun0' & Hrel1).
    rewrite Hrun0 in Hrun0'. inversion Hrun0'; subst mid.
    assert (Hrun1 : FormalSpec.run1 isa1 = (Some tt, isa2)).
    { unfold isa2. apply run1_addi_exact;
        try (unfold legal_reg, legal_addi_imm; lia).
      exact isa1_addi. }
    destruct (cv32e40p_reachable_addi_next_commit_preserves_StateRel
      second_window isa1 1 1 1 ltac:(unfold legal_reg; lia)
      ltac:(unfold legal_reg; lia) ltac:(unfold legal_addi_imm; lia)
      isa1_addi Hrel1 second_reachable_invariant)
      as (post & Hrun1' & Hrel2).
    rewrite Hrun1 in Hrun1'. inversion Hrun1'; subst post.
    split; [exact Hrun0|].
    split; [exact Hrel1|].
    split; [exact Hrun1|exact Hrel2].
  Qed.

  Theorem isa2_architectural_fields :
      word.unsigned (getPc isa2) = 8 /\
      word.unsigned (getNextPc isa2) = 12 /\
      BzeenoFormalSim.formal_reg_value (getRegs isa2) 1 = 2 /\
      getInstMem isa2 = getInstMem isa0 /\
      getDataMem isa2 = getDataMem isa0.
  Proof.
    split.
    - unfold isa2, isa1, addi_isa_post.
      cbn [getPc getNextPc].
      rewrite word.unsigned_add, !word.unsigned_of_Z. reflexivity.
    - split.
      + unfold isa2, isa1, addi_isa_post.
        cbn [getNextPc].
        rewrite !word.unsigned_add, !word.unsigned_of_Z. reflexivity.
      + split.
        * change (isa_rf_value isa2 1 = 2).
          unfold isa2.
          rewrite addi_isa_post_rf by (unfold legal_reg; lia).
          destruct (Z.eq_dec 1 0); [lia|].
          destruct (Z.eq_dec 1 1); [|lia].
          rewrite addi_result_word_unsigned by (unfold legal_reg; lia).
          unfold isa1.
          rewrite addi_isa_post_rf by (unfold legal_reg; lia).
          destruct (Z.eq_dec 1 0); [lia|].
          destruct (Z.eq_dec 1 1); [|lia].
          rewrite addi_result_word_unsigned by (unfold legal_reg; lia).
          unfold isa_rf_value, isa0. cbn [getRegs].
          destruct (Z.eq_dec 0 0); [reflexivity|lia].
        * split; reflexivity.
  Qed.

End CV32E40PReq40ConcreteRefinement.
