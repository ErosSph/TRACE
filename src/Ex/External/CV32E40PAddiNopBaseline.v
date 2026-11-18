(** Opt-in NOP-ROM initialization for the real scheduler. Old fixtures intact. *)
From Coq Require Import ZArith List Lia.
From ITree Require Import ITree ITreeFacts.
Require Import Ex.External.CV32E40PAddiNopROM
  Ex.External.CV32E40PAddiNopISAInvariant
  Ex.External.CV32E40PAddiPhysicalRefinement Ex.External.CV32E40PAddiITree
  Ex.External.CV32E40PAddiCommitSchedule Ex.External.CV32E40PAddiCommitTrace
  Ex.External.CV32E40PAddiReachability Ex.External.CV32E40PReq40ConcreteRefinement
  Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PReq39Trace.
Require Import Ex.RvCore.Machine Ex.RvCore.FormalSpec.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Import CV32E40PAddiNopROM CV32E40PAddiPhysicalRefinement CV32E40PAddiITree
  CV32E40PAddiNopISAInvariant
  CV32E40PAddiCommitSchedule CV32E40PAddiCommitTrace CV32E40PAddiReachability
  CV32E40PReq40ConcreteRefinement CV32E40PReq40StateRel CV32E40PReq39Trace.
Local Open Scope Z_scope.
Local Open Scope itree_scope.
Module CV32E40PAddiNopBaseline.
  #[local] Opaque nop_rom cycle physical_projection FormalSpec.run1.
  Definition with_nop_rom (s : FormalSpec.State) : FormalSpec.State :=
    withInstMem (nop_rom image) s.
  Definition spec0 := with_nop_rom isa0.
  Definition spec1 := addi_isa_post spec0 1 0 1.
  Definition spec2 := addi_isa_post spec1 1 1 1.
  Definition spec3 := addi_isa_post spec2 0 0 0.

  Lemma fetch_decode s rd rs imm :
    getInstMem s = nop_rom image -> word.unsigned (getPc s) mod 4 = 0 ->
    Decode.decode Decode.RV32I
      (instruction_from_image image (word.unsigned (getPc s)) mod 2^32) =
        Decode.IInstruction (Decode.Addi rd rs imm) -> ADDIAtPC s rd rs imm.
  Proof.
    intros Hmem Halign Hdecode. econstructor.
    - exact Halign.
    - rewrite Hmem. apply nop_rom_fetch. exact Halign.
    - rewrite LittleEndian.combine_split. exact Hdecode.
  Qed.
  Lemma spec0_addi : ADDIAtPC spec0 1 0 1.
  Proof. apply fetch_decode; reflexivity. Qed.
  Lemma spec1_addi : ADDIAtPC spec1 1 1 1.
  Proof. apply fetch_decode; reflexivity. Qed.
  Lemma spec2_nop : ADDIAtPC spec2 0 0 0.
  Proof. apply fetch_decode; reflexivity. Qed.
  Theorem three_successful_run1_steps :
    FormalSpec.run1 spec0 = (Some tt, spec1) /\
    FormalSpec.run1 spec1 = (Some tt, spec2) /\
    FormalSpec.run1 spec2 = (Some tt, spec3).
  Proof.
    split.
    - exact (run1_addi_exact spec0 1 0 1 ltac:(unfold legal_reg; lia)
        ltac:(unfold legal_reg; lia) ltac:(unfold legal_addi_imm; lia) spec0_addi).
    - split.
      + exact (run1_addi_exact spec1 1 1 1 ltac:(unfold legal_reg; lia)
          ltac:(unfold legal_reg; lia) ltac:(unfold legal_addi_imm; lia) spec1_addi).
      + exact (run1_addi_exact spec2 0 0 0 ltac:(unfold legal_reg; lia)
          ltac:(unfold legal_reg; lia) ltac:(unfold legal_addi_imm; lia) spec2_nop).
  Qed.

  Definition physical_nop_projection (s : RetirementState) : RTLArchitecturalState :=
    let p := physical_projection s in
    {| rtl_arch_pc := rtl_arch_pc p; rtl_arch_next_pc := rtl_arch_next_pc p;
       rtl_arch_rf := rtl_arch_rf p; rtl_arch_imem := nop_rom image;
       rtl_arch_dmem := rtl_arch_dmem p |}.
  Lemma transport_relation rtl isa :
    StateRel (physical_projection rtl) isa ->
    StateRel (physical_nop_projection rtl) (with_nop_rom isa).
  Proof.
    unfold physical_nop_projection, with_nop_rom.
    generalize (nop_rom image). intro rom.
    destruct isa as [regs pc npc imem dmem].
    intros (Hpc & Hnext & Hrf & Hrom & Hram).
    unfold StateRel, withInstMem.
    cbn. split; [exact Hpc|]. split; [exact Hnext|].
    split; [exact Hrf|]. split; [reflexivity|exact Hram].
  Qed.
  Lemma addi_post_change_rom (s : FormalSpec.State) rom rd rs imm :
    addi_isa_post (withInstMem rom s) rd rs imm =
      withInstMem rom (addi_isa_post s rd rs imm).
  Proof. destruct s. reflexivity. Qed.
  Lemma spec1_transport : spec1 = with_nop_rom isa1.
  Proof.
    unfold spec1, spec0, with_nop_rom, isa1.
    apply addi_post_change_rom.
  Qed.
  Lemma spec2_transport : spec2 = with_nop_rom isa2.
  Proof.
    unfold spec2. rewrite spec1_transport.
    unfold with_nop_rom, isa2. apply addi_post_change_rom.
  Qed.
  Theorem real_two_commit_relations :
    StateRel (physical_nop_projection (cycle 5)) spec0 /\
    StateRel (physical_nop_projection (cycle 6)) spec1 /\
    StateRel (physical_nop_projection (cycle 7)) spec2.
  Proof.
    rewrite spec1_transport, spec2_transport.
    split; [apply transport_relation; exact physical_initial_related|].
    split.
    - apply transport_relation. exact physical_first_post_related.
    - apply transport_relation. exact physical_second_post_related.
  Qed.

  Definition three_outputs (k : itree Events void) :=
    Vis (inl1 (FormalSpec.Output 0)) (fun _ =>
      Vis (inl1 (FormalSpec.Output 4)) (fun _ =>
        Vis (inl1 (FormalSpec.Output 8)) (fun _ => k))).
  Theorem rtl_three_events : rtl_itree image (cycle 0) ≈
    three_outputs (rtl_itree image (cycle 8)).
  Proof.
    rewrite (next_retirement_itree _ _ _ _ _ first_real_retirement).
    unfold three_outputs. apply eqit_Vis. intros [].
    rewrite (next_retirement_itree _ _ _ _ _ second_real_retirement).
    apply eqit_Vis. intros [].
    apply (next_retirement_itree image (cycle 7) 1 (token 8 19) (cycle 8)).
    apply retire_at_cycle. rewrite retirement_at_cycle by lia. reflexivity.
  Qed.
  Theorem isa_three_events : FormalSpec.riscv_itree_with_state spec0 ≈
    three_outputs (FormalSpec.riscv_itree_with_state spec3).
  Proof.
    destruct three_successful_run1_steps as (H0 & H1 & H2).
    rewrite (formal_success_unfold _ _ H0). unfold three_outputs.
    apply eqit_Vis. intros []. rewrite (formal_success_unfold _ _ H1).
    apply eqit_Vis. intros []. rewrite (formal_success_unfold _ _ H2).
    apply eqit_Vis. intros []. reflexivity.
  Qed.
  Lemma image_all_addi : Forall GoodADDI image.
  Proof.
    constructor.
    - exists 1, 0, 1. repeat split; unfold legal_reg, legal_addi_imm; lia || reflexivity.
    - constructor.
      + exists 1, 1, 1. repeat split; unfold legal_reg, legal_addi_imm; lia || reflexivity.
      + constructor.
  Qed.
  Lemma initial_isa_invariant : ISAInvariant image spec0.
  Proof. split; [reflexivity|]. split; reflexivity. Qed.
  Theorem baseline_isa_never_runs_out_of_instructions n :
    exists s', ISARuns n spec0 s' /\ ISAInvariant image s'.
  Proof.
    exact (arbitrary_finite_isa_progress image spec0 n image_all_addi initial_isa_invariant).
  Qed.
  Print Assumptions three_successful_run1_steps.
  Print Assumptions real_two_commit_relations.
  Print Assumptions rtl_three_events.
  Print Assumptions isa_three_events.
  Print Assumptions baseline_isa_never_runs_out_of_instructions.
End CV32E40PAddiNopBaseline.
