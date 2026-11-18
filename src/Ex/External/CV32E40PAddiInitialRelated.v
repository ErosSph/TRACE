(** StateRel at the actual reset/release state, for any instruction image.
    This is the initialization obligation, not the inductive step. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CV32E40PAddiResetInvariant
  Ex.External.CV32E40PAddiReachability Ex.External.CV32E40PReq39Trace
  Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PReq40ConcreteRefinement
  Ex.External.CV32E40PAddiNopROM Ex.External.CV32E40PAddiNopISAInvariant
  Ex.External.CV32E40PAddiNopBaseline Ex.External.CV32E40PAddiCommitTrace
  Ex.External.CV32E40PReq40Windows Ex.External.CV32E40PReq40NextCommit Ex.External.BzeenoFormalSim.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Properties.
Import CV32E40PAddiResetInvariant CV32E40PAddiReachability CV32E40PReq39Trace
  CV32E40PReq40StateRel CV32E40PReq40ConcreteRefinement CV32E40PReq40Windows
  CV32E40PReq40NextCommit CV32E40PAddiNopROM CV32E40PAddiNopISAInvariant.
Local Open Scope Z_scope.
Module CV32E40PAddiInitialRelated.
  Definition architecture image (s : RetirementState) : RTLArchitecturalState :=
    {| rtl_arch_pc := architectural_cursor s;
       rtl_arch_next_pc := (architectural_cursor s + 4) mod 2^32;
       rtl_arch_rf := fun r => if (0 <=? r) && (r <? 32)
         then rf_register (trace_rtl (physical_state s)) (Z.to_nat r) else 0;
       rtl_arch_imem := nop_rom image;
       rtl_arch_dmem := word_formal_dmem (trace_memory_word (physical_state s)) |}.
  Definition initial_isa image : FormalSpec.State :=
    {| getRegs := map.empty; getPc := word.of_Z 0; getNextPc := word.of_Z 4;
       getInstMem := nop_rom image; getDataMem := word_formal_dmem 0 |}.
  Lemma baseline_projection_unchanged s :
    architecture CV32E40PAddiCommitTrace.CV32E40PAddiCommitTrace.image s =
    CV32E40PAddiNopBaseline.CV32E40PAddiNopBaseline.physical_nop_projection s.
  Proof. reflexivity. Qed.
  Lemma baseline_initial_isa_unchanged :
    initial_isa CV32E40PAddiCommitTrace.CV32E40PAddiCommitTrace.image =
    CV32E40PAddiNopBaseline.CV32E40PAddiNopBaseline.spec0.
  Proof. reflexivity. Qed.
  #[local] Opaque nop_rom word_formal_dmem rf_register FormalSpec.run1.
  Theorem reset_architectural_relation image :
    StateRel (architecture image reset_retirement) (initial_isa image).
  Proof.
    unfold StateRel, architecture, initial_isa.
    cbn [rtl_arch_pc rtl_arch_next_pc rtl_arch_rf rtl_arch_imem rtl_arch_dmem
      getPc getNextPc getRegs getInstMem getDataMem].
    split; [reflexivity|]. split; [reflexivity|]. split.
    - intros r Hr.
      assert (Hvalid : (0 <=? r) && (r <? 32) = true).
      { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; exact (proj1 Hr) || exact (proj2 Hr). }
      rewrite Hvalid, actual_reset_all_registers_zero.
      unfold isa_rf_value. destruct (Z.eq_dec r 0); [reflexivity|].
      unfold BzeenoFormalSim.formal_reg_value. cbn [getRegs].
      rewrite map.get_empty. reflexivity.
    - split; reflexivity.
  Qed.
  Theorem reset_isa_well_formed image : ISAInvariant image (initial_isa image).
  Proof. split; [reflexivity|]. split; reflexivity. Qed.
  Theorem reset_related_and_all_future_x0 image :
    StateRel (architecture image reset_retirement) (initial_isa image) /\
    (forall s, ResetReachable image s -> X0Zero s).
  Proof. split; [apply reset_architectural_relation|apply every_reset_reachable_state_has_zero_x0]. Qed.
  Print Assumptions reset_architectural_relation.
  Print Assumptions reset_related_and_all_future_x0.
End CV32E40PAddiInitialRelated.
