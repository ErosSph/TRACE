(** Raw bit invariants from original reset reachability. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitInvariant
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PReq38Phase
 Ex.External.CV32E40PReq38Clock Ex.External.CV32E40PReq39Trace
 Ex.External.CV32E40PAddiReachability.
Import ListNotations ExtendedSV ExtendedSVBitInvariant CV32E40PExtendedAST
 CV32E40PReq38Phase CV32E40PReq38Clock CV32E40PReq39Trace CV32E40PAddiReachability.
Module CV32E40PInternalBits.
 Definition external_roots : list nat := [7;8;9;10;11;12;13;14;15;17;18;20;22;23;28;29;32;36].
 Definition InternalBit root := program_bitb cv32e40p_program root = true /\ ~ In root external_roots.
 Lemma external_other root x : ~ In root external_roots -> In x external_roots -> x <> root.
 Proof. intros H Hx ->. contradiction. Qed.
 Lemma released_bit root : InternalBit root -> BitRoot root released.
 Proof.
   intros [Hp Hext]. unfold released, post_reset.
   apply phase_bit; [exact Hp|apply (external_other root 8 Hext); cbn; tauto|].
   apply phase_bit; [exact Hp|apply (external_other root 8 Hext); cbn; tauto|].
   unfold pre_reset. apply lfp_bit; [exact Hp|]. unfold BitRoot.
   rewrite read_signal_write_other by (apply (external_other root 8 Hext); cbn; tauto).
   apply initialize_bit; [exact Hp|apply zero_state_bit].
 Qed.
 #[local] Opaque lfp_candidate PhaseSemantics read_signal.
 Lemma environment_bit root image s : InternalBit root -> BitRoot root (trace_rtl s) ->
   BitRoot root (environment_state_image image s).
 Proof.
   intros [Hp Hext] Hs. unfold environment_state_image, obi_ports_image.
   apply lfp_bit; [exact Hp|]. unfold BitRoot, drive. cbn [fold_left fst snd].
   repeat rewrite read_signal_write_other by (eapply external_other; [exact Hext|cbn; tauto]).
   exact Hs.
 Qed.
 Lemma cycle_bit root image s : InternalBit root -> BitRoot root (trace_rtl s) ->
   BitRoot root (trace_rtl (full_cycle_image image s)).
 Proof.
   intros H Hs. destruct H as [Hp Hext].
   change (BitRoot root (settled_state_image image s)). unfold settled_state_image.
   apply lfp_bit; [exact Hp|]. unfold falling_state_image, rising_state_image.
   apply phase_bit; [exact Hp|apply (external_other root 7 Hext); cbn; tauto|].
   apply phase_bit; [exact Hp|apply (external_other root 7 Hext); cbn; tauto|].
   apply environment_bit; [split; assumption|exact Hs].
 Qed.
 Theorem reachable_internal_bit root image s : InternalBit root -> ResetReachable image s ->
   BitRoot root (trace_rtl (physical_state s)).
 Proof.
   intros Hb Hr. induction Hr; [now apply released_bit|].
   rewrite advance_physical. apply cycle_bit; assumption.
 Qed.
 Lemma prefetch_clock_internal : InternalBit 418.
 Proof. split; [vm_compute; reflexivity|cbn; intuition discriminate]. Qed.
 Lemma prefetch_reset_internal : InternalBit 419.
 Proof. split; [vm_compute; reflexivity|cbn; intuition discriminate]. Qed.
 Theorem reachable_prefetch_bits image s : ResetReachable image s ->
   BitRoot 418 (trace_rtl (physical_state s)) /\ BitRoot 419 (trace_rtl (physical_state s)).
 Proof. intros H. split; eapply reachable_internal_bit; eauto using prefetch_clock_internal, prefetch_reset_internal. Qed.
 Print Assumptions reachable_prefetch_bits.
End CV32E40PInternalBits.
