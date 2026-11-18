(** All pending/retired monitor tokens have reachable ID sampling provenance.
    The sampled data projections are connected to the actual rising phase.
    This is safety/provenance, not ALU operand freshness or liveness. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Ex.Generated.CV32E40PExtendedAST
  Ex.External.CV32E40PReq39Trace Ex.External.CV32E40PAddiReachability
  Ex.External.CV32E40PAddiTokenOrigin Ex.External.CV32E40PAddiIDSampling.
Import ExtendedSV CV32E40PExtendedAST CV32E40PReq39Trace CV32E40PAddiReachability
  CV32E40PAddiTokenOrigin CV32E40PAddiIDSampling.
Module CV32E40PAddiTokenSampling.
  Definition edge_input image s := phase_driven_state cv32e40p_program clk_rise
    (environment_state_image image (physical_state s)).
  Lemma environment_to_edge image s :
    norm 32 (read_signal (edge_input image s) 718) =
      norm 32 (read_signal (environment_state_image image (physical_state s)) 718) /\
    norm 32 (read_signal (edge_input image s) 121) =
      norm 32 (read_signal (environment_state_image image (physical_state s)) 121).
  Proof.
    unfold edge_input, environment_state_image, obi_ports_image. cbv beta zeta.
    apply settled_to_edge_id_projection; discriminate.
  Qed.
  Definition OriginSample image token origin :=
    norm 32 (token_instruction token) = norm 32 (read_signal (edge_input image origin) 718) /\
    norm 32 (token_pc token) = norm 32 (read_signal (edge_input image origin) 121).
  Lemma issued_has_edge_sample image origin token :
    issued image origin = Some token -> OriginSample image token origin.
  Proof.
    intros Hissue. destruct (issued_token_records_actual_id_ports image origin token Hissue) as [Hpc Hins].
    destruct (environment_to_edge image origin) as [Hedgeins Hedgepc].
    unfold OriginSample. rewrite Hpc, Hins. split; symmetry; assumption.
  Qed.
  Theorem all_reachable_pending_tokens_have_actual_edge_origin image s :
    ResetReachable image s -> forall token, pending_token s = Some token ->
    exists origin n, ResetReachable image origin /\
      TokenResidence image origin token n s /\ OriginSample image token origin.
  Proof.
    intros Hreach token Hpending.
    destruct (every_pending_token_has_reachable_origin image s Hreach token Hpending)
      as (origin&n&Horigin&Hres).
    exists origin, n. split; [exact Horigin|]. split; [exact Hres|].
    apply issued_has_edge_sample. eapply residence_has_actual_issue; exact Hres.
  Qed.
  Theorem all_retirements_have_actual_edge_origin image pre n token post :
    NextRetirement image pre n token post -> ResetReachable image pre ->
    exists origin, ResetReachable image origin /\ OriginSample image token origin.
  Proof.
    intros Hnext Hreach.
    destruct (every_retirement_has_reachable_issue image pre n token post Hnext Hreach)
      as (origin&Horigin&Hissue).
    exists origin. split; [exact Horigin|]. now apply issued_has_edge_sample.
  Qed.
  Print Assumptions all_reachable_pending_tokens_have_actual_edge_origin.
  Print Assumptions all_retirements_have_actual_edge_origin.
End CV32E40PAddiTokenSampling.
