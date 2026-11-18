(** Preserve auxiliary histories when their actual process did not trigger. *)
From Coq Require Import ZArith List.
Require Import Lang.ExtendedSV Lang.ExtendedSVCaptureBirth Lang.ExtendedSVProjectionOrigin.
Import ExtendedSV ExtendedSVCaptureBirth ExtendedSVProjectionOrigin.
Module ExtendedSVPhaseIdle.
Theorem ghost_idle p proc root word valid pc ev pre g:
 process_matches_states pre(phase_driven_state p ev pre)proc=false ->
 ghost_step p proc root word valid pc ev pre g=g.
Proof.
 intro HF;unfold ghost_step,phase_decision;rewrite HF;destruct g;reflexivity.
Qed.
Theorem origin_idle (Label:Type)p proc recipe ev pre(old incoming:option Label):
 process_matches_states pre(phase_driven_state p ev pre)proc=false ->
 @projection_phase_origin Label p proc recipe ev pre old incoming=old.
Proof. intro HF;unfold projection_phase_origin;now rewrite HF. Qed.
End ExtendedSVPhaseIdle.
Print Assumptions ExtendedSVPhaseIdle.ghost_idle.
Print Assumptions ExtendedSVPhaseIdle.origin_idle.
