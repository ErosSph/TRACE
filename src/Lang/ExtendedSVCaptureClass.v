(** Instruction-class evidence follows the SAME capture update as the RTL
    history. The class is arbitrary: no CPU, opcode, or ISA is built into this
    rule. New-class premises refer only to actual newly captured records. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVCaptureBirth
 Lang.ExtendedSVCaptureContent Lang.ExtendedSVCapturedPending.
Import ListNotations ExtendedSV ExtendedSVCaptureBirth ExtendedSVCaptureContent
 ExtendedSVCapturedPending.
Module ExtendedSVCaptureClass.

Theorem phase_class p proc root word valid pc (P:Token->Prop) ev pre g:
 Forall P(observed_births p proc root word valid pc ev pre g) ->Related P g ->
 Related P(ghost_step p proc root word valid pc ev pre g).
Proof.
 intros HNew[HHistory HCurrent];unfold Related,ghost_step;cbn[history current].
 apply decision_preserves;[|exact HHistory|exact HCurrent].
 intros source HD;unfold observed_births in HNew;rewrite HD in HNew.
 inversion HNew;assumption.
Qed.

Theorem idle_phase_class p proc root word valid pc (P:Token->Prop) ev pre g:
 process_matches_states pre(phase_driven_state p ev pre)proc=false ->
 Related P g ->Related P(ghost_step p proc root word valid pc ev pre g).
Proof.
 intros HM HR;apply phase_class;[|exact HR].
 unfold observed_births,phase_decision;rewrite HM;constructor.
Qed.

Theorem class_implication (P Q:Token->Prop) g:
 (forall token,P token ->Q token) ->Related P g ->Related Q g.
Proof.
 intros HP[HH HC];split.
 - eapply Forall_impl;[exact HP|exact HH].
 - intros token HT;apply HP;exact(HC token HT).
Qed.

End ExtendedSVCaptureClass.
Print Assumptions ExtendedSVCaptureClass.phase_class.
Print Assumptions ExtendedSVCaptureClass.idle_phase_class.
Print Assumptions ExtendedSVCaptureClass.class_implication.
