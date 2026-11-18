(** Propagate an existing reference value through an actual selected copy.
    Sampling uses phase_driven_state, never an arbitrary pre/post-state.
    Queue ownership and the retiring reference chain remain explicit. *)
From Coq Require Import List ZArith.
Require Import Ex.External.CPUActualSourceCapture Ex.External.CPUReferenceCutTransfer.
Import ListNotations ExtendedSV.ExtendedSV
 ExtendedSVInstructionOrigin.ExtendedSVInstructionOrigin
 ExtendedSVWordInvariant.ExtendedSVWordInvariant CPUActualSourceCapture
 CPUReferenceCuts.CPUReferenceCuts CPUGeneratedJointTemplate.CPUGeneratedJointTemplate
 CPUReferenceCutTransfer.
Module CPUActualCaptureReference.

Theorem capture_value p proc destination expression ev pre source:
 norm 32(read_signal(PhaseSemantics p ev pre)destination)=
 (if process_matches_states pre(phase_driven_state p ev pre)proc
 then norm 32(eval_expr(phase_driven_state p ev pre)expression)
 else norm 32(read_signal pre destination)) ->
 capture_source p proc destination expression ev pre=Some source ->
 norm 32(read_signal(PhaseSemantics p ev pre)destination)=
 norm 32(read_signal(phase_driven_state p ev pre)source).
Proof.
 intros HE HS.
 destruct(capture_selected p proc destination expression ev pre source HS)
 as[HF[HC HN]].
 rewrite HE,HF,(copy_source_sound expression(phase_driven_state p ev pre)source HC).
 apply norm_idempotent.
Qed.

Theorem captured_token_transfer {Architecture Token:Type}
 (effect:Token->Architecture->option Architecture)(project:Architecture->Z)
 p proc destination expression ev pre source
 initial advanced retiring kept added index token:
 norm 32(read_signal(PhaseSemantics p ev pre)destination)=
 (if process_matches_states pre(phase_driven_state p ev pre)proc
 then norm 32(eval_expr(phase_driven_state p ev pre)expression)
 else norm 32(read_signal pre destination)) ->
 capture_source p proc destination expression ev pre=Some source ->
 EffectChain effect initial retiring advanced ->
 FieldAtToken effect project initial(retiring++kept)(length retiring+index)token
 (norm 32(read_signal(phase_driven_state p ev pre)source)) ->
 FieldAtToken effect project advanced(kept++added)index token
 (norm 32(read_signal(PhaseSemantics p ev pre)destination)).
Proof.
 intros HE HS HC HR.
 rewrite(capture_value p proc destination expression ev pre source HE HS).
 exact(field_cycle effect project initial advanced retiring kept added index token _ HC HR).
Qed.
End CPUActualCaptureReference.
Print Assumptions CPUActualCaptureReference.capture_value.
Print Assumptions CPUActualCaptureReference.captured_token_transfer.
