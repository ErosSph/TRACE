(** An actual selected self-copy preserves an existing token value even on a
    triggered phase. This is neither an inactive instruction nor a new capture. *)
From Coq Require Import List ZArith.
Require Import Lang.ExtendedSVScalarExpression Ex.External.CPUActualCaptureReference.
Import ListNotations ExtendedSV.ExtendedSV ExtendedSVScalarExpression
 ExtendedSVRootProjection.ExtendedSVRootProjection
 ExtendedSVInstructionOrigin.ExtendedSVInstructionOrigin
 ExtendedSVWordInvariant.ExtendedSVWordInvariant
 CPUReferenceCuts.CPUReferenceCuts CPUGeneratedJointTemplate.CPUGeneratedJointTemplate
 CPUReferenceCutTransfer.CPUReferenceCutTransfer.
Module CPUSelfHoldReference.
Theorem self_hold_value p proc root expression ev pre:
 comb_root_unwrittenb p root=true -> changed_signal ev<>root ->
 norm 32(read_signal(PhaseSemantics p ev pre)root)=
 (if process_matches_states pre(phase_driven_state p ev pre)proc
 then norm 32(eval_expr(phase_driven_state p ev pre)expression)
 else norm 32(read_signal pre root)) ->
 copy_source(phase_driven_state p ev pre)expression=Some root ->
 norm 32(read_signal(PhaseSemantics p ev pre)root)=norm 32(read_signal pre root).
Proof.
 intros HW HE HP HS;rewrite HP.
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc);[|reflexivity].
 rewrite(copy_source_sound expression(phase_driven_state p ev pre)root HS),norm_idempotent.
 now rewrite(sampled_root_preserved p ev pre root HW HE).
Qed.

Theorem self_hold_token_transfer {Architecture Token:Type}
 (effect:Token->Architecture->option Architecture)(project:Architecture->Z)
 p proc root expression ev pre initial advanced retiring kept added index token:
 comb_root_unwrittenb p root=true ->changed_signal ev<>root ->
 norm 32(read_signal(PhaseSemantics p ev pre)root)=
 (if process_matches_states pre(phase_driven_state p ev pre)proc
 then norm 32(eval_expr(phase_driven_state p ev pre)expression)
 else norm 32(read_signal pre root)) ->
 copy_source(phase_driven_state p ev pre)expression=Some root ->
 EffectChain effect initial retiring advanced ->
 FieldAtToken effect project initial(retiring++kept)(length retiring+index)token
 (norm 32(read_signal pre root)) ->
 FieldAtToken effect project advanced(kept++added)index token
 (norm 32(read_signal(PhaseSemantics p ev pre)root)).
Proof.
 intros HW HE HP HS HC HR.
 rewrite(self_hold_value p proc root expression ev pre HW HE HP HS).
 exact(field_cycle effect project initial advanced retiring kept added index token _ HC HR).
Qed.
End CPUSelfHoldReference.
Print Assumptions CPUSelfHoldReference.self_hold_value.
Print Assumptions CPUSelfHoldReference.self_hold_token_transfer.
