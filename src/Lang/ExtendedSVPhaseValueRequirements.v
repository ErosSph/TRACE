(** Value obligations are evaluated at the real sample, not the post-state.
    Non-triggered phases retain the pre-state field. *)
From Coq Require Import ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVValueRequirements.
Import ExtendedSV ExtendedSVValueRequirements.
Module ExtendedSVPhaseValueRequirements.
Definition phase_requirements p proc width root expression ev pre expected : Prop :=
 (process_matches_states pre (phase_driven_state p ev pre) proc=true ->
  requirements width expression (phase_driven_state p ev pre) expected) /\
 (process_matches_states pre (phase_driven_state p ev pre) proc=false ->
  norm width(read_signal pre root)=expected).

Theorem phase_requirements_exact p proc width root expression ev pre expected:
 norm width(read_signal(PhaseSemantics p ev pre)root)=
 (if process_matches_states pre(phase_driven_state p ev pre)proc
  then norm width(eval_expr(phase_driven_state p ev pre)expression)
  else norm width(read_signal pre root)) ->
 (phase_requirements p proc width root expression ev pre expected <->
  norm width(read_signal(PhaseSemantics p ev pre)root)=expected).
Proof.
 intro H;rewrite H;unfold phase_requirements;rewrite requirements_exact.
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc);
 intuition discriminate.
Qed.
End ExtendedSVPhaseValueRequirements.
Print Assumptions ExtendedSVPhaseValueRequirements.phase_requirements_exact.
