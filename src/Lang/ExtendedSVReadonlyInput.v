(** A generated read-only storage component, independent of a previous INV.
    External installers and ISA-memory correspondence are separate obligations. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVAutoAdapterPhase Lang.ExtendedSVScalarHistory.
Import ListNotations ExtendedSV ExtendedSVAutoAdapterPhase ExtendedSVScalarHistory.
Module ExtendedSVReadonlyInput.
Theorem readonly_phase p root (certificate:PlanRootCertificate p root []) ev pre :
 changed_signal ev<>root ->
 read_signal(PhaseSemantics p ev pre)root=read_signal pre root.
Proof.
 intro HE. rewrite(planned_phase_root p root [] certificate ev pre HE). reflexivity.
Qed.
Theorem readonly_history p root (certificate:PlanRootCertificate p root []) events :
 Forall(fun ev=>changed_signal ev<>root)events ->forall pre,
 read_signal(phase_run p events pre)root=read_signal pre root.
Proof.
 intro HE;induction HE as[|ev tail HS Htail IH];intro pre;[reflexivity|].
 cbn[phase_run]. rewrite IH. now apply readonly_phase.
Qed.
Print Assumptions readonly_phase.
Print Assumptions readonly_history.
End ExtendedSVReadonlyInput.
