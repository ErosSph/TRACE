(** Sideband state cannot alter the original phase transition. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory.
Import ListNotations ExtendedSV ExtendedSVScalarHistory.
Module ExtendedSVPhaseInstrumentation.
Section Instrumentation.
Context {Ghost:Type}.
Variable p:Program.
Variable update:Event->State->Ghost->Ghost.
Fixpoint instrumented_run events pre g:State*Ghost:=match events with
| []=>(pre,g)
| ev::rest=>instrumented_run rest(PhaseSemantics p ev pre)(update ev pre g)
end.
Theorem instrumented_erases events:forall pre g,
 fst(instrumented_run events pre g)=phase_run p events pre.
Proof.
 induction events as[|ev rest IH];intros pre g;cbn[instrumented_run phase_run].
 - reflexivity.
 - exact(IH(PhaseSemantics p ev pre)(update ev pre g)).
Qed.
End Instrumentation.
Print Assumptions instrumented_erases.
End ExtendedSVPhaseInstrumentation.
