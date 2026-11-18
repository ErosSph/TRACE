(** Relate two auxiliary histories over the SAME actual phase semantics.
    A change of record layout is not an RTL or ISA execution assumption. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVRuntimeHistory Lang.ExtendedSVPhaseInstrumentation.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVRuntimeHistory ExtendedSVPhaseInstrumentation.
Module ExtendedSVHistoryRepresentation.
Section Representation.
Context {Left Right:Type}.
Variable p:Program.
Variable advance:Event->State->Left->unit->Left.
Variable update:Event->State->Right->Right.
Variable represent:Left->Right.
Variable step:forall ev pre ghost,represent(advance ev pre ghost tt)=update ev pre(represent ghost).

Theorem replay_map events:forall pre ghost,
 instrumented_run p update events pre(represent ghost)=
 (phase_run p events pre,represent(replay p Left advance events pre ghost)).
Proof.
 induction events as[|ev rest IH];intros pre ghost;
 cbn[instrumented_run phase_run replay];[reflexivity|].
 rewrite<-step;apply IH.
Qed.

Theorem reflected_empty events pre ghost final empty:
 (forall left right,represent left=represent right ->left=right) ->
 instrumented_run p update events pre(represent ghost)=(final,represent empty) ->
 replay p Left advance events pre ghost=empty.
Proof.
 intros HI HR;apply HI;pose proof(f_equal snd HR)as HH.
 rewrite(replay_map events pre ghost)in HH;exact HH.
Qed.
End Representation.
End ExtendedSVHistoryRepresentation.
Print Assumptions ExtendedSVHistoryRepresentation.replay_map.
Print Assumptions ExtendedSVHistoryRepresentation.reflected_empty.
