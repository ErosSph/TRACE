(** A history chain transports ghost labels without altering RTL execution.
    Boundary evidence is explicit; this theorem does not supply ISA identity. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory.
Import ListNotations ExtendedSV ExtendedSVScalarHistory.
Module ExtendedSVHistoryChain.
Section History.
Variable p:Program.
Variables Ghost Input:Type.
Variable advance:Event->State->Ghost->Input->Ghost.
Variable Boundary:Event->State->Input->Prop.
Inductive Execution:State->Ghost->list Event->State->Ghost->Prop:=
| Done pre ghost:Execution pre ghost [] pre ghost
| More ev events pre ghost input post final:
  Boundary ev pre input ->
  Execution (PhaseSemantics p ev pre) (advance ev pre ghost input) events post final ->
  Execution pre ghost (ev::events) post final.
Theorem erases pre ghost events post final:
 Execution pre ghost events post final ->post=phase_run p events pre.
Proof. intro HR;induction HR;[reflexivity|cbn[phase_run];exact IHHR]. Qed.
Variable Related:State->Ghost->Prop.
Hypothesis keep:forall ev pre ghost input,Related pre ghost ->Boundary ev pre input ->
 Related (PhaseSemantics p ev pre) (advance ev pre ghost input).
Theorem preserves pre ghost events post final:
 Execution pre ghost events post final ->Related pre ghost ->Related post final.
Proof. intro HR;induction HR;intro HI;[exact HI|apply IHHR;exact(keep _ _ _ _ HI H)]. Qed.
End History.
Print Assumptions erases.
Print Assumptions preserves.
End ExtendedSVHistoryChain.
