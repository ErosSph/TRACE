(** Checked runtime readiness from phase evidence and an explicit state shape.
    No CPU invariant or promise of future architectural correctness is used. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVCheckedPhaseReplay.
Import ListNotations ExtendedSV ExtendedSVScalarHistory.
Module ExtendedSVConstrainedRuntime.
Module Replay:=ExtendedSVCheckedPhaseReplay.

Theorem ready_map p (A B:Event->State->Prop)
 (implies:forall ev pre,A ev pre->B ev pre) events:
 forall pre,Replay.Ready p A events pre->Replay.Ready p B events pre.
Proof.
 induction events as[|ev rest IH];intros pre HR;[exact I|].
 destruct HR as[HA HR];split;[exact(implies ev pre HA)|exact(IH _ HR)].
Qed.

Section Runtime.
Variable p:Program.
Variable Shape:State->Prop.
Variable Condition:Event->State->Prop.
Hypothesis phase_evidence:forall ev pre,Condition ev pre->Shape pre->
 CombLFP p(write_signal pre(changed_signal ev)(new_value ev))(phase_driven_state p ev pre) /\
 (exists seed,CombLFP p seed(PhaseSemantics p ev pre)) /\Shape(PhaseSemantics p ev pre).
Definition Stable pre:=exists seed,CombLFP p seed pre.
Definition Runtime pre:=Shape pre /\Stable pre.
Definition WithLFP ev pre:=Condition ev pre /\Stable pre /\
 CombLFP p(write_signal pre(changed_signal ev)(new_value ev))(phase_driven_state p ev pre).

Theorem phase_runtime ev pre:Condition ev pre->Shape pre->Runtime(PhaseSemantics p ev pre).
Proof. intros HE HS;destruct(phase_evidence ev pre HE HS)as[_[HL HP]];split;assumption. Qed.

Theorem history_runtime events:forall pre,Replay.Ready p Condition events pre->Runtime pre->
 Runtime(phase_run p events pre).
Proof.
 induction events as[|ev rest IH];intros pre HR HI;[exact HI|].
 destruct HR as[HE HR]. cbn[phase_run]. apply IH;[exact HR|].
 exact(phase_runtime ev pre HE(proj1 HI)).
Qed.

Theorem history_ready_with_lfp events:forall pre,Replay.Ready p Condition events pre->Runtime pre->
 Replay.Ready p WithLFP events pre.
Proof.
 induction events as[|ev rest IH];intros pre HR HI;[exact I|].
 destruct HR as[HE HR]. destruct(phase_evidence ev pre HE(proj1 HI))as[HL[HP HS]].
 split.
 - exact(conj HE(conj(proj2 HI)HL)).
 - exact(IH _ HR(conj HS HP)).
Qed.

Theorem nonempty_history_runtime events pre:events<>[]->Replay.Ready p Condition events pre->
 Shape pre->Runtime(phase_run p events pre).
Proof.
 destruct events as[|ev rest];[contradiction|].
 intros _[HE HR]HS. cbn[phase_run]. apply history_runtime;[exact HR|].
 exact(phase_runtime ev pre HE HS).
Qed.
End Runtime.
Print Assumptions ready_map.
Print Assumptions phase_runtime.
Print Assumptions history_runtime.
Print Assumptions history_ready_with_lfp.
Print Assumptions nonempty_history_runtime.
End ExtendedSVConstrainedRuntime.
