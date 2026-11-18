(** Generic fail-closed shadow replay. The observer can reject a phase, but
    cannot change its RTL transition. No CPU invariant is supplied here. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory.
Import ListNotations ExtendedSV ExtendedSVScalarHistory.
Module ExtendedSVCheckedPhaseReplay.
Section Replay.
Variable p:Program.
Variable Ghost:Type.
Variable observe:Event->State->Ghost->option Ghost.
Fixpoint run events pre ghost:option(State*Ghost):=match events with
| []=>Some(pre,ghost)
| ev::rest=>match observe ev pre ghost with
  | None=>None|Some next=>run rest(PhaseSemantics p ev pre)next end end.

Theorem run_erases events:forall pre ghost post final,
 run events pre ghost=Some(post,final) ->post=phase_run p events pre.
Proof.
 induction events as[|ev rest IH];intros pre ghost post final HS;cbn[run]in HS.
 - inversion HS;reflexivity.
 - cbn[phase_run];destruct(observe ev pre ghost)as[next|]eqn:HC;[|discriminate].
   exact(IH(PhaseSemantics p ev pre)next post final HS).
Qed.

Variable Allowed:Event->State->Prop.
Fixpoint Ready events pre:Prop:=match events with
| []=>True|ev::rest=>Allowed ev pre /\Ready rest(PhaseSemantics p ev pre)end.
Variable Inv:State->Ghost->Prop.
Hypothesis keep:forall ev pre ghost,Allowed ev pre ->Inv pre ghost ->
 exists next,observe ev pre ghost=Some next /\Inv(PhaseSemantics p ev pre)next.
Theorem run_preserves events:forall pre ghost,Ready events pre ->Inv pre ghost ->
 exists post final,run events pre ghost=Some(post,final) /\Inv post final.
Proof.
 induction events as[|ev rest IH];intros pre ghost HR HI.
 - exists pre,ghost;split;[reflexivity|exact HI].
 - destruct HR as[HA HR];destruct(keep ev pre ghost HA HI)as[next[HS Hnext]].
   destruct(IH(PhaseSemantics p ev pre)next HR Hnext)as[post[final[Hrun Hinv]]].
   exists post,final;split;[cbn[run];now rewrite HS|exact Hinv].
Qed.
End Replay.
Example rejected_phase_is_not_accepted p ev pre:
 run p unit(fun _ _ _=>None)[ev]pre tt=None.
Proof. reflexivity. Qed.
Print Assumptions run_erases.
Print Assumptions run_preserves.
Print Assumptions rejected_phase_is_not_accepted.
End ExtendedSVCheckedPhaseReplay.
