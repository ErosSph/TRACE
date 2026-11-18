(** Append auxiliary observations along the SAME real phase execution. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVRuntimeHistory.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVRuntimeHistory.
Module ExtendedSVRuntimeAppend.

Theorem replay_append p Ghost advance left right pre (ghost:Ghost):
 replay p Ghost advance(left++right)pre ghost=
 replay p Ghost advance right(phase_run p left pre)(replay p Ghost advance left pre ghost).
Proof.
 revert pre ghost;induction left as[|ev rest IH];intros pre ghost;cbn[replay phase_run app];
 [reflexivity|apply IH].
Qed.

Theorem replay_one_more p Ghost advance events ev pre (ghost:Ghost):
 replay p Ghost advance(events++[ev])pre ghost=
 advance ev(phase_run p events pre)(replay p Ghost advance events pre ghost)tt.
Proof. rewrite replay_append;reflexivity. Qed.
End ExtendedSVRuntimeAppend.
Print Assumptions ExtendedSVRuntimeAppend.replay_append.
Print Assumptions ExtendedSVRuntimeAppend.replay_one_more.
