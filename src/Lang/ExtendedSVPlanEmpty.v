(** A shared, reflected no-update certificate for sliced NBA plans.
    In particular an empty branch need not inspect any CPU guard value. *)
From Coq Require Import List ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
 Lang.ExtendedSVAutoAdapterPlan Lang.ExtendedSVPlanRootSlice.
Import ListNotations ExtendedSV ExtendedSVRootProjection
 ExtendedSVAutoAdapterPlan ExtendedSVPlanRootSlice.
Module ExtendedSVPlanEmpty.

Fixpoint plan_emptyb (fuel : nat) (plan : NbPlan) : bool :=
 match fuel with
 | O => false
 | S f => match plan with
   | NEmpty => true
   | NAssign _ _ => false
   | NSeq plans => forallb (plan_emptyb f) plans
   | NIf _ yes no => plan_emptyb f yes && plan_emptyb f no
   | NCase _ arms => forallb (fun arm => plan_emptyb f (snd arm)) arms
   end
 end.

Theorem empty_plan_sound fuel : forall plan s,
 plan_emptyb fuel plan = true -> eval_plan s plan = [].
Proof.
 induction fuel as [|f IH]; intros plan s H; [discriminate|].
 destruct plan as [|rhs lhs|plans|guard yes no|scrutinee arms];
   cbn [plan_emptyb] in H.
 - reflexivity.
 - discriminate.
 - cbn [eval_plan]. induction plans as [|plan rest IHr]; [reflexivity|].
   cbn [forallb] in H. apply andb_true_iff in H as [HP HR].
   cbn [flat_map]. rewrite (IH plan s HP), (IHr HR). reflexivity.
 - apply andb_true_iff in H as [HY HN]. cbn [eval_plan].
   destruct (Z.eqb (eval_expr s guard) 0); apply IH; assumption.
 - change (case_updates s (eval_expr s scrutinee) arms [] = []).
   induction arms as [|[key body] rest IHr]; [reflexivity|].
   cbn [forallb snd] in H. apply andb_true_iff in H as [HB HR].
   cbn [case_updates]. destruct key as [key|]; cbn.
   + destruct (Z.eqb (eval_expr s scrutinee) (eval_expr s key)).
     * exact (IH body s HB).
     * exact (IHr HR).
   + rewrite (IH body s HB). exact (IHr HR).
Qed.

Print Assumptions empty_plan_sound.

Corollary empty_plan_keeps_root fuel plan s root old :
 plan_emptyb fuel plan = true ->
 apply_updates_root_value root old (eval_plan s plan) = old.
Proof. intro H. rewrite (empty_plan_sound fuel plan s H). reflexivity. Qed.
Print Assumptions empty_plan_keeps_root.
End ExtendedSVPlanEmpty.
