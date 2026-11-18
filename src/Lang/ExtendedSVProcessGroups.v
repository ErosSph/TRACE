(** Process-order independence with source order INSIDE each process.
    Earlier flat sufficient conditions also compared NBA updates within one
    process, rejecting legal last-assignment priority. This opt-in certificate
    proves the SAME PhaseIndependentAt without altering runtime semantics. *)
From Coq Require Import List Bool Sorting.Permutation.
Require Import Lang.ExtendedSV.
Import ExtendedSV ListNotations.
Module ExtendedSVProcessGroups.

Definition cross_compatibleb (first second : list Update) : bool :=
 forallb (fun u => forallb (updates_compatibleb u) second) first.
Fixpoint process_groups_commuteb (groups : list (list Update)) : bool :=
 match groups with
 | [] => true
 | group :: rest => forallb (cross_compatibleb group) rest && process_groups_commuteb rest
 end.
Definition GroupsCommute (first second : list Update) : Prop :=
 forall s, apply_updates (apply_updates s first) second =
   apply_updates (apply_updates s second) first.
Definition AllGroupsCommute (groups : list (list Update)) : Prop :=
 forall first second, In first groups -> In second groups -> GroupsCommute first second.

Lemma apply_updates_app s first second :
 apply_updates s (first ++ second) = apply_updates (apply_updates s first) second.
Proof. revert s. induction first; intro s; cbn; [reflexivity|apply IHfirst]. Qed.

Lemma move_update_past_group update group :
 (forall u, In u group -> UpdatesCommute u update) ->
 forall s, apply_update (apply_updates s group) update =
   apply_updates (apply_update s update) group.
Proof.
 induction group as [|head rest IH]; intros H s; cbn; [reflexivity|].
 rewrite IH by (intros; apply H; now right).
 rewrite (H head (or_introl eq_refl)). reflexivity.
Qed.

Lemma cross_updates_imply_groups_commute first second :
 (forall u v, In u first -> In v second -> UpdatesCommute u v) ->
 GroupsCommute first second.
Proof.
 induction second as [|head rest IH]; intros H s; cbn; [reflexivity|].
 rewrite move_update_past_group by (intros; apply H; auto; now left).
 apply IH. intros. apply H; auto; now right.
Qed.

Lemma cross_compatibleb_sound first second :
 cross_compatibleb first second = true -> GroupsCommute first second.
Proof.
 intros H. apply cross_updates_imply_groups_commute. intros u v Hu Hv.
 unfold cross_compatibleb in H.
 apply forallb_forall with (x:=u) in H; [|exact Hu].
 apply forallb_forall with (x:=v) in H; [|exact Hv].
 intro s. apply updates_compatibleb_commute. exact H.
Qed.

Theorem process_groups_commuteb_sound groups :
 process_groups_commuteb groups = true -> AllGroupsCommute groups.
Proof.
 induction groups as [|head rest IH]; cbn; intros H first second Hfirst Hsecond.
 - contradiction.
 - apply andb_true_iff in H. destruct H as [Hhead Hrest].
   destruct Hfirst as [<-|Hfirst]; destruct Hsecond as [<-|Hsecond].
   + intro s. reflexivity.
   + apply cross_compatibleb_sound. apply forallb_forall with (x:=second) in Hhead; auto.
   + intro s. symmetry. apply cross_compatibleb_sound.
     apply forallb_forall with (x:=first) in Hhead; auto.
   + apply IH; auto.
Qed.

Lemma all_groups_commute_permutation first second :
 Permutation first second -> AllGroupsCommute first -> AllGroupsCommute second.
Proof.
 intros Hperm H x y Hx Hy. apply H.
 - exact (Permutation_in x (Permutation_sym Hperm) Hx).
 - exact (Permutation_in y (Permutation_sym Hperm) Hy).
Qed.

Theorem apply_process_groups_permutation first second :
 Permutation first second -> AllGroupsCommute first ->
 forall s, apply_updates s (concat first) = apply_updates s (concat second).
Proof.
 intros Hperm. induction Hperm; intros Hall s; cbn.
 - reflexivity.
 - rewrite !apply_updates_app. apply IHHperm.
   intros a b Ha Hb. apply Hall; cbn; auto.
 - rewrite !apply_updates_app. rewrite (Hall x y) by (cbn; auto). reflexivity.
 - rewrite (IHHperm1 Hall s). apply IHHperm2.
   eapply all_groups_commute_permutation; eauto.
Qed.

Definition ProcessGroupsCommuteAt p ev pre : Prop :=
 let driven := phase_driven_state p ev pre in
 process_groups_commuteb
   (map (process_updates p driven) (selected_on_transition p pre driven)) = true.

Theorem process_groups_commute_implies_phase_independent p ev pre :
 ProcessGroupsCommuteAt p ev pre -> PhaseIndependentAt p ev pre.
Proof.
 intros Hcheck order Hperm.
 unfold PhaseSemantics,phase_execute_order,execute_process_order.
 f_equal.
 rewrite !flat_map_concat_map.
 apply apply_process_groups_permutation.
 - apply Permutation_map. exact Hperm.
 - eapply all_groups_commute_permutation.
   + apply Permutation_map. apply Permutation_sym. exact Hperm.
   + apply process_groups_commuteb_sound. exact Hcheck.
Qed.
End ExtendedSVProcessGroups.
Print Assumptions ExtendedSVProcessGroups.process_groups_commute_implies_phase_independent.
