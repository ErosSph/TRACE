(** Static disjoint writer roots certify ORIGINAL process-group independence.
    Source order WITHIN each process (including blocking and last-NBA priority)
    is retained. This proves no LFP convergence or CPU correctness property. *)
From Coq Require Import List Bool Arith.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
 Lang.ExtendedSVProcessSlice Lang.ExtendedSVProcessGroups.
Import ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVProcessGroups ListNotations.
Module ExtendedSVStaticProcessGroups.
Definition roots_disjointb first second:=
 forallb(fun root=>negb(existsb(Nat.eqb root)second))first.
Definition writers_disjointb first second:=roots_disjointb(process_writers first)(process_writers second).
Fixpoint static_process_groups_disjointb order:=match order with
 |[]=>true|proc::rest=>forallb(writers_disjointb proc)rest && static_process_groups_disjointb rest end.
Definition is_sequential proc:=match process_kind proc with Sequential=>true|_=>false end.
Definition sequential_writers_disjointb p:=
 static_process_groups_disjointb(filter is_sequential(processes p)).
Lemma roots_disjointb_sound first second:
 roots_disjointb first second=true->forall root,In root first->~In root second.
Proof.
 intros H root Hin Hsecond. unfold roots_disjointb in H.
 apply forallb_forall with(x:=root)in H;[|exact Hin].
 apply negb_true_iff in H.
 assert(E:existsb(Nat.eqb root)second=true).
 { apply existsb_exists. exists root. split;[exact Hsecond|apply Nat.eqb_refl]. }
 congruence.
Qed.
Lemma writers_disjoint_implies_cross_compatible p s first second:
 writers_disjointb first second=true->
 cross_compatibleb(process_updates p s first)(process_updates p s second)=true.
Proof.
 intros H. unfold cross_compatibleb. apply forallb_forall. intros u Hu.
 apply forallb_forall. intros v Hv.
 assert(Hdifferent:update_signal u<>update_signal v).
 { intro E. unfold writers_disjointb in H.
   apply(roots_disjointb_sound _ _ H(update_signal u)
    (process_emitted_writers p s first u Hu)).
   rewrite E. exact(process_emitted_writers p s second v Hv). }
 unfold updates_compatibleb. rewrite(proj2(Nat.eqb_neq _ _)Hdifferent). reflexivity.
Qed.
Lemma static_process_groups_imply_dynamic p s order:
 static_process_groups_disjointb order=true->
 process_groups_commuteb(map(process_updates p s)order)=true.
Proof.
 induction order as[|proc rest IH];cbn;intro H;[reflexivity|].
 apply andb_true_iff in H as[Hcross Hrest]. apply andb_true_iff. split;[|now apply IH].
 apply forallb_forall. intros group Hin. apply in_map_iff in Hin as[other[<- Hin]].
 apply writers_disjoint_implies_cross_compatible.
 exact(proj1(forallb_forall _ _)Hcross other Hin).
Qed.
Lemma static_disjoint_filter predicate order:
 static_process_groups_disjointb order=true->
 static_process_groups_disjointb(filter predicate order)=true.
Proof.
 induction order as[|proc rest IH];cbn;intro H;[reflexivity|].
 apply andb_true_iff in H as[Hcross Hrest]. destruct(predicate proc);cbn;[|now apply IH].
 apply andb_true_iff. split;[|now apply IH].
 apply forallb_forall. intros other Hin. apply filter_In in Hin as[Hin Hselected].
 exact(proj1(forallb_forall _ _)Hcross other Hin).
Qed.
Lemma selected_transition_is_sequential_filter p old new:
 selected_on_transition p old new=
 filter(process_matches_states old new)(filter is_sequential(processes p)).
Proof.
 assert(Hfilter:forall A(keep eligible:A->bool)xs,
  (forall x,keep x=true->eligible x=true)->filter keep xs=filter keep(filter eligible xs)).
 { intros A keep eligible xs H. induction xs as[|x xs IH];[reflexivity|].
   cbn[filter]. destruct(keep x)eqn:Hx.
   - rewrite(H x Hx). cbn[filter]. rewrite Hx,IH. reflexivity.
   - destruct(eligible x);cbn[filter];rewrite ?Hx;exact IH. }
 unfold selected_on_transition. apply Hfilter.
 intros proc Hselected. unfold process_matches_states in Hselected. unfold is_sequential.
 destruct(process_kind proc);try discriminate;reflexivity.
Qed.
Theorem static_sequential_writers_imply_original_phase_independent p ev pre:
 sequential_writers_disjointb p=true->PhaseIndependentAt p ev pre.
Proof.
 intro Hstatic. apply process_groups_commute_implies_phase_independent.
 unfold ProcessGroupsCommuteAt. apply static_process_groups_imply_dynamic.
 rewrite selected_transition_is_sequential_filter.
 apply static_disjoint_filter. exact Hstatic.
Qed.
End ExtendedSVStaticProcessGroups.
Print Assumptions ExtendedSVStaticProcessGroups.static_sequential_writers_imply_original_phase_independent.
