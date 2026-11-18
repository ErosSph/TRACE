(** A deterministic progress certificate compiler.  A backend proves that
    bounded search succeeds on the generated invariant; the rank and its
    silent-cycle decrease are then derived, not supplied by an LLM.
    No bound or response guarantee is silently imposed on an original target. *)
From Coq Require Import Arith Lia ZArith.
Require Import Ex.External.CV32E40PTwoCommitITreeInterface.
Import CV32E40PTwoCommitITreeInterface.
Module CPUGeneratedProgress.
Section Search.
Context {State Architecture : Type}.
Variable step : State -> State.
Variable observe : State -> CycleCommits.

Fixpoint first_commit (fuel : nat) (s : State) : option nat :=
 match fuel with
 | O => match observe s with SilentCycle => None | _ => Some O end
 | S remaining => match observe s with
   | SilentCycle => option_map S (first_commit remaining (step s))
   | _ => Some O
   end
 end.

Lemma first_commit_unfold fuel s :
 first_commit fuel s =
 match observe s with
 | SilentCycle => match fuel with
   | O => None | S remaining => option_map S (first_commit remaining (step s)) end
 | _ => Some O
 end.
Proof. destruct fuel; reflexivity. Qed.

Inductive FirstCommitAt : State -> nat -> Prop :=
| commit_now s : observe s <> SilentCycle -> FirstCommitAt s O
| commit_later s n : observe s = SilentCycle ->
    FirstCommitAt (step s) n -> FirstCommitAt s (S n).

Theorem first_commit_sound fuel : forall s distance,
 first_commit fuel s = Some distance ->
 FirstCommitAt s distance /\ distance <= fuel.
Proof.
 induction fuel as [|fuel IH]; intros s distance H;
 rewrite first_commit_unfold in H;
 destruct (observe s) eqn:HO; cbn in H.
 - discriminate.
 - inversion H; subst. split; [constructor; congruence|lia].
 - inversion H; subst. split; [constructor; congruence|lia].
 - destruct (first_commit fuel (step s)) as [d|] eqn:HS; [|discriminate].
   inversion H; subst distance.
   destruct (IH _ _ HS) as [HP HB]. split; [constructor; assumption|lia].
 - inversion H; subst. split; [constructor; congruence|lia].
 - inversion H; subst. split; [constructor; congruence|lia].
Qed.

Lemma first_commit_extend fuel : forall s distance,
 first_commit fuel s = Some distance ->
 first_commit (S fuel) s = Some distance.
Proof.
 induction fuel as [|fuel IH]; intros s distance H;
 rewrite (first_commit_unfold _ s) in H;
 rewrite (first_commit_unfold _ s);
 destruct (observe s) eqn:HO; cbn -[first_commit] in H |- *.
 - discriminate.
 - exact H.
 - exact H.
 - destruct (first_commit fuel (step s)) as [d|] eqn:HS; [|discriminate].
   inversion H; subst distance. now rewrite (IH _ _ HS).
 - exact H.
 - exact H.
Qed.

Definition search_rank fuel s : nat :=
 match first_commit fuel s with Some distance => distance | None => O end.

Theorem search_rank_silent_decreases fuel s distance :
 first_commit fuel s = Some distance -> observe s = SilentCycle ->
 search_rank fuel (step s) < search_rank fuel s.
Proof.
 intros H HS. destruct fuel as [|fuel].
 - rewrite first_commit_unfold, HS in H. discriminate.
 - pose proof H as Hfound.
   rewrite first_commit_unfold, HS in H.
   destruct (first_commit fuel (step s)) as [d|] eqn:HD; [|discriminate].
   inversion H; subst distance.
   pose proof (first_commit_extend fuel (step s) d HD) as HE.
   unfold search_rank. rewrite Hfound, HE. lia.
Qed.

Definition BoundedProgress (fuel : nat) (Joint : State -> Architecture -> Prop) : Prop :=
 forall s a, Joint s a -> exists distance, first_commit fuel s = Some distance.

Theorem bounded_progress_rank fuel Joint :
 BoundedProgress fuel Joint ->
 forall s a, Joint s a -> observe s = SilentCycle ->
 search_rank fuel (step s) < search_rank fuel s.
Proof.
 intros HB s a Hjoint Hsilent.
 destruct (HB s a Hjoint) as [distance HD].
 eapply search_rank_silent_decreases; eassumption.
Qed.

(** Reuse path for an existing local rank proof. This is not rank discovery:
    an old well-founded witness and a PROVED uniform bound discharge search
    completeness. New backends may instead prove bounded search directly. *)
Theorem ranked_search_complete
 (Joint : State -> Architecture -> Prop) (rank : State -> Architecture -> nat)
 (Hsilent : forall s a, Joint s a -> observe s = SilentCycle -> Joint (step s) a)
 (Hdecrease : forall s a, Joint s a -> observe s = SilentCycle -> rank (step s) a < rank s a) :
 forall fuel s a, Joint s a -> rank s a <= fuel ->
 exists distance, first_commit fuel s = Some distance.
Proof.
 induction fuel as [|fuel IH]; intros s a HJ HB;
 rewrite first_commit_unfold;
 destruct (observe s) eqn:HO.
 - pose proof (Hdecrease _ _ HJ HO). lia.
 - exists O; reflexivity.
 - exists O; reflexivity.
 - destruct (IH (step s) a (Hsilent _ _ HJ HO)
     ltac:(pose proof (Hdecrease _ _ HJ HO); lia)) as [d HD].
   exists (S d). now rewrite HD.
 - exists O; reflexivity.
 - exists O; reflexivity.
Qed.
End Search.

Module Regression.
Definition countdown_observer (s : nat) : CycleCommits :=
 match s with O => OneCommit 0%Z | S _ => SilentCycle end.

Example three_silent_cycles :
 first_commit Nat.pred countdown_observer 3 3 = Some 3.
Proof. reflexivity. Qed.

Example automatic_decrease :
 search_rank Nat.pred countdown_observer 3 2 <
 search_rank Nat.pred countdown_observer 3 3.
Proof.
 apply (search_rank_silent_decreases Nat.pred countdown_observer 3 3 3);
 reflexivity.
Qed.

Example permanent_stall_rejected fuel :
 first_commit (fun s : nat => s) (fun _ => SilentCycle) fuel 0 = None.
Proof. induction fuel; cbn; [reflexivity|now rewrite IHfuel]. Qed.
End Regression.
Print Assumptions first_commit_sound.
Print Assumptions search_rank_silent_decreases.
Print Assumptions bounded_progress_rank.
Print Assumptions ranked_search_complete.
End CPUGeneratedProgress.
