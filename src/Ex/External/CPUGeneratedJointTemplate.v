(** An ordered pending-effect invariant template. This is not a wrapper
    around a CPU's global invariant: its invariant and queue induction are
    constructed here. Instantiation still requires architectural role and
    local physical-transfer evidence, not merely a syntactic writer table. *)
From Coq Require Import List.
Import ListNotations.
Module CPUGeneratedJointTemplate.
Section Template.
Context {Architecture Token Runtime : Type}.
Variable effect : Token -> Architecture -> option Architecture.

Inductive EffectChain : Architecture -> list Token -> Architecture -> Prop :=
| chain_nil : forall a, EffectChain a [] a
| chain_cons : forall a t b ts c,
    effect t a = Some b -> EffectChain b ts c ->
    EffectChain a (t :: ts) c.

Lemma chain_append a xs b ys c :
 EffectChain a xs b -> EffectChain b ys c -> EffectChain a (xs ++ ys) c.
Proof. intros H; induction H; cbn; intros; [assumption|].
 econstructor; eauto. Qed.

Lemma chain_split xs : forall a ys c,
 EffectChain a (xs ++ ys) c ->
 exists b, EffectChain a xs b /\ EffectChain b ys c.
Proof.
 induction xs as [|t xs IH]; intros a ys c H; cbn in H.
 - exists a; split; [constructor|exact H].
 - inversion H as [|a' t' middle ts' c' HE HC]; subst.
   destruct (IH middle ys c HC) as [b [HP HS]].
   exists b; split; [econstructor; eauto|exact HS].
Qed.

Lemma chain_deterministic a ts b c :
 EffectChain a ts b -> EffectChain a ts c -> b = c.
Proof.
 intros H; revert c; induction H; intros target HT;
   inversion HT as [|a' t' b' ts' c' HE' HC']; subst.
 - reflexivity.
 - assert (b = b') by congruence; subst b'.
   eauto.
Qed.

Variable pending : Runtime -> list Token.
Variable Physical : Runtime -> Architecture -> Architecture -> Prop.

(** The hardware bank/PC/memory view may be speculative. The chain is the
    explicit, ordered connection back to the retired architectural state.
    Physical pins BOTH boundaries: a speculative overlay alone can hide
    incorrect retired register values when pending writes overwrite them. *)
Definition Joint (s : Runtime) (retired : Architecture) : Prop :=
 exists frontier, Physical s retired frontier /\
   EffectChain retired (pending s) frontier.

Theorem joint_initial boot initial :
 pending boot = [] -> Physical boot initial initial -> Joint boot initial.
Proof. intros HE HP; exists initial; split; [exact HP|].
 rewrite HE; constructor. Qed.

(** A local cycle certificate exposes the queue operation and the effects
    of newly accepted instructions. It does NOT assume invariant preservation
    or correctness of the retiring prefix; those are derived below.

    [retiring] is an in-order prefix, [kept] its suffix. Flushes may only
    remove tokens whose effects are absent from the certified chain; a CPU
    with speculative wrong-path tokens must supply a separate valid-token
    projection or prove a rollback relation before applying this template. *)
Record QueueTransfer (s post : Runtime) (retired frontier : Architecture)
    (retiring kept accepted_tail : list Token) (next_frontier : Architecture) : Prop := {
 transfer_old_queue : pending s = retiring ++ kept;
 transfer_new_queue : pending post = kept ++ accepted_tail;
 transfer_accepted_effects : EffectChain frontier accepted_tail next_frontier;
 transfer_physical : forall advanced, EffectChain retired retiring advanced ->
   Physical post advanced next_frontier
}.

Theorem ordered_cycle_composition s post retired frontier retiring kept accepted_tail next_frontier :
 Physical s retired frontier ->
 EffectChain retired (pending s) frontier ->
 QueueTransfer s post retired frontier retiring kept accepted_tail next_frontier ->
 exists advanced,
   EffectChain retired retiring advanced /\
   Joint post advanced.
Proof.
 intros Hphysical Hchain [Hold Hnew Hadmit Hpost].
 rewrite Hold in Hchain.
 destruct (chain_split retiring retired kept frontier Hchain)
   as [advanced [Hret Hkept]].
 exists advanced; split; [exact Hret|].
 exists next_frontier; split; [now apply Hpost|].
 rewrite Hnew. eapply chain_append; eassumption.
Qed.

(** The generated obligation only uses present physical boundaries and
    their current pending chain. No old global invariant, future progress or trace refinement
    theorem is supplied to this composition rule. *)
Theorem joint_cycle step retiring :
 (forall s retired frontier, Physical s retired frontier ->
    EffectChain retired (pending s) frontier ->
    exists kept accepted_tail next_frontier,
      QueueTransfer s (step s) retired frontier (retiring s) kept accepted_tail next_frontier) ->
 forall s retired, Joint s retired ->
 exists advanced, EffectChain retired (retiring s) advanced /\
   Joint (step s) advanced.
Proof.
 intros Hlocal s retired [frontier [HP HC]].
 destruct (Hlocal s retired frontier HP HC) as [kept [accepted_tail [next_frontier HT]]].
 eapply ordered_cycle_composition; eassumption.
Qed.

(** Some implementations/segments accept and retire a token in the same
    transition. Retirement is a prefix of OLD++ACCEPTED, not necessarily OLD.
    These equations retain the original token order and never invent a commit.
    Wrong-path invalidation still requires a checked valid-token projection or
    rollback proof; this interface does not simply discard arbitrary effects. *)
Record StreamingTransfer (s post : Runtime) (retired frontier : Architecture)
    (retiring admitted : list Token) (next_frontier : Architecture) : Prop := {
 streaming_queue : pending s ++ admitted = retiring ++ pending post;
 streaming_admitted_effects : EffectChain frontier admitted next_frontier;
 streaming_physical : forall advanced, EffectChain retired retiring advanced ->
   Physical post advanced next_frontier
}.

Theorem queue_to_streaming s post retired frontier retiring kept admitted next_frontier :
 QueueTransfer s post retired frontier retiring kept admitted next_frontier ->
 StreamingTransfer s post retired frontier retiring admitted next_frontier.
Proof.
 intros [Hold Hpost HE HP]; constructor; try assumption.
 rewrite Hold, Hpost. now rewrite app_assoc.
Qed.

Theorem streaming_cycle_composition s post retired frontier retiring admitted next_frontier :
 Physical s retired frontier ->
 EffectChain retired (pending s) frontier ->
 StreamingTransfer s post retired frontier retiring admitted next_frontier ->
 exists advanced, EffectChain retired retiring advanced /\ Joint post advanced.
Proof.
 intros HP HC [HQ HE Hpost].
 pose proof (chain_append _ _ _ _ _ HC HE) as Hwhole.
 rewrite HQ in Hwhole.
 destruct (chain_split retiring retired (pending post) next_frontier Hwhole)
   as [advanced [HR Hremaining]].
 exists advanced; split; [exact HR|].
 exists next_frontier; split; [now apply Hpost|exact Hremaining].
Qed.

Theorem streaming_joint_cycle step retiring :
 (forall s retired frontier, Physical s retired frontier ->
    EffectChain retired (pending s) frontier ->
    exists admitted next_frontier,
      StreamingTransfer s (step s) retired frontier (retiring s) admitted next_frontier) ->
 forall s retired, Joint s retired ->
 exists advanced, EffectChain retired (retiring s) advanced /\ Joint (step s) advanced.
Proof.
 intros Hlocal s retired [frontier [HP HC]].
 destruct (Hlocal s retired frontier HP HC) as [admitted [next_frontier HT]].
 eapply streaming_cycle_composition; eassumption.
Qed.

Theorem joint_architecture (ArchitecturalRel : Runtime -> Architecture -> Prop) :
 (forall s retired frontier, Physical s retired frontier -> ArchitecturalRel s retired) ->
 forall s retired, Joint s retired -> ArchitecturalRel s retired.
Proof. intros HP s retired [frontier [Hphysical Hchain]].
 now apply (HP s retired frontier). Qed.

(** ISA/observation linking is deliberately separated from queue algebra:
    each token effect must be checked against the ORIGINAL ISA transition.
    This lemma reuses those per-token checks for arbitrary retirement width. *)
Section Erasure.
Context {Label : Type}.
Variable label : Token -> Label.
Variable architectural_step : Architecture -> Label -> Architecture -> Prop.
Hypothesis effect_sound : forall t a b,
 effect t a = Some b -> architectural_step a (label t) b.

Inductive ArchitecturalTrace : Architecture -> list Label -> Architecture -> Prop :=
| trace_nil : forall a, ArchitecturalTrace a [] a
| trace_cons : forall a l b ls c,
    architectural_step a l b -> ArchitecturalTrace b ls c ->
    ArchitecturalTrace a (l :: ls) c.

Theorem erase_checked_effects a tokens b :
 EffectChain a tokens b -> ArchitecturalTrace a (map label tokens) b.
Proof. intros H; induction H; cbn; [constructor|].
 econstructor; eauto. Qed.
End Erasure.
End Template.

(** Small executable model regressions, NOT evidence about any CPU. Both
    pipeline depths use the same queue-composition theorem, including a
    two-token retirement prefix. *)
Module Regression.
Definition add_effect (token state : nat) := Some (state + token).
Definition State := (list nat * nat * nat)%type.
Definition queue (s : State) := fst (fst s).
Definition physical (s : State) (retired frontier : nat) :=
 snd (fst s) = retired /\ snd s = frontier.

Example two_depth_cycle :
 exists advanced,
   EffectChain add_effect 0 [1] advanced /\
   Joint add_effect queue physical ([2;3],1,6) advanced.
Proof.
 apply (ordered_cycle_composition add_effect queue physical
   ([1;2],0,3) ([2;3],1,6) 0 3 [1] [2] [3] 6).
 - split; reflexivity.
 - econstructor; [reflexivity|]. econstructor; [reflexivity|constructor].
 - constructor; try reflexivity.
   + econstructor; [reflexivity|constructor].
   + intros advanced HR.
     assert (HA : advanced = 1).
     { eapply chain_deterministic; [exact HR|].
       econstructor; [reflexivity|constructor]. }
     subst; split; reflexivity.
Qed.

Example three_depth_two_retire_cycle :
 exists advanced,
   EffectChain add_effect 0 [1;2] advanced /\
   Joint add_effect queue physical ([3;4],3,10) advanced.
Proof.
 apply (ordered_cycle_composition add_effect queue physical
   ([1;2;3],0,6) ([3;4],3,10) 0 6 [1;2] [3] [4] 10).
 - split; reflexivity.
 - econstructor; [reflexivity|]. econstructor; [reflexivity|].
   econstructor; [reflexivity|constructor].
 - constructor; try reflexivity.
   + econstructor; [reflexivity|constructor].
   + intros advanced HR.
     assert (HA : advanced = 3).
     { eapply chain_deterministic; [exact HR|].
       econstructor; [reflexivity|]. econstructor; [reflexivity|constructor]. }
     subst; split; reflexivity.
Qed.

(** Overwriting effects are noninjective. Matching a speculative frontier
    therefore cannot reconstruct the retired physical bank. *)
Definition overwrite_effect (token _ : nat) := Some token.
Example frontier_only_hides_retired_mismatch :
 7 <> 5 /\
 EffectChain overwrite_effect 7 [9] 9 /\
 EffectChain overwrite_effect 5 [9] 9.
Proof.
 split; [discriminate|]. split.
 - econstructor; [reflexivity|constructor].
 - econstructor; [reflexivity|constructor].
Qed.

Example strengthened_joint_rejects_wrong_bank :
 ~ Joint overwrite_effect queue physical ([9],7,9) 5.
Proof.
 intros [frontier [[Hbank Hfrontier] Hchain]].
 discriminate Hbank.
Qed.

Example accept_and_retire_same_transition :
 exists advanced, EffectChain add_effect 0 [1] advanced /\
   Joint add_effect queue physical ([],1,1) advanced.
Proof.
 apply (streaming_cycle_composition add_effect queue physical
   ([],0,0) ([],1,1) 0 0 [1] [1] 1).
 - split; reflexivity.
 - constructor.
 - constructor; [reflexivity| |].
   + econstructor; [reflexivity|constructor].
   + intros advanced HA.
     assert (advanced=1).
     { eapply chain_deterministic; [exact HA|].
       econstructor; [reflexivity|constructor]. }
     subst; split; reflexivity.
Qed.

Example old_prefix_rule_cannot_retire_new_token :
 ~ exists kept, queue ([],0,0) = [1] ++ kept.
Proof. intros [kept H]; discriminate. Qed.

Example retire_old_and_new_in_order :
 exists advanced, EffectChain add_effect 0 [1;2] advanced /\
   Joint add_effect queue physical ([3],3,6) advanced.
Proof.
 apply (streaming_cycle_composition add_effect queue physical
   ([1],0,1) ([3],3,6) 0 1 [1;2] [2;3] 6).
 - split; reflexivity.
 - econstructor; [reflexivity|constructor].
 - constructor; [reflexivity| |].
   + econstructor; [reflexivity|]. econstructor; [reflexivity|constructor].
   + intros advanced HA.
     assert (advanced=3).
     { eapply chain_deterministic; [exact HA|].
       econstructor; [reflexivity|]. econstructor; [reflexivity|constructor]. }
     subst; split; reflexivity.
Qed.

Example frontier_only_predicate_accepts_wrong_bank :
 exists frontier,
   snd (([9],7,9) : State) = frontier /\
   EffectChain overwrite_effect 5 (queue ([9],7,9)) frontier.
Proof. exists 9; split; [reflexivity|].
 econstructor; [reflexivity|constructor]. Qed.
End Regression.
Print Assumptions joint_initial.
Print Assumptions ordered_cycle_composition.
Print Assumptions joint_cycle.
Print Assumptions joint_architecture.
Print Assumptions erase_checked_effects.
Print Assumptions queue_to_streaming.
Print Assumptions streaming_cycle_composition.
Print Assumptions streaming_joint_cycle.
End CPUGeneratedJointTemplate.
