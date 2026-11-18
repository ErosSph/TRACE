(** Checked single-root slicing of complete NBA plans. Guards, case priority,
    sampled RHS values and assignment order are unchanged. At zero fuel the
    original plan is retained, not discarded: soundness needs no depth bound. *)
From Coq Require Import List ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
 Lang.ExtendedSVAutoAdapterPlan Lang.ExtendedSVAutoAdapterPhase.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice
 ExtendedSVAutoAdapterPlan ExtendedSVAutoAdapterPhase.
Module ExtendedSVPlanRootSlice.

Fixpoint slice_plan (fuel : nat) (root : signal) (plan : NbPlan) : NbPlan :=
 match fuel with
 | O => plan
 | S f => match plan with
   | NEmpty => NEmpty
   | NAssign rhs lhs =>
       if Nat.eqb (lvalue_root lhs) root then NAssign rhs lhs else NEmpty
   | NSeq plans => NSeq (map (slice_plan f root) plans)
   | NIf guard yes no => NIf guard (slice_plan f root yes) (slice_plan f root no)
   | NCase scrutinee arms => NCase scrutinee
       (map (fun arm => (fst arm, slice_plan f root (snd arm))) arms)
   end
 end.

Definition case_updates (s : State) (value : Z)
    (arms : list (option Expr * NbPlan)) (default : list Update) :=
 let fix select xs d :=
   match xs with
   | [] => d
   | (None,p) :: rest => select rest (eval_plan s p)
   | (Some key,p) :: rest =>
       if Z.eqb value (eval_expr s key) then eval_plan s p else select rest d
   end in select arms default.

Lemma case_map_projection f s value root old :
 (forall plan, apply_updates_root_value root old (eval_plan s (f plan)) =
    apply_updates_root_value root old (eval_plan s plan)) ->
 forall arms dl dr,
 apply_updates_root_value root old dl = apply_updates_root_value root old dr ->
 apply_updates_root_value root old
   (case_updates s value (map (fun arm => (fst arm, f (snd arm))) arms) dl) =
 apply_updates_root_value root old (case_updates s value arms dr).
Proof.
 intros H. induction arms as [|[key body] rest IH]; intros dl dr HD;
   cbn [map fst snd case_updates]; [exact HD|].
 destruct key as [key|]; cbn.
 - destruct (Z.eqb value (eval_expr s key)); [apply H|now apply IH].
 - apply IH. apply H.
Qed.

Theorem slice_plan_sound fuel : forall root plan s old,
 apply_updates_root_value root old (eval_plan s (slice_plan fuel root plan)) =
 apply_updates_root_value root old (eval_plan s plan).
Proof.
 induction fuel as [|f IH]; intros root plan s old; [reflexivity|].
 destruct plan as [|rhs lhs|plans|guard yes no|scrutinee arms];
   cbn [slice_plan eval_plan]; try reflexivity.
 - destruct (Nat.eqb (lvalue_root lhs) root) eqn:HE; [reflexivity|].
   cbn [eval_plan apply_updates_root_value].
   unfold apply_update_root_value. rewrite resolve_update_root, HE. reflexivity.
 - induction plans as [|plan rest IHr] in old |- *;
     cbn [map flat_map]; [reflexivity|].
   rewrite !apply_root_app, IH. apply IHr.
 - destruct (Z.eqb (eval_expr s guard) 0); apply IH.
 - change (apply_updates_root_value root old
     (case_updates s (eval_expr s scrutinee)
       (map (fun arm => (fst arm, slice_plan f root (snd arm))) arms) []) =
     apply_updates_root_value root old
       (case_updates s (eval_expr s scrutinee) arms [])).
   apply case_map_projection; [intro plan; apply IH|reflexivity].
Qed.

(** Complete actual phase writer chains can use the sliced plans without
    constructing another CPU state or assuming any architectural invariant. *)
Definition sliced_transition_updates fuel root old driven entries :=
 flat_map (fun entry : Process * NbPlan =>
   if process_matches_states old driven (fst entry)
   then eval_plan driven (slice_plan fuel root (snd entry)) else []) entries.

Lemma sliced_transition_sound fuel root old driven entries value :
 apply_updates_root_value root value
   (sliced_transition_updates fuel root old driven entries) =
 apply_updates_root_value root value (plan_transition_updates old driven entries).
Proof.
 induction entries as [|[proc plan] rest IH] in value |- *;
   cbn [sliced_transition_updates plan_transition_updates flat_map fst snd];
   [reflexivity|].
 destruct (process_matches_states old driven proc); cbn.
 - rewrite !apply_root_app, slice_plan_sound. apply IH.
 - apply IH.
Qed.

Theorem checked_sliced_phase p root entries fuel :
 PlanRootCertificate p root entries -> forall ev pre,
 changed_signal ev <> root ->
 read_signal (PhaseSemantics p ev pre) root =
 apply_updates_root_value root (read_signal pre root)
   (sliced_transition_updates fuel root pre (phase_driven_state p ev pre) entries).
Proof.
 intros HC ev pre HE. rewrite sliced_transition_sound.
 exact (planned_phase_root p root entries HC ev pre HE).
Qed.

Print Assumptions slice_plan_sound.
Print Assumptions sliced_transition_sound.
Print Assumptions checked_sliced_phase.
End ExtendedSVPlanRootSlice.
