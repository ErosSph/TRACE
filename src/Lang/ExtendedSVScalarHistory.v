(** An automatically instantiable field-history simulation. The local model
    carries its own previous value; that field is erased from each sampled
    input frame before replay. Actual process selection and OTHER sampled
    inputs remain observations, not assumed ISA/controller correctness. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVExprAgreement
 Lang.ExtendedSVScalarExpression Lang.ExtendedSVWordInvariant.
Import ExtendedSV ExtendedSVRootProjection ExtendedSVExprAgreement ExtendedSVScalarExpression
 ExtendedSVWordInvariant ListNotations.
Module ExtendedSVScalarHistory.

Definition self_widthb width root expression :=
 forallb (fun input => if Nat.eqb (snd input) root
   then Nat.eqb (fst input) width else true) (expr_inputs expression).

Lemma self_width_checked width root expression : self_widthb width root expression=true ->
 forall w, In (w,root) (expr_inputs expression) -> w=width.
Proof.
 unfold self_widthb; intros H w HI.
 apply forallb_forall with (x:=(w,root)) in H; [|exact HI].
 cbn in H. rewrite Nat.eqb_refl in H. now apply Nat.eqb_eq.
Qed.

Record ScalarCertificate (p : Program) root width (proc : Process) expression : Prop := {
 history_comb_frame : comb_root_unwrittenb p root=true;
 history_self_width : self_widthb width root expression=true;
 history_phase_projection : forall ev pre, changed_signal ev<>root ->
  norm width (read_signal (PhaseSemantics p ev pre) root)=
  if process_matches_states pre (phase_driven_state p ev pre) proc
  then norm width (eval_expr (phase_driven_state p ev pre) expression)
  else norm width (read_signal pre root)
}.

Definition Frame := (State * bool)%type.
Definition frame_for p proc root ev pre : Frame :=
 (write_signal (phase_driven_state p ev pre) root 0,
  process_matches_states pre (phase_driven_state p ev pre) proc).
Definition local_step width root expression (old : Z) (frame : Frame) : Z :=
 if snd frame then
  norm width (eval_expr (write_signal (fst frame) root old) expression)
 else old.
Definition Related width root (concrete : State) (local : Z) : Prop :=
 norm width (read_signal concrete root)=local.

Lemma erased_frame_has_no_old_value p proc root ev pre :
 read_signal (fst (frame_for p proc root ev pre)) root=0%Z.
Proof. unfold frame_for; cbn [fst]. apply read_signal_write_same. Qed.

Theorem history_initial width root pre :
 Related width root pre (norm width (read_signal pre root)).
Proof. reflexivity. Qed.

Theorem history_step p root width proc expression
 (certificate : ScalarCertificate p root width proc expression) ev pre old :
 changed_signal ev<>root -> Related width root pre old ->
 Related width root (PhaseSemantics p ev pre)
  (local_step width root expression old (frame_for p proc root ev pre)).
Proof.
 intros HE HR. unfold Related in *.
 unfold local_step,frame_for; cbn [fst snd].
 rewrite write_signal_write_same.
 rewrite (history_phase_projection _ _ _ _ _ certificate ev pre HE).
 destruct (process_matches_states pre (phase_driven_state p ev pre) proc).
 - f_equal. apply eval_expr_agree. intros w x HI.
   destruct (Nat.eq_dec x root) as [HX|HX].
   + subst x.
     pose proof (self_width_checked _ _ _ (history_self_width _ _ _ _ _ certificate) w HI) as HW.
     subst w. rewrite read_signal_write_same.
     rewrite (sampled_root_preserved p ev pre root
       (history_comb_frame _ _ _ _ _ certificate) HE).
     rewrite <- HR, norm_idempotent. reflexivity.
   + rewrite read_signal_write_other by congruence. reflexivity.
 - exact HR.
Qed.

Fixpoint phase_run p events pre := match events with
 | []=>pre | ev::tail=>phase_run p tail (PhaseSemantics p ev pre) end.
Fixpoint observed_frames p proc root events pre := match events with
 | []=>[] | ev::tail=>frame_for p proc root ev pre ::
   observed_frames p proc root tail (PhaseSemantics p ev pre) end.
Fixpoint local_run width root expression frames old := match frames with
 | []=>old | frame::tail=>local_run width root expression tail
    (local_step width root expression old frame) end.

Theorem history_sequence p root width proc expression
 (certificate : ScalarCertificate p root width proc expression) events :
 Forall (fun ev=>changed_signal ev<>root) events ->
 forall pre old, Related width root pre old ->
 Related width root (phase_run p events pre)
  (local_run width root expression (observed_frames p proc root events pre) old).
Proof.
 intro HE; induction HE as [|ev events Hhead Htail IH]; intros pre old HR.
 - exact HR.
 - cbn [phase_run observed_frames local_run]. apply IH.
   exact (history_step p root width proc expression certificate ev pre old Hhead HR).
Qed.

Corollary history_from_initial p root width proc expression
 (certificate : ScalarCertificate p root width proc expression) events pre :
 Forall (fun ev=>changed_signal ev<>root) events ->
 norm width (read_signal (phase_run p events pre) root)=
 local_run width root expression (observed_frames p proc root events pre)
  (norm width (read_signal pre root)).
Proof. intro HE. exact (history_sequence p root width proc expression certificate
 events HE pre _ (history_initial width root pre)). Qed.
End ExtendedSVScalarHistory.
Print Assumptions ExtendedSVScalarHistory.self_width_checked.
Print Assumptions ExtendedSVScalarHistory.erased_frame_has_no_old_value.
Print Assumptions ExtendedSVScalarHistory.history_initial.
Print Assumptions ExtendedSVScalarHistory.history_step.
Print Assumptions ExtendedSVScalarHistory.history_sequence.
Print Assumptions ExtendedSVScalarHistory.history_from_initial.
