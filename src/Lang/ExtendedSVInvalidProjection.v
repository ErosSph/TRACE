(** Inactive payloads may be nonzero NOP encodings. Only their observed
    projection must be zero. No ISA instruction identity is assumed. *)
From Coq Require Import ZArith List.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVScalarExpression Lang.ExtendedSVRootProjection Lang.ExtendedSVWordInvariant.
Import ExtendedSV ExtendedSVScalarHistory ExtendedSVScalarExpression
 ExtendedSVRootProjection ExtendedSVWordInvariant.
Module ExtendedSVInvalidProjection.
Definition Related width payload valid (project:Z->Z) s:=
 norm 1(read_signal s valid)=0%Z ->project(norm width(read_signal s payload))=0%Z.
Lemma choice_zero width project guard wy wn vy vn s:
 (norm 1(eval_expr s vy)=0%Z ->project(norm width(eval_expr s wy))=0%Z) ->
 (norm 1(eval_expr s vn)=0%Z ->project(norm width(eval_expr s wn))=0%Z) ->
 norm 1(eval_expr s(ECond 1 guard vy vn))=0%Z ->
 project(norm width(eval_expr s(ECond width guard wy wn)))=0%Z.
Proof.
 intros HY HN;cbn[eval_expr];rewrite !norm_idempotent;
 destruct(Z.eqb(eval_expr s guard)0);assumption.
Qed.
Theorem phase_preserves p width payload valid proc word bit project
 (wc:ScalarCertificate p payload width proc word)
 (vc:ScalarCertificate p valid 1 proc bit)
 (local_rule:forall s,Related width payload valid project s ->
  norm 1(eval_expr s bit)=0%Z ->project(norm width(eval_expr s word))=0%Z)
 ev pre:
 changed_signal ev<>payload ->changed_signal ev<>valid ->
 Related width payload valid project pre ->Related width payload valid project(PhaseSemantics p ev pre).
Proof.
 intros HE HV HI;unfold Related.
 rewrite(history_phase_projection _ _ _ _ _ vc ev pre HV).
 rewrite(history_phase_projection _ _ _ _ _ wc ev pre HE).
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc);[|exact HI].
 apply local_rule;unfold Related.
 rewrite(sampled_root_preserved p ev pre payload(history_comb_frame _ _ _ _ _ wc)HE).
 rewrite(sampled_root_preserved p ev pre valid(history_comb_frame _ _ _ _ _ vc)HV).
 exact HI.
Qed.
Theorem history_preserves p width payload valid proc word bit project
 (wc:ScalarCertificate p payload width proc word)
 (vc:ScalarCertificate p valid 1 proc bit)
 (local_rule:forall s,Related width payload valid project s ->
  norm 1(eval_expr s bit)=0%Z ->project(norm width(eval_expr s word))=0%Z) events:
 Forall(fun ev=>changed_signal ev<>payload /\changed_signal ev<>valid)events ->
 forall pre,Related width payload valid project pre ->
 Related width payload valid project(phase_run p events pre).
Proof.
 intro HE;induction HE as[|ev rest[HP HV]HT IH];intros pre HR;[exact HR|].
 cbn[phase_run];apply IH.
 exact(phase_preserves p width payload valid proc word bit project wc vc local_rule ev pre HP HV HR).
Qed.
End ExtendedSVInvalidProjection.
Print Assumptions ExtendedSVInvalidProjection.phase_preserves.
Print Assumptions ExtendedSVInvalidProjection.history_preserves.
