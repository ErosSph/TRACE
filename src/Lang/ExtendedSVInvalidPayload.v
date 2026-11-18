(** Invalid data is not arbitrary when RTL explicitly writes a bubble.
    Pair certificates preserve both guards and their priority. The payload
    theorem is about the ORIGINAL phase, never a replacement evaluator. *)
From Coq Require Import List ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVScalarExpression Lang.ExtendedSVWordInvariant.
Import ListNotations ExtendedSV ExtendedSVScalarHistory
 ExtendedSVScalarExpression ExtendedSVWordInvariant.
Module ExtendedSVInvalidPayload.

Lemma two_phases p first second pre:
 phase_run p[first;second]pre=PhaseSemantics p second(PhaseSemantics p first pre).
Proof. reflexivity. Qed.
Lemma four_phases p first second third fourth pre:
 phase_run p[first;second;third;fourth]pre=
 phase_run p[third;fourth](PhaseSemantics p second(PhaseSemantics p first pre)).
Proof. reflexivity. Qed.

Definition Related width root valid bubble s : Prop :=
 norm 1(read_signal s valid)=0%Z ->norm width(read_signal s root)=norm width bubble.

Inductive Pair width root valid bubble : Expr->Expr->Prop :=
| PairDrop : forall literal, norm width literal=norm width bubble ->
 Pair width root valid bubble(EConst width literal)(EConst 1 0)
| PairFresh : forall data,Pair width root valid bubble data(EConst 1 1)
| PairHold : Pair width root valid bubble(EVar width root)(EVar 1 valid)
| PairSelect : forall guard wy wn vy vn,
 Pair width root valid bubble wy vy ->Pair width root valid bubble wn vn ->
 Pair width root valid bubble(ECond width guard wy wn)(ECond 1 guard vy vn).

Theorem pair_value width root valid bubble word_expr valid_expr
 (certificate:Pair width root valid bubble word_expr valid_expr)s:
 Related width root valid bubble s ->
 norm 1(eval_expr s valid_expr)=0%Z ->norm width(eval_expr s word_expr)=norm width bubble.
Proof.
 intro HI;induction certificate;intro HV.
 - cbn[eval_expr];rewrite norm_idempotent;exact H.
 - change(1%Z=0%Z)in HV;discriminate.
 - cbn[eval_expr]in *;rewrite norm_idempotent in *;exact(HI HV).
 - cbn[eval_expr]in *;rewrite norm_idempotent in *.
   destruct(Z.eqb(eval_expr s guard)0);[exact(IHcertificate2 HV)|exact(IHcertificate1 HV)].
Qed.

Theorem actual_phase p width root valid bubble proc word_expr valid_expr
 (word_certificate:ScalarCertificate p root width proc word_expr)
 (valid_certificate:ScalarCertificate p valid 1 proc valid_expr)
 (pair_certificate:Pair width root valid bubble word_expr valid_expr)ev pre:
 changed_signal ev<>root ->changed_signal ev<>valid ->
 Related width root valid bubble pre ->Related width root valid bubble(PhaseSemantics p ev pre).
Proof.
 intros HW HV HI HPost.
 rewrite(history_phase_projection _ _ _ _ _ valid_certificate ev pre HV)in HPost.
 rewrite(history_phase_projection _ _ _ _ _ word_certificate ev pre HW).
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc)eqn:HF.
 - apply(pair_value width root valid bubble word_expr valid_expr pair_certificate _);[|exact HPost].
   unfold Related;rewrite(sampled_root_preserved p ev pre root(history_comb_frame _ _ _ _ _ word_certificate)HW),
    (sampled_root_preserved p ev pre valid(history_comb_frame _ _ _ _ _ valid_certificate)HV);exact HI.
 - exact(HI HPost).
Qed.

Theorem history p width root valid bubble proc word_expr valid_expr
 (word_certificate:ScalarCertificate p root width proc word_expr)
 (valid_certificate:ScalarCertificate p valid 1 proc valid_expr)
 (pair_certificate:Pair width root valid bubble word_expr valid_expr)events:
 Forall(fun ev=>changed_signal ev<>root /\changed_signal ev<>valid)events ->forall pre,
 Related width root valid bubble pre ->Related width root valid bubble(phase_run p events pre).
Proof.
 intro HE;induction HE as[|ev rest[HW HV]HE IH];intros pre HI;[exact HI|].
 cbn[phase_run];apply IH;exact(actual_phase p width root valid bubble proc word_expr valid_expr
 word_certificate valid_certificate pair_certificate ev pre HW HV HI).
Qed.

Theorem actual_reset p width root valid bubble proc reset normal_word normal_valid
 (word_certificate:ScalarCertificate p root width proc(ECond width reset normal_word(EConst width bubble)))
 (valid_certificate:ScalarCertificate p valid 1 proc(ECond 1 reset normal_valid(EConst 1 0)))ev pre:
 changed_signal ev<>root ->changed_signal ev<>valid ->
 process_matches_states pre(phase_driven_state p ev pre)proc=true ->
 eval_expr(phase_driven_state p ev pre)reset=0%Z ->
 norm width(read_signal(PhaseSemantics p ev pre)root)=norm width bubble /\
 norm 1(read_signal(PhaseSemantics p ev pre)valid)=0%Z.
Proof.
 intros HW HV HF HR;split.
 - rewrite(history_phase_projection _ _ _ _ _ word_certificate ev pre HW),HF.
   cbn[eval_expr];rewrite HR;cbn[Z.eqb];rewrite !norm_idempotent;reflexivity.
 - rewrite(history_phase_projection _ _ _ _ _ valid_certificate ev pre HV),HF.
   cbn[eval_expr];rewrite HR;reflexivity.
Qed.
End ExtendedSVInvalidPayload.
Print Assumptions ExtendedSVInvalidPayload.pair_value.
Print Assumptions ExtendedSVInvalidPayload.actual_phase.
Print Assumptions ExtendedSVInvalidPayload.history.
Print Assumptions ExtendedSVInvalidPayload.actual_reset.
Print Assumptions ExtendedSVInvalidPayload.two_phases.
Print Assumptions ExtendedSVInvalidPayload.four_phases.
