(** Validity of an effective write, not validity of arbitrary stale payloads. *)
From Coq Require Import ZArith List.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVScalarExpression Lang.ExtendedSVWordInvariant Lang.ExtendedSVRootProjection.
Import ExtendedSV ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVWordInvariant ExtendedSVRootProjection.
Module ExtendedSVWriteValidity.
Definition Eligible width rd write valid s :=
 norm 1(read_signal s write)<>0%Z ->
 norm width(read_signal s rd)<>0%Z ->norm 1(read_signal s valid)<>0%Z.
Definition InputsEligible width rd write valid s :=
 norm 1(eval_expr s write)<>0%Z ->
 norm width(eval_expr s rd)<>0%Z ->norm 1(eval_expr s valid)<>0%Z.

Lemma enabled_nonzero_guard width write rd s :
 Z.eqb(eval_expr s(EBinary 1 BAnd(EVar 1 write)
   (EBinary 1 BNeq(EConst width 0)(EVar width rd))))0=false ->
 norm 1(read_signal s write)<>0%Z /\norm width(read_signal s rd)<>0%Z.
Proof.
 cbn [eval_expr]. assert(HZ:norm width 0=0%Z)by(unfold norm;apply Z.land_0_l).
 rewrite HZ. intro H;split;intro E.
 - rewrite E in H;cbn in H;discriminate.
 - rewrite E in H;cbn in H;rewrite Z.land_0_r in H;discriminate.
Qed.

Lemma reset_choices width guard rd write valid s :
 InputsEligible width rd write valid s ->
 InputsEligible width (ECond width guard rd(EConst width 0))
   (ECond 1 guard write(EConst 1 0))(ECond 1 guard valid(EConst 1 0))s.
Proof.
 unfold InputsEligible;cbn [eval_expr];rewrite !norm_idempotent.
 destruct(Z.eqb(eval_expr s guard)0);[intros _ H;contradiction H;reflexivity|trivial].
Qed.

Lemma sampled_eligible p width rd write valid ev pre :
 comb_root_unwrittenb p rd=true ->comb_root_unwrittenb p write=true ->
 comb_root_unwrittenb p valid=true ->
 changed_signal ev<>rd ->changed_signal ev<>write ->changed_signal ev<>valid ->
 Eligible width rd write valid pre ->Eligible width rd write valid(phase_driven_state p ev pre).
Proof.
 intros HD HW HV ED EW EV;unfold Eligible.
 rewrite(sampled_root_preserved p ev pre rd HD ED),
 (sampled_root_preserved p ev pre write HW EW),
 (sampled_root_preserved p ev pre valid HV EV);trivial.
Qed.

Theorem actual_stage p width rd write valid proc re we ve
 (rc:ScalarCertificate p rd width proc re)
 (wc:ScalarCertificate p write 1 proc we)
 (vc:ScalarCertificate p valid 1 proc ve) ev pre :
 changed_signal ev<>rd ->changed_signal ev<>write ->changed_signal ev<>valid ->
 Eligible width rd write valid pre ->
 InputsEligible width re we ve(phase_driven_state p ev pre) ->
 Eligible width rd write valid(PhaseSemantics p ev pre).
Proof.
 intros HD HW HV Hold Hin;unfold Eligible.
 rewrite(history_phase_projection _ _ _ _ _ rc ev pre HD),
 (history_phase_projection _ _ _ _ _ wc ev pre HW),
 (history_phase_projection _ _ _ _ _ vc ev pre HV).
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc);assumption.
Qed.

Theorem reset_establishes p width rd write valid proc re we ve
 (rc:ScalarCertificate p rd width proc re)
 (wc:ScalarCertificate p write 1 proc we)
 (vc:ScalarCertificate p valid 1 proc ve) ev pre :
 changed_signal ev<>write ->
 process_matches_states pre(phase_driven_state p ev pre)proc=true ->
 norm 1(eval_expr(phase_driven_state p ev pre)we)=0%Z ->
 Eligible width rd write valid(PhaseSemantics p ev pre).
Proof.
 intros HW HT Hzero;unfold Eligible.
 rewrite(history_phase_projection _ _ _ _ _ wc ev pre HW),HT,Hzero.
 intros H;contradiction H;reflexivity.
Qed.
End ExtendedSVWriteValidity.
Print Assumptions ExtendedSVWriteValidity.actual_stage.
Print Assumptions ExtendedSVWriteValidity.reset_establishes.
