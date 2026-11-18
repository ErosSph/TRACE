(** Endogenous capture labels, derived from actual sampled data.
    These are capture identities, not yet ISA admissions or retirements. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVInstructionOrigin Lang.ExtendedSVRecipeCoverage
 Lang.ExtendedSVCoveredField Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression
 Lang.ExtendedSVWordInvariant Lang.ExtendedSVRootProjection Lang.ExtendedSVConstantRoot.
Import ListNotations ExtendedSV ExtendedSVInstructionOrigin ExtendedSVRecipeCoverage
 ExtendedSVCoveredField ExtendedSVScalarHistory ExtendedSVScalarExpression
 ExtendedSVWordInvariant ExtendedSVRootProjection ExtendedSVConstantRoot.
Module ExtendedSVCaptureBirth.

Record Token:Type:={token_id:nat;token_word:Z;token_pc:option Z}.
Definition word_reference(t:Token):=norm 32(token_word t).
Inductive Decision:=Keep|Drop|Accept(source:signal).
Definition decide root word valid s :=
 if Z.eqb(norm 1(eval_expr s valid))0 then Drop else
 match copy_source s word with None=>Drop|Some source=>
 if Nat.eqb source root then Keep else Accept source end.
Definition fresh serial s source(pc:State->signal->option Z):Token:=
 Build_Token serial(norm 32(read_signal s source))(pc s source).
Definition next_tag decision serial s pc(old:option Token):=match decision with
| Keep=>old|Drop=>None|Accept source=>Some(fresh serial s source pc)end.
Definition next_serial decision serial:=match decision with Accept _=>S serial|_=>serial end.
Definition birth decision serial s pc:=match decision with Accept source=>Some(fresh serial s source pc)|_=>None end.

Inductive BirthMatches root validroot:Expr->Expr->Prop:=
| BirthInvalid:forall word,BirthMatches root validroot word(EConst 1 0)
| BirthHold:forall valid,RequiresBit validroot valid ->BirthMatches root validroot(EVar 32 root)valid
| BirthFresh:forall source valid,source<>root ->BirthMatches root validroot(EVar 32 source)valid
| BirthSelect:forall guard wy wn vy vn,
 BirthMatches root validroot wy vy ->BirthMatches root validroot wn vn ->
 BirthMatches root validroot(ECond 32 guard wy wn)(ECond 1 guard vy vn).

Theorem decision_coverage root validroot word valid
 (certificate:BirthMatches root validroot word valid)s serial pc old:
 (norm 1(read_signal s validroot)<>0%Z ->exists label,old=Some label) ->
 norm 1(eval_expr s valid)<>0%Z ->
 exists label,next_tag(decide root word valid s)serial s pc old=Some label.
Proof.
 intros Hold;induction certificate;intro HV.
 - cbn[eval_expr norm]in HV;contradiction.
 - assert(HB:Z.eqb(norm 1(eval_expr s valid))0=false)by(now apply Z.eqb_neq).
   unfold decide;rewrite HB;cbn[copy_source];rewrite !Nat.eqb_refl;cbn[next_tag].
   apply Hold;exact(requires_bit_sound _ _ H s HV).
 - assert(HB:Z.eqb(norm 1(eval_expr s valid))0=false)by(now apply Z.eqb_neq).
   unfold decide;rewrite HB;cbn[copy_source];rewrite !Nat.eqb_refl.
   assert(HE:Nat.eqb source root=false)by(now apply Nat.eqb_neq).
   rewrite HE;exists(fresh serial s source pc);reflexivity.
 - unfold decide;cbn[eval_expr copy_source]in *;rewrite norm_idempotent in *.
   destruct(Z.eqb(eval_expr s guard)0);[now apply IHcertificate2|now apply IHcertificate1].
Qed.

Theorem decision_value root word valid s serial pc old label:
 (forall l,old=Some l ->norm 32(read_signal s root)=word_reference l) ->
 next_tag(decide root word valid s)serial s pc old=Some label ->
 norm 32(eval_expr s word)=word_reference label.
Proof.
 intros Hold HT;unfold decide in HT.
 destruct(Z.eqb(norm 1(eval_expr s valid))0);[discriminate|].
 destruct(copy_source s word)as[source|]eqn:HC;[|discriminate].
 rewrite(copy_source_sound word s source HC),norm_idempotent.
 destruct(Nat.eqb source root)eqn:HE.
 - apply Nat.eqb_eq in HE;subst source;now apply Hold.
 - inversion HT;subst label;unfold word_reference,fresh;cbn[token_word];symmetry;apply norm_idempotent.
Qed.

Definition phase_decision p proc root word valid ev pre:=
 if process_matches_states pre(phase_driven_state p ev pre)proc
 then decide root word valid(phase_driven_state p ev pre)else Keep.
Definition phase_tag p proc root word valid ev pre serial pc old:=
 next_tag(phase_decision p proc root word valid ev pre)serial(phase_driven_state p ev pre)pc old.

Theorem actual_birth_related p root validroot proc word valid
 (word_certificate:ScalarCertificate p root 32 proc word)
 (valid_certificate:ScalarCertificate p validroot 1 proc valid)
 (certificate:BirthMatches root validroot word valid)ev pre serial pc old:
 changed_signal ev<>root ->changed_signal ev<>validroot ->
 ExtendedSVCoveredField.Related 32 root validroot word_reference old pre ->
 ExtendedSVCoveredField.Related 32 root validroot word_reference
  (phase_tag p proc root word valid ev pre serial pc old)(PhaseSemantics p ev pre).
Proof.
 intros HE HV[Hcover Hvalue];constructor.
 - rewrite(history_phase_projection _ _ _ _ _ valid_certificate ev pre HV).
   unfold phase_tag,phase_decision.
   destruct(process_matches_states pre(phase_driven_state p ev pre)proc).
   + apply(decision_coverage root validroot word valid certificate
      (phase_driven_state p ev pre)serial pc old).
     rewrite(sampled_root_preserved p ev pre validroot
      (history_comb_frame _ _ _ _ _ valid_certificate)HV);exact Hcover.
   + exact Hcover.
 - intros label HT;rewrite(history_phase_projection _ _ _ _ _ word_certificate ev pre HE).
   unfold phase_tag,phase_decision in HT.
   destruct(process_matches_states pre(phase_driven_state p ev pre)proc).
   + eapply decision_value;[|exact HT].
     intros l Hl;rewrite(sampled_root_preserved p ev pre root
       (history_comb_frame _ _ _ _ _ word_certificate)HE);exact(Hvalue l Hl).
   + exact(Hvalue label HT).
Qed.

Theorem serial_monotone decision serial:(serial<=next_serial decision serial)%nat.
Proof. destruct decision;cbn[next_serial];lia. Qed.

Theorem tag_id_range decision serial s pc old:
 (forall label,old=Some label ->(token_id label<serial)%nat) ->
 forall label,next_tag decision serial s pc old=Some label ->
 (token_id label<next_serial decision serial)%nat.
Proof.
 intros Hold label HT;destruct decision;cbn[next_tag next_serial]in *.
 - now apply Hold.
 - discriminate.
 - inversion HT;subst label;cbn[fresh token_id];lia.
Qed.

Theorem fresh_id_outside_history serial s source pc history:
 Forall(fun label=>(token_id label<serial)%nat)history ->
 ~In(token_id(fresh serial s source pc))(map token_id history).
Proof.
 intros HR HI;apply in_map_iff in HI as[label[HE HI]].
 apply Forall_forall with(x:=label)in HR;[|exact HI].
 cbn[fresh token_id]in HE;lia.
Qed.

Theorem initialize_unwritten_field p root:
 roots_unwrittenb root(filter is_initial(processes p))=true ->
 forall seed,read_signal(initialize p seed)root=read_signal seed root.
Proof.
 intros HC seed;unfold initialize.
 exact(fold_run_process_preserves_root p _ root seed(roots_unwrittenb_sound _ _ HC)).
Qed.

Definition next_history decision serial s pc history:=
 match birth decision serial s pc with Some token=>history++[token]|None=>history end.
Definition HistoryRange serial history:=Forall(fun token=>(token_id token<serial)%nat)history.
Definition TagRange serial tag:=forall token,tag=Some token ->(token_id token<serial)%nat.

Lemma next_history_range decision serial s pc history:
 HistoryRange serial history ->HistoryRange(next_serial decision serial)(next_history decision serial s pc history).
Proof.
 unfold HistoryRange;intros HR;destruct decision;cbn[next_serial next_history birth];try exact HR.
 apply Forall_app;split.
 - eapply Forall_impl with(P:=fun token=>(token_id token<serial)%nat);[intros token HT;lia|exact HR].
 - constructor;[cbn[fresh token_id];lia|constructor].
Qed.

Lemma next_history_unique decision serial s pc history:
 HistoryRange serial history ->NoDup(map token_id history) ->
 NoDup(map token_id(next_history decision serial s pc history)).
Proof.
 intros HR HN;destruct decision;cbn[next_history birth];try exact HN.
 rewrite map_app;cbn[map fresh token_id].
 unfold HistoryRange in HR;revert HN;induction HR as[|token rest HB HR IH];intro HN;cbn[map]in *.
 - constructor;[intro H;contradiction|constructor].
 - inversion HN as[|x xs HX Htail];subst;constructor.
   + intro HI;apply in_app_or in HI as[HI|HI];[contradiction|].
     cbn in HI;destruct HI as[HE|HF];[lia|contradiction].
   + now apply IH.
Qed.

Record Ghost:Type:={serial:nat;current:option Token;history:list Token}.
Definition ghost_step p proc root word valid pc ev pre(g:Ghost):=
 let sampled:=phase_driven_state p ev pre in
 let decision:=phase_decision p proc root word valid ev pre in
 Build_Ghost(next_serial decision(serial g))
  (next_tag decision(serial g)sampled pc(current g))
  (next_history decision(serial g)sampled pc(history g)).
Fixpoint replay p proc root word valid pc events pre g:State*Ghost:=match events with
| []=>(pre,g)
| ev::rest=>replay p proc root word valid pc rest(PhaseSemantics p ev pre)
  (ghost_step p proc root word valid pc ev pre g)end.

Definition Invariant root validroot pre g:=
 ExtendedSVCoveredField.Related 32 root validroot word_reference(current g)pre /\
 TagRange(serial g)(current g) /\HistoryRange(serial g)(history g) /\NoDup(map token_id(history g)).

Theorem ghost_step_invariant p root validroot proc word valid
 (wc:ScalarCertificate p root 32 proc word)(vc:ScalarCertificate p validroot 1 proc valid)
 (certificate:BirthMatches root validroot word valid)pc ev pre g:
 changed_signal ev<>root ->changed_signal ev<>validroot ->Invariant root validroot pre g ->
 Invariant root validroot(PhaseSemantics p ev pre)(ghost_step p proc root word valid pc ev pre g).
Proof.
 intros HE HV[HR[HT[HH HN]]];unfold Invariant,ghost_step;cbn[serial current history].
 split.
 - exact(actual_birth_related p root validroot proc word valid wc vc certificate ev pre(serial g)pc(current g)HE HV HR).
 - split.
   + unfold TagRange;intros token Htoken;eapply tag_id_range;[exact HT|exact Htoken].
   + split;[now apply next_history_range|now apply next_history_unique].
Qed.

Theorem replay_invariant p root validroot proc word valid
 (wc:ScalarCertificate p root 32 proc word)(vc:ScalarCertificate p validroot 1 proc valid)
 (certificate:BirthMatches root validroot word valid)pc events:
 Forall(fun ev=>changed_signal ev<>root /\changed_signal ev<>validroot)events ->
 forall pre g,Invariant root validroot pre g ->
 Invariant root validroot(fst(replay p proc root word valid pc events pre g))
 (snd(replay p proc root word valid pc events pre g)).
Proof.
 intros HE;induction HE as[|ev rest[HR HV]HT IH];intros pre g HI.
 - exact HI.
 - cbn[replay];apply IH;exact(ghost_step_invariant p root validroot proc word valid wc vc certificate pc ev pre g HR HV HI).
Qed.

Theorem replay_erases p proc root word valid pc events:
 forall pre g,fst(replay p proc root word valid pc events pre g)=phase_run p events pre.
Proof. induction events as[|ev rest IH];intros pre g;cbn[replay phase_run];[reflexivity|apply IH]. Qed.

Theorem empty_initial_invariant root validroot pre:
 norm 1(read_signal pre validroot)=0%Z ->Invariant root validroot pre(Build_Ghost 0 None []).
Proof.
 intros HV;unfold Invariant;cbn[serial current history];split.
 - now apply invalid_empty_related.
 - split;[intros token H;discriminate|];split;constructor.
Qed.

Print Assumptions decision_coverage.
Print Assumptions decision_value.
Print Assumptions actual_birth_related.
Print Assumptions serial_monotone.
Print Assumptions tag_id_range.
Print Assumptions fresh_id_outside_history.
Print Assumptions initialize_unwritten_field.
Print Assumptions ghost_step_invariant.
Print Assumptions replay_invariant.
Print Assumptions replay_erases.
Print Assumptions empty_initial_invariant.
End ExtendedSVCaptureBirth.
