(** Captured words retain the real read-port relation. No ISA-order premise. *)
From Coq Require Import ZArith List Bool Sorting.Permutation.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVInstructionOrigin Lang.ExtendedSVExprAgreement
 Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCheckedPhaseReplay
 Lang.ExtendedSVRootProjection Lang.ExtendedSVEmptyPipeline
 Lang.ExtendedSVWordInvariant Lang.ExtendedSVCaptureAccounting Lang.ExtendedSVConstantRoot.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVInstructionOrigin
 ExtendedSVExprAgreement ExtendedSVCaptureBirth ExtendedSVRootProjection ExtendedSVWordInvariant ExtendedSVConstantRoot.
Module ExtendedSVCaptureRead.

Definition reads_twob width bank address expression:=
 forallb(fun wr=>(Nat.eqb(fst wr)width && Nat.eqb(snd wr)bank) ||
 (Nat.eqb(fst wr)32 && Nat.eqb(snd wr)address))(expr_inputs expression).
Definition image_state bank address image pc:=write_signal(write_signal [] bank image)address pc.
Definition image_read expression bank address image pc:=eval_expr(image_state bank address image pc)expression.

Theorem read_projection width bank address expression s image:
 bank<>address ->reads_twob width bank address expression=true ->
 read_signal s bank=image ->
 eval_expr s expression=image_read expression bank address image(norm 32(read_signal s address)).
Proof.
 intros Hneq HC HB;unfold image_read,image_state;apply eval_expr_agree.
 intros w root HI;pose proof(proj1(forallb_forall _ _)HC(w,root)HI)as HR.
 cbn[fst snd]in HR;apply orb_true_iff in HR;destruct HR as[HR|HR];
 apply andb_true_iff in HR;destruct HR as[HW HX];
 apply Nat.eqb_eq in HW;apply Nat.eqb_eq in HX;subst w root.
 - rewrite read_signal_write_other by congruence;rewrite read_signal_write_same,HB;reflexivity.
 - rewrite read_signal_write_same;apply eq_sym;apply norm_idempotent.
Qed.

Theorem phase_accept_copy p proc root word valid ev pre source:
 phase_decision p proc root word valid ev pre=Accept source ->
 copy_source(phase_driven_state p ev pre)word=Some source /\source<>root.
Proof.
 unfold phase_decision;destruct(process_matches_states _ _ _);[|discriminate].
 unfold decide;destruct(Z.eqb _ _);[discriminate|].
 destruct(copy_source _ _)as[actual|]eqn:HC;[|discriminate].
 destruct(Nat.eqb actual root)eqn:HN;[discriminate|].
 intro H;inversion H;subst actual;split;[reflexivity|now apply Nat.eqb_neq].
Qed.

Definition FreshProperty p proc root word valid pc ev pre(P:Token->Prop):=
 forall source serial,phase_decision p proc root word valid ev pre=Accept source ->
 P(fresh serial(phase_driven_state p ev pre)source pc).

Theorem history_property p proc root word valid pc ev pre g P:
 Forall P(history g) ->FreshProperty p proc root word valid pc ev pre P ->
 Forall P(history(ghost_step p proc root word valid pc ev pre g)).
Proof.
 intros HH HF;unfold ghost_step;cbn[history];unfold next_history.
 destruct(phase_decision p proc root word valid ev pre)eqn:HD;cbn[birth];try exact HH.
 apply Forall_app;split;[exact HH|]. constructor;[exact(HF _ _ HD)|constructor].
Qed.

Theorem current_property p proc root word valid pc ev pre g P:
 (forall token,current g=Some token ->P token) ->FreshProperty p proc root word valid pc ev pre P ->
 forall token,current(ghost_step p proc root word valid pc ev pre g)=Some token ->P token.
Proof.
 intros HT HF token;unfold ghost_step;cbn[current].
 destruct(phase_decision p proc root word valid ev pre)eqn:HD;cbn[next_tag].
 - exact(HT token).
 - discriminate.
 - intro HE;inversion HE;subst token;exact(HF _ _ HD).
Qed.

Theorem recorded_property(P:Token->Prop)ledger token:
 Forall P ledger ->In token ledger ->P token.
Proof. intros HP HI;exact(proj1(Forall_forall _ _)HP token HI). Qed.

Theorem accounted_property P ledger accounts:
 Forall P ledger ->ExtendedSVCaptureAccounting.AccountsFor ledger accounts ->
 Forall P(ExtendedSVCaptureAccounting.retired accounts++ExtendedSVCaptureAccounting.waiting accounts).
Proof.
 intros HP HA;apply Forall_forall;intros token HI;eapply recorded_property;[exact HP|].
 apply(Permutation_in token(Permutation_sym HA));apply in_app_or in HI as[HI|HI];
 apply in_or_app;[now left|right;apply in_or_app;now left].
Qed.

Theorem unwritten_history p root events:
 roots_unwrittenb root(processes p)=true ->Forall(fun ev=>changed_signal ev<>root)events ->
 forall pre,read_signal(phase_run p events pre)root=read_signal pre root.
Proof.
 intros HW HE;induction HE as[|ev rest HE HR IH];intro pre;[reflexivity|].
 cbn[phase_run];rewrite IH,(ExtendedSVEmptyPipeline.phase_input p root ev pre HW).
 now rewrite read_signal_write_other.
Qed.

Theorem successful_replay p(Ghost:Type)observe(EventClass:Event->Prop)(Inv:State->Ghost->Prop)
 (keep:forall ev pre g next,EventClass ev ->Inv pre g ->observe ev pre g=Some next ->
 Inv(PhaseSemantics p ev pre)next)events:
 Forall EventClass events ->forall pre g post final,Inv pre g ->
 ExtendedSVCheckedPhaseReplay.run p Ghost observe events pre g=Some(post,final) ->Inv post final.
Proof.
 intro HE;induction HE as[|ev rest HE HR IH];intros pre g post final HI HS;
 cbn[ExtendedSVCheckedPhaseReplay.run]in HS.
 - inversion HS;subst;exact HI.
 - destruct(observe ev pre g)as[next|]eqn:HC;[|discriminate].
   exact(IH _ next post final(keep ev pre g next HE HI HC)HS).
Qed.
Print Assumptions read_projection.
Print Assumptions phase_accept_copy.
Print Assumptions history_property.
Print Assumptions current_property.
Print Assumptions recorded_property.
Print Assumptions accounted_property.
Print Assumptions unwritten_history.
Print Assumptions successful_replay.
End ExtendedSVCaptureRead.
