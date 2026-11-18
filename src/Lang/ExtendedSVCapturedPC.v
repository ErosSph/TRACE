(** PC stored alongside a captured instruction, not ISA execution order. *)
From Coq Require Import ZArith Bool List.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVCaptureBirth Lang.ExtendedSVInstructionOrigin Lang.ExtendedSVScalarExpression
 Lang.ExtendedSVRuntimeHistory Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVBootstrap.
Import ExtendedSV ExtendedSVScalarHistory ExtendedSVWordInvariant ExtendedSVCaptureBirth ExtendedSVInstructionOrigin ExtendedSVScalarExpression.
Module ExtendedSVCapturedPC.
Definition Related root pre g:=forall token,current g=Some token ->
 token_pc token=Some(norm 32(read_signal pre root)).

Inductive Matches root pcroot (pc:State->signal->option Z)(Good:State->Prop):Expr->Expr->Expr->Prop:=
| Invalid:forall word next,Matches root pcroot pc Good word(EConst 1 0)next
| Hold:forall valid,Matches root pcroot pc Good(EVar 32 root)valid(EVar 32 pcroot)
| Fresh:forall source valid next,source<>root ->
 (forall s,Good s ->pc s source=Some(norm 32(eval_expr s next))) ->
 Matches root pcroot pc Good(EVar 32 source)valid next
| Select:forall guard wy wn vy vn py pn,
 Matches root pcroot pc Good wy vy py ->Matches root pcroot pc Good wn vn pn ->
 Matches root pcroot pc Good(ECond 32 guard wy wn)(ECond 1 guard vy vn)(ECond 32 guard py pn).

Lemma decision_pc root pcroot pc Good word valid next
 (certificate:Matches root pcroot pc Good word valid next)s serial old:
 Good s ->(forall token,old=Some token ->token_pc token=Some(norm 32(read_signal s pcroot))) ->
 forall token,next_tag(decide root word valid s)serial s pc old=Some token ->
 token_pc token=Some(norm 32(eval_expr s next)).
Proof.
 intros HG HO;induction certificate;intros token HT.
 - unfold decide in HT;cbn[eval_expr norm next_tag]in HT;discriminate.
 - unfold decide in HT;cbn[copy_source]in HT;rewrite !Nat.eqb_refl in HT.
   destruct(Z.eqb(norm 1(eval_expr s valid))0);[discriminate|].
   cbn[next_tag]in HT;cbn[eval_expr];rewrite norm_idempotent;apply HO;exact HT.
 - unfold decide in HT;cbn[copy_source]in HT;rewrite Nat.eqb_refl in HT.
   assert(HS:Nat.eqb source root=false)by(now apply Nat.eqb_neq).
   rewrite HS in HT;destruct(Z.eqb(norm 1(eval_expr s valid))0);[discriminate|].
   cbn[next_tag]in HT;inversion HT;subst token;cbn[fresh token_pc];now apply H0.
 - unfold decide in HT;cbn[eval_expr copy_source]in HT;rewrite norm_idempotent in HT.
   cbn[eval_expr];rewrite norm_idempotent.
   destruct(Z.eqb(eval_expr s guard)0).
   + apply IHcertificate2;exact HT.
   + apply IHcertificate1;exact HT.
Qed.

Theorem actual_phase p root pcroot proc word valid next pc Good
 (scalar:ScalarCertificate p pcroot 32 proc next)
 (certificate:Matches root pcroot pc Good word valid next)ev pre g:
 changed_signal ev<>pcroot ->Good(phase_driven_state p ev pre) ->Related pcroot pre g ->
 Related pcroot(PhaseSemantics p ev pre)(ghost_step p proc root word valid pc ev pre g).
Proof.
 intros HE HG HR token HT;rewrite(history_phase_projection _ _ _ _ _ scalar ev pre HE).
 unfold ghost_step in HT;cbn[current]in HT;unfold phase_decision in HT.
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc).
 - eapply decision_pc;[exact certificate|exact HG| |exact HT].
   intros t H;rewrite(sampled_root_preserved p ev pre pcroot(history_comb_frame _ _ _ _ _ scalar)HE);now apply HR.
 - exact(HR token HT).
Qed.
Theorem checked_history p catalog
 (cert:ExtendedSVBoundedCatalogPhase.BoundedCatalogCertificate p catalog)
 (Ghost:Type)(advance:Event->State->Ghost->unit->Ghost)(R:State->Ghost->Prop)(Allowed:Event->Prop)
 (input:forall ev,Allowed ev ->ExtendedSVBoundedCatalogPhase.CatalogEvent p catalog ev)
 (step:forall seed ev pre ghost,Allowed ev ->CombLFP p seed(phase_driven_state p ev pre) ->
 R pre ghost ->R(PhaseSemantics p ev pre)(advance ev pre ghost tt)) events:
 Forall Allowed events ->forall pre ghost,ExtendedSVBoundedCatalogPhase.CatalogShape p catalog pre ->R pre ghost ->
 R(phase_run p events pre)(ExtendedSVRuntimeHistory.replay p Ghost advance events pre ghost).
Proof.
 intro HE;induction HE as[|ev rest HE HT IH];intros pre ghost HS HR;[exact HR|].
 destruct(ExtendedSVBootstrap.catalog_phase_evidence p catalog cert ev pre(input ev HE)HS)as[HL[HX HS']].
 cbn[phase_run ExtendedSVRuntimeHistory.replay];apply IH;[exact HS'|exact(step _ _ _ _ HE HL HR)].
Qed.
End ExtendedSVCapturedPC.
Print Assumptions ExtendedSVCapturedPC.decision_pc.
Print Assumptions ExtendedSVCapturedPC.actual_phase.
