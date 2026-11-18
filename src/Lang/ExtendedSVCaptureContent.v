(** Preserve a checked property of captured instruction records.
    The property is supplied with a proof at the actual sampled acceptance
    branch; this does not establish ISA program order or retirement. *)
From Coq Require Import List ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVInstructionOrigin
 Lang.ExtendedSVCaptureBirth Lang.ExtendedSVWordInvariant.
Import ListNotations ExtendedSV ExtendedSVInstructionOrigin
 ExtendedSVCaptureBirth ExtendedSVWordInvariant.
Module ExtendedSVCaptureContent.

Inductive Matches root (pc:State->signal->option Z)
 (Good:State->Prop)(P:Token->Prop):Expr->Expr->Prop:=
| Invalid:forall word,Matches root pc Good P word(EConst 1 0)
| Hold:forall valid,Matches root pc Good P(EVar 32 root)valid
| Fresh:forall source valid,source<>root ->
 (forall s serial,Good s ->norm 1(eval_expr s valid)<>0%Z ->
  P(fresh serial s source pc)) ->
 Matches root pc Good P(EVar 32 source)valid
| Select:forall guard wy wn vy vn,
 Matches root pc (fun s=>Good s /\Z.eqb(eval_expr s guard)0=false) P wy vy ->
 Matches root pc (fun s=>Good s /\Z.eqb(eval_expr s guard)0=true) P wn vn ->
 Matches root pc Good P(ECond 32 guard wy wn)(ECond 1 guard vy vn).

Theorem accepted_content root pc Good P word valid
 (cert:Matches root pc Good P word valid)s serial source:
 Good s ->decide root word valid s=Accept source ->P(fresh serial s source pc).
Proof.
 induction cert;intros HG HD.
 - unfold decide in HD;cbn[eval_expr norm]in HD;discriminate.
 - unfold decide in HD;cbn[copy_source]in HD;rewrite !Nat.eqb_refl in HD.
   destruct(Z.eqb(norm 1(eval_expr s valid))0);discriminate.
 - unfold decide in HD;cbn[copy_source]in HD;rewrite Nat.eqb_refl in HD.
   destruct(Z.eqb(norm 1(eval_expr s valid))0)eqn:HV;[discriminate|].
   destruct(Nat.eqb source0 root)eqn:HR;[discriminate|].
   inversion HD;subst source;apply H0;[exact HG|now apply Z.eqb_neq].
 - unfold decide in HD;cbn[eval_expr copy_source]in HD;rewrite norm_idempotent in HD.
   destruct(Z.eqb(eval_expr s guard)0)eqn:HB.
   + apply IHcert2;[split;[exact HG|reflexivity]|exact HD].
   + apply IHcert1;[split;[exact HG|reflexivity]|exact HD].
Qed.

Definition Related (P:Token->Prop)(g:Ghost):Prop:=
 Forall P(history g) /\forall token,current g=Some token ->P token.

Lemma decision_preserves P decision serial s pc old log:
 (forall source,decision=Accept source ->P(fresh serial s source pc)) ->
 Forall P log ->(forall token,old=Some token ->P token) ->
 Forall P(next_history decision serial s pc log) /\
 (forall token,next_tag decision serial s pc old=Some token ->P token).
Proof.
 intros HF HH HT;destruct decision;cbn[next_history birth next_tag].
 - split;assumption.
 - split;[exact HH|intros token H;discriminate].
 - split.
   + apply Forall_app;split;[exact HH|constructor;[apply HF;reflexivity|constructor]].
   + intros token H;inversion H;subst token;apply HF;reflexivity.
Qed.

Theorem actual_phase p proc root word valid pc Good P
 (cert:Matches root pc Good P word valid)ev pre g:
 Good(phase_driven_state p ev pre) ->Related P g ->
 Related P(ghost_step p proc root word valid pc ev pre g).
Proof.
 intros HG[HH HT];unfold Related,ghost_step;cbn[history current].
 apply decision_preserves;[|exact HH|exact HT].
 intros source HD;unfold phase_decision in HD.
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc);[|discriminate].
 exact(accepted_content root pc Good P word valid cert _ _ source HG HD).
Qed.

Lemma empty_related P:Related P(Build_Ghost 0 None []).
Proof. split;[constructor|intros token H;discriminate]. Qed.

Lemma recorded_content P g token:
 Related P g ->In token(history g) ->P token.
Proof. intros[HH _]HI;rewrite Forall_forall in HH;exact(HH token HI). Qed.
End ExtendedSVCaptureContent.
Print Assumptions ExtendedSVCaptureContent.accepted_content.
Print Assumptions ExtendedSVCaptureContent.actual_phase.
