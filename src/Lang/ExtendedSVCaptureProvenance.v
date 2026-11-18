(** Recorded capture identities are distinct from ISA retirement identities. *)
From Coq Require Import List ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVCaptureBirth Lang.ExtendedSVProjectionOrigin.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVCaptureBirth ExtendedSVProjectionOrigin.
Module ExtendedSVCaptureProvenance.
Definition Recorded (log:list Token)(tag:option Token):Prop:=
 forall token,tag=Some token ->In token log.

Lemma history_extends decision serial s pc log:
 incl log(next_history decision serial s pc log).
Proof.
 destruct decision;cbn[next_history birth];intros token H;try exact H.
 apply in_or_app;left;exact H.
Qed.

Lemma tag_recorded decision serial s pc old log:
 Recorded log old ->Recorded(next_history decision serial s pc log)(next_tag decision serial s pc old).
Proof.
 intros HR token HT;destruct decision;cbn[next_history birth next_tag]in *.
 - now apply HR.
 - discriminate.
 - inversion HT;subst token;apply in_or_app;right;left;reflexivity.
Qed.

Lemma ghost_recorded p proc root word valid pc ev pre g:
 Recorded(history g)(current g) ->
 Recorded(history(ghost_step p proc root word valid pc ev pre g))
 (current(ghost_step p proc root word valid pc ev pre g)).
Proof. unfold ghost_step;cbn[history current];apply tag_recorded. Qed.

Lemma ghost_history_extends p proc root word valid pc ev pre g:
 incl(history g)(history(ghost_step p proc root word valid pc ev pre g)).
Proof. unfold ghost_step;cbn[history];apply history_extends. Qed.

Lemma recipe_recorded s recipe old incoming log:
 Recorded log old ->Recorded log incoming ->Recorded log(recipe_origin s recipe old incoming).
Proof.
 intros HO HI;induction recipe;cbn[recipe_origin];try assumption.
 - intros token H;discriminate.
 - destruct(Z.eqb(eval_expr s guard)0);assumption.
Qed.

Lemma projection_recorded p proc recipe ev pre old incoming log:
 Recorded log old ->Recorded log incoming ->
 Recorded log(projection_phase_origin p proc recipe ev pre old incoming).
Proof.
 intros HO HI;unfold projection_phase_origin.
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc);
 [now apply recipe_recorded|exact HO].
Qed.

Lemma recorded_extend oldlog newlog tag:
 incl oldlog newlog ->Recorded oldlog tag ->Recorded newlog tag.
Proof. intros HI HR token HT;apply HI;now apply HR. Qed.

Lemma token_id_identifies log:
 NoDup(map token_id log) ->forall a b,In a log ->In b log ->token_id a=token_id b ->a=b.
Proof.
 induction log as[|head rest IH];cbn;intros HN a b HA HB HE;[contradiction|].
 inversion HN as[|x xs Hnot Htail];subst.
 destruct HA as[<-|HA];destruct HB as[<-|HB];try reflexivity.
 - exfalso;apply Hnot;rewrite HE;apply in_map;exact HB.
 - exfalso;apply Hnot;rewrite <-HE;apply in_map;exact HA.
 - exact(IH Htail a b HA HB HE).
Qed.
End ExtendedSVCaptureProvenance.
Print Assumptions ExtendedSVCaptureProvenance.ghost_recorded.
Print Assumptions ExtendedSVCaptureProvenance.projection_recorded.
Print Assumptions ExtendedSVCaptureProvenance.token_id_identifies.
