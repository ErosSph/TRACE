(** Authenticity of capture identities, independent of an old CPU INV. *)
From Coq Require Import List Arith ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVCaptureBirth Lang.ExtendedSVProjectionOrigin.
Import ListNotations ExtendedSV ExtendedSVCaptureBirth ExtendedSVProjectionOrigin.
Module ExtendedSVOriginLedger.

Definition Recorded ledger(tag:option Token):Prop:=forall token,tag=Some token ->In token ledger.
Definition CurrentRecorded g:=Recorded(history g)(current g).

Theorem next_history_preserves decision serial sampled pc ledger token:
 In token ledger ->In token(next_history decision serial sampled pc ledger).
Proof.
 intro H;destruct decision;cbn[next_history birth];try exact H.
 apply in_or_app;now left.
Qed.

Theorem next_tag_recorded decision serial sampled pc old ledger:
 Recorded ledger old ->Recorded(next_history decision serial sampled pc ledger)
 (next_tag decision serial sampled pc old).
Proof.
 intros HR token HT;destruct decision;cbn[next_tag next_history birth]in *.
 - now apply HR.
 - discriminate.
 - inversion HT;subst token;apply in_or_app;right;now left.
Qed.

Theorem ghost_history_preserves p proc root word valid pc ev pre g token:
 In token(history g) ->In token(history(ghost_step p proc root word valid pc ev pre g)).
Proof. unfold ghost_step;cbn[history];apply next_history_preserves. Qed.

Theorem ghost_current_recorded p proc root word valid pc ev pre g:
 CurrentRecorded g ->CurrentRecorded(ghost_step p proc root word valid pc ev pre g).
Proof. unfold CurrentRecorded,ghost_step;cbn[history current];apply next_tag_recorded. Qed.

Theorem recipe_recorded recipe sampled old incoming ledger:
 Recorded ledger old ->Recorded ledger incoming ->
 Recorded ledger(@recipe_origin Token sampled recipe old incoming).
Proof.
 intros HO HI;induction recipe;cbn[recipe_origin];try assumption.
 - intros token H;discriminate.
 - destruct(Z.eqb(eval_expr sampled guard)0);assumption.
Qed.

Theorem phase_recorded p proc recipe ev pre old incoming ledger:
 Recorded ledger old ->Recorded ledger incoming ->
 Recorded ledger(@projection_phase_origin Token p proc recipe ev pre old incoming).
Proof.
 intros HO HI;unfold projection_phase_origin.
 destruct(process_matches_states pre(phase_driven_state p ev pre)proc).
 - now apply recipe_recorded.
 - exact HO.
Qed.

Theorem recorded_mono before after tag:
 (forall token,In token before ->In token after) ->Recorded before tag ->Recorded after tag.
Proof. intros HM HR token HT;apply HM;exact(HR token HT). Qed.

Theorem ledger_id_unique ledger:
 NoDup(map token_id ledger) ->forall a b,In a ledger ->In b ledger ->token_id a=token_id b ->a=b.
Proof.
 induction ledger as[|head rest IH];intros HN a b HA HB HE;[contradiction|].
 inversion HN as[|x xs Hhead Hrest];subst;cbn in HA,HB.
 destruct HA as[HA|HA];destruct HB as[HB|HB].
 - now subst a b.
 - subst a;exfalso;apply Hhead;rewrite HE;now apply in_map.
 - subst b;exfalso;apply Hhead;rewrite <-HE;now apply in_map.
 - exact(IH Hrest a b HA HB HE).
Qed.

Print Assumptions ghost_history_preserves.
Print Assumptions ghost_current_recorded.
Print Assumptions recipe_recorded.
Print Assumptions phase_recorded.
Print Assumptions recorded_mono.
Print Assumptions ledger_id_unique.
End ExtendedSVOriginLedger.
