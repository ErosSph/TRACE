(** Generic constant-slice producer algebra needed by the actual three BE bits. *)
From Coq Require Import List ZArith Lia Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVAssignment Lang.ExtendedSVProducerAssignment
 Lang.ExtendedSVCombIdempotence Lang.ExtendedSVBlocking Lang.ExtendedSVBlockingReplay
 Lang.ExtendedSVProcessSlice.
Import ListNotations ExtendedSV ExtendedSVAssignment ExtendedSVProducerAssignment
 ExtendedSVCombIdempotence ExtendedSVBlocking ExtendedSVBlockingReplay ExtendedSVProcessSlice.
Local Open Scope Z_scope.
Module DarkRISCV38SliceProducer.
Definition lhs width bank root offwidth off:=LSel width(LVar bank root)(EConst offwidth off).
Definition upd width root offset value:Update:={|update_signal:=root;update_offset:=offset;
 update_width:=width;update_value:=norm width value|}.
Lemma actual_slice p proc width bank root offwidth off rhs state :
 process_body proc=SAssign false rhs(lhs width bank root offwidth off) ->
 (0<statement_fuel p)%nat ->
 run_process p state proc=apply_update state(upd width root(norm offwidth off)(eval_expr state rhs)).
Proof.
 intros HB HF. rewrite(assignment_run_process p proc state false rhs(lhs width bank root offwidth off)HB HF).
 unfold lhs,upd;cbn [resolve_update resolve_lvalue eval_expr].
 rewrite Z.add_0_l. reflexivity.
Qed.
Theorem slice_idempotent p proc width bank root offwidth off rhs :
 process_body proc=SAssign false rhs(lhs width bank root offwidth off) ->
 (0<statement_fuel p)%nat ->NoInputRoot root rhs ->ProducerIdempotent p proc.
Proof.
 intros HB HF HI state. rewrite !actual_slice with(width:=width)(bank:=bank)(root:=root)
 (offwidth:=offwidth)(off:=off)(rhs:=rhs)by assumption.
 rewrite invisible_update_keeps_expression by exact HI.
 apply identical_update_is_idempotent.
Qed.
Definition DisjointUpdate width root offset update:=update_signal update<>root \/
 Z.land(update_mask update)(Z.shiftl(mask width)offset)=0.
Lemma slice_commutes_update p proc width bank root offwidth off rhs update state :
 process_body proc=SAssign false rhs(lhs width bank root offwidth off) ->
 (0<statement_fuel p)%nat ->NoInputRoot(update_signal update)rhs ->
 DisjointUpdate width root(norm offwidth off)update ->
 run_process p(apply_update state update)proc=apply_update(run_process p state proc)update.
Proof.
 intros HB HF HI HD. rewrite !actual_slice with(width:=width)(bank:=bank)(root:=root)
 (offwidth:=offwidth)(off:=off)(rhs:=rhs)by assumption.
 rewrite invisible_update_keeps_expression by exact HI.
 destruct HD as[HN|HD].
 - apply apply_update_commute. exact HN.
 - destruct(Nat.eq_dec(update_signal update)root)as[HE|HN].
   + apply apply_update_commute_disjoint;[exact HE|].
     exact HD.
   + apply apply_update_commute;exact HN.
Qed.
Lemma slice_preserved_updates p proc width bank root offwidth off rhs updates :
 process_body proc=SAssign false rhs(lhs width bank root offwidth off) ->
 (0<statement_fuel p)%nat ->
 (forall u,In u updates ->NoInputRoot(update_signal u)rhs /\DisjointUpdate width root(norm offwidth off)u) ->
 forall state,ProducerFixed p proc state ->ProducerFixed p proc(apply_updates state updates).
Proof.
 intros HB HF HU. induction updates as[|u us IH];intros state HS;[exact HS|].
 cbn [apply_updates]. apply IH;[intros v HV;apply HU;now right|].
 unfold ProducerFixed in *.
 rewrite(slice_commutes_update p proc width bank root offwidth off rhs u state HB HF
 (proj1(HU u(or_introl eq_refl)))(proj2(HU u(or_introl eq_refl)))). now rewrite HS.
Qed.
Theorem slice_foreign_later p first later width bank root offwidth off rhs :
 process_body first=SAssign false rhs(lhs width bank root offwidth off) ->
 (0<statement_fuel p)%nat ->blocking_onlyb(process_body later)=true ->
 (forall r,In r(process_writers later)->r<>root /\NoInputRoot r rhs) ->
 LaterPreservesFixed p first later.
Proof.
 intros HB HF HL HR state HS. unfold ProducerFixed.
 rewrite(actual_blocking_process_replays p later state HL).
 apply(slice_preserved_updates p first width bank root offwidth off rhs _ HB HF);[|exact HS].
 intros u HU. apply process_emitted_writers in HU. destruct(HR _ HU)as[HN HI].
 split;[exact HI|now left].
Qed.
Theorem slice_disjoint_later p first later width bank root offwidth off rhs
 width2 bank2 offwidth2 off2 rhs2 :
 process_body first=SAssign false rhs(lhs width bank root offwidth off) ->
 process_body later=SAssign false rhs2(lhs width2 bank2 root offwidth2 off2) ->
 (0<statement_fuel p)%nat ->NoInputRoot root rhs ->
 Z.land(Z.shiftl(mask width2)(norm offwidth2 off2))(Z.shiftl(mask width)(norm offwidth off))=0 ->
 LaterPreservesFixed p first later.
Proof.
 intros HB HL HF HI HD state HS. unfold ProducerFixed in *.
 rewrite(actual_slice p later width2 bank2 root offwidth2 off2 rhs2 state HL HF).
 rewrite(slice_commutes_update p first width bank root offwidth off rhs
 (upd width2 root(norm offwidth2 off2)(eval_expr state rhs2)) state HB HF HI).
 - now rewrite HS.
 - right;exact HD.
Qed.
Definition slice_producerb proc:=match process_body proc with
 |SAssign false rhs(LSel width(LVar bank root)(EConst ow off))=>no_input_rootb root rhs
 |_=>false end.
Lemma slice_producerb_sound p proc : (0<statement_fuel p)%nat ->slice_producerb proc=true ->ProducerIdempotent p proc.
Proof.
 intros HF HC. unfold slice_producerb in HC.
 destruct(process_body proc)as[|nba e lv| | |]eqn:HB;try discriminate.
 destruct nba;[discriminate|]. destruct lv as[w r|w base offset];[discriminate|].
 destruct base as[b r|];[|discriminate]. destruct offset;try discriminate.
 eapply slice_idempotent;[exact HB|exact HF|now apply no_input_rootb_sound].
Qed.
Definition slice_transportb first later:=match process_body first with
 |SAssign false rhs(LSel width(LVar bank root)(EConst ow off))=>
 (blocking_onlyb(process_body later)&&forallb(fun r=>negb(Nat.eqb r root)&&no_input_rootb r rhs)(process_writers later)) ||
 match process_body later with
 |SAssign false rhs2(LSel width2(LVar bank2 root2)(EConst ow2 off2))=>
 Nat.eqb root root2&&no_input_rootb root rhs&&
 Z.eqb(Z.land(Z.shiftl(mask width2)(norm ow2 off2))(Z.shiftl(mask width)(norm ow off)))0
 |_=>false end
 |_=>false end.
Lemma slice_transportb_sound p first later : (0<statement_fuel p)%nat ->
 slice_transportb first later=true ->LaterPreservesFixed p first later.
Proof.
 intros HF HC. unfold slice_transportb in HC.
 destruct(process_body first)as[|nba e lv| | |]eqn:HB;try discriminate.
 destruct nba;[discriminate|]. destruct lv as[w r|w base offset];[discriminate|].
 destruct base as[b r|];[|discriminate]. destruct offset;try discriminate.
 apply orb_true_iff in HC as[HC|HC].
 - apply andb_true_iff in HC as[HL HW].
   eapply slice_foreign_later;[exact HB|exact HF|exact HL|].
   intros root Hin. apply forallb_forall with(x:=root)in HW;[|exact Hin].
   apply andb_true_iff in HW as[HN HI]. split.
   + apply Bool.negb_true_iff in HN;now apply Nat.eqb_neq.
   + now apply no_input_rootb_sound.
 - destruct(process_body later)as[|nba2 e2 lv2| | |]eqn:HL;try discriminate.
   destruct nba2;[discriminate|]. destruct lv2 as[w2 r2|w2 base2 offset2];[discriminate|].
   destruct base2 as[b2 r2|];[|discriminate]. destruct offset2;try discriminate.
   apply andb_true_iff in HC as[HC HD]. apply andb_true_iff in HC as[HE HI].
   apply Nat.eqb_eq in HE;subst r2.
   eapply slice_disjoint_later;[exact HB|exact HL|exact HF|now apply no_input_rootb_sound|now apply Z.eqb_eq].
Qed.
End DarkRISCV38SliceProducer.
