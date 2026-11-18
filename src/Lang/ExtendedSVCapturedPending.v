(** Queue construction consumes births from the actual RTL phase observer.
    Retirement/cancellation bindings remain explicit unproved CPU obligations. *)
From Coq Require Import List Arith ZArith Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVCaptureBirth Lib.CheckedPendingQueue.
Import ListNotations ExtendedSV ExtendedSVCaptureBirth.
Module ExtendedSVCapturedPending.

Definition token_eq_dec:forall a b:Token,{a=b}+{a<>b}.
Proof. decide equality;try apply Nat.eq_dec;try apply Z.eq_dec;decide equality;apply Z.eq_dec. Defined.
Definition NewTokens decision serial sampled pc:=match birth decision serial sampled pc with
| Some token=>[token]|None=>[]end.
Definition Pending ledger queue:=Forall(fun token=>In token ledger)queue /\NoDup(map token_id queue).

Lemma history_app_birth decision serial sampled pc ledger:
 next_history decision serial sampled pc ledger=ledger++NewTokens decision serial sampled pc.
Proof. destruct decision;cbn[next_history NewTokens birth];now rewrite ?app_nil_r. Qed.

Lemma nodup_snoc{A:Type}(l:list A)x:NoDup l ->~In x l ->NoDup(l++[x]).
Proof.
 intros HN;induction HN as[|head rest HH HN IH];intro HX;cbn.
 - constructor;[intro H;contradiction|constructor].
 - constructor.
   + intro HI;apply in_app_or in HI as[HI|HI];[contradiction|].
     cbn in HI;destruct HI as[HE|HF];[subst head;apply HX;now left|contradiction].
   + apply IH;intro H;apply HX;now right.
Qed.

Theorem extend_pending decision serial sampled pc ledger queue:
 HistoryRange serial ledger ->Pending ledger queue ->
 Pending(next_history decision serial sampled pc ledger)(queue++NewTokens decision serial sampled pc).
Proof.
 intros HR[HQ HN];split.
 - apply Forall_forall;intros token HI;rewrite history_app_birth.
   apply in_app_or in HI as[HI|HI];apply in_or_app;[left|now right].
   apply Forall_forall with(x:=token)in HQ;assumption.
 - destruct decision;cbn[NewTokens birth];try(now rewrite app_nil_r).
   rewrite map_app;cbn[map];apply nodup_snoc;[exact HN|].
   intro HI;apply in_map_iff in HI as[token[HE HI]].
   apply Forall_forall with(x:=token)in HQ;[|exact HI].
   unfold HistoryRange in HR;apply Forall_forall with(x:=token)in HR;[|exact HQ].
   cbn[fresh token_id]in HE;lia.
Qed.

Theorem successful_queue_preserves ledger queue admitted retiring cancel kept killed:
 Pending ledger(queue++admitted) ->
 CheckedPendingQueue.step token_eq_dec queue admitted retiring cancel=Some(kept,killed) ->Pending ledger kept.
Proof.
 intros[HF HN]HS;pose proof(CheckedPendingQueue.step_partition token_eq_dec _ _ _ _ _ _ HS)as HE.
 rewrite HE in HF,HN;apply Forall_app in HF as[_ HF];apply Forall_app in HF as[HF _].
 rewrite !map_app in HN;split;[exact HF|].
 exact(NoDup_app_remove_r(map token_id kept)(map token_id killed)
  (NoDup_app_remove_l(map token_id retiring)(map token_id kept++map token_id killed)HN)).
Qed.

Section ActualPhase.
Variable p:Program.
Variable proc:Process.
Variable root:signal.
Variable word valid:Expr.
Variable pc:State->signal->option Z.
Definition observed_births ev pre g:=NewTokens(phase_decision p proc root word valid ev pre)
 (serial g)(phase_driven_state p ev pre)pc.
Definition queue_step ev pre g queue retiring cancel:=CheckedPendingQueue.step token_eq_dec
 queue(observed_births ev pre g)retiring cancel.

Theorem phase_queue_partition ev pre g queue retiring cancel kept killed:
 queue_step ev pre g queue retiring cancel=Some(kept,killed) ->
 queue++observed_births ev pre g=retiring++(kept++killed).
Proof. apply CheckedPendingQueue.step_partition. Qed.

Theorem phase_queue_preserved ev pre g queue retiring cancel kept killed:
 HistoryRange(serial g)(history g) ->Pending(history g)queue ->
 queue_step ev pre g queue retiring cancel=Some(kept,killed) ->
 Pending(history(ghost_step p proc root word valid pc ev pre g))kept.
Proof.
 intros HR HQ HS;eapply successful_queue_preserves;[|exact HS].
 unfold ghost_step,observed_births;cbn[history];now apply extend_pending.
Qed.

Theorem phase_births_recorded ev pre g:
 Forall(fun token=>In token(history(ghost_step p proc root word valid pc ev pre g)))
 (observed_births ev pre g).
Proof.
 unfold ghost_step,observed_births;cbn[history];rewrite history_app_birth.
 apply Forall_forall;intros token HI;apply in_or_app;now right.
Qed.

Theorem phase_births_have_current_serial ev pre g:
 Forall(fun token=>token_id token=serial g)(observed_births ev pre g).
Proof.
 unfold observed_births;destruct(phase_decision p proc root word valid ev pre);cbn[NewTokens birth];
 repeat constructor.
Qed.
End ActualPhase.

Print Assumptions extend_pending.
Print Assumptions successful_queue_preserves.
Print Assumptions phase_queue_partition.
Print Assumptions phase_queue_preserved.
Print Assumptions phase_births_recorded.
Print Assumptions phase_births_have_current_serial.
End ExtendedSVCapturedPending.
