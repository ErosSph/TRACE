(** Every capture is pending, retired, or explicitly cancelled. No future
    CPU correctness, retirement success or progress is assumed by this INV. *)
From Coq Require Import List Arith Lia Sorting.Permutation.
Require Import Lang.ExtendedSV Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPending Lib.CheckedPendingQueue.
Import ListNotations ExtendedSVCaptureBirth ExtendedSVCapturedPending.
Module ExtendedSVCaptureAccounting.
Record Accounts:Type:={retired:list Token;waiting:list Token;cancelled:list Token}.
Definition empty:=Build_Accounts[][][].
Definition AccountsFor ledger a:=Permutation ledger(retired a++waiting a++cancelled a).
Definition advance a admitted retiring cancel:=
 match CheckedPendingQueue.step token_eq_dec(waiting a)admitted retiring cancel with
 | None=>None
 | Some(kept,killed)=>Some(Build_Accounts(retired a++retiring)kept(cancelled a++killed))
 end.

Lemma partition_accounts(history r q c admitted retiring kept killed:list Token):
 Permutation history(r++q++c) ->q++admitted=retiring++(kept++killed) ->
 Permutation(history++admitted)((r++retiring)++kept++(c++killed)).
Proof.
 intros HA HQ;transitivity((r++q++c)++admitted);[now apply Permutation_app_tail|].
 replace((r++q++c)++admitted)with(r++q++(c++admitted))by(now rewrite !app_assoc).
 transitivity(r++q++(admitted++c)).
 - apply Permutation_app_head,Permutation_app_head,Permutation_app_comm.
 - replace(r++q++(admitted++c))with(r++(q++admitted)++c)by(now rewrite !app_assoc).
   rewrite HQ.
   replace(r++(retiring++(kept++killed))++c)with(r++retiring++kept++(killed++c))by(now rewrite !app_assoc).
   replace((r++retiring)++kept++(c++killed))with(r++retiring++kept++(c++killed))by(now rewrite !app_assoc).
   apply Permutation_app_head,Permutation_app_head,Permutation_app_head,Permutation_app_comm.
Qed.

Theorem accounts_step history a admitted retiring cancel next:
 AccountsFor history a ->advance a admitted retiring cancel=Some next ->AccountsFor(history++admitted)next.
Proof.
 intros HA HS;unfold advance in HS.
 destruct(CheckedPendingQueue.step token_eq_dec(waiting a)admitted retiring cancel)as[[kept killed]|]eqn:HC;[|discriminate].
 inversion HS;subst next;unfold AccountsFor in *;cbn[retired waiting cancelled].
 apply(partition_accounts history(retired a)(waiting a)(cancelled a)admitted retiring kept killed HA).
 exact(CheckedPendingQueue.step_partition token_eq_dec _ _ _ _ _ _ HC).
Qed.

Theorem accounts_cover_capture history a token:
 AccountsFor history a ->In token history ->
 In token(retired a) \/In token(waiting a) \/In token(cancelled a).
Proof.
 intros HA HI;apply(Permutation_in token HA)in HI.
 apply in_app_or in HI as[HI|HI];[now left|right].
 now apply in_app_or in HI.
Qed.

Theorem uncompleted_capture_is_waiting history a token:
 AccountsFor history a ->In token history ->~In token(retired a) ->~In token(cancelled a) ->In token(waiting a).
Proof.
 intros HA HI HR HC;destruct(accounts_cover_capture history a token HA HI)as[H|[H|H]];tauto.
Qed.

Theorem no_duplicate_status history a:
 AccountsFor history a ->NoDup(map token_id history) ->
 NoDup(map token_id(retired a++waiting a++cancelled a)).
Proof. intros HA HN;exact(Permutation_NoDup(Permutation_map token_id HA)HN). Qed.

Theorem accounted_pending history a:
 AccountsFor history a ->NoDup(map token_id history) ->Pending history(waiting a).
Proof.
 intros HA HN;split.
 - apply Forall_forall;intros token HI;apply(Permutation_in token(Permutation_sym HA)).
   apply in_or_app;right;apply in_or_app;now left.
 - pose proof(no_duplicate_status history a HA HN)as HS;rewrite !map_app in HS.
   exact(NoDup_app_remove_r(map token_id(waiting a))(map token_id(cancelled a))
    (NoDup_app_remove_l(map token_id(retired a))(map token_id(waiting a)++map token_id(cancelled a))HS)).
Qed.

Theorem status_accounting history a:
 AccountsFor history a ->length history=length(retired a)+length(waiting a)+length(cancelled a).
Proof.
 intro HA;pose proof(Permutation_length HA)as H;rewrite !app_length in H;lia.
Qed.

Theorem empty_accounts:AccountsFor[]empty.
Proof. constructor. Qed.
Theorem nonempty_capture_cannot_vanish token:~AccountsFor[token]empty.
Proof. intro H;apply Permutation_length in H;cbn in H;discriminate. Qed.

Section ActualBirth.
Variable p:ExtendedSV.Program.
Variable proc:ExtendedSV.Process.
Variable root:ExtendedSV.signal.
Variable word valid:ExtendedSV.Expr.
Variable pc:ExtendedSV.State->ExtendedSV.signal->option BinInt.Z.
Theorem actual_birth_accounting ev pre g a retiring cancel next:
 AccountsFor(history g)a ->advance a(observed_births p proc root word valid pc ev pre g)retiring cancel=Some next ->
 AccountsFor(history(ghost_step p proc root word valid pc ev pre g))next.
Proof.
 intros HA HS;unfold ghost_step;cbn[history];rewrite history_app_birth.
 exact(accounts_step(history g)a(observed_births p proc root word valid pc ev pre g)retiring cancel next HA HS).
Qed.
End ActualBirth.

Print Assumptions accounts_step.
Print Assumptions accounts_cover_capture.
Print Assumptions uncompleted_capture_is_waiting.
Print Assumptions no_duplicate_status.
Print Assumptions accounted_pending.
Print Assumptions status_accounting.
Print Assumptions nonempty_capture_cannot_vanish.
Print Assumptions actual_birth_accounting.
End ExtendedSVCaptureAccounting.
