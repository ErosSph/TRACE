(** Pending is constructed from admission/retirement events, not recovered
    from a previously proved CPU invariant. A successful checker result is
    NOT assumed for a CPU: actual RTL correspondence is a separate obligation.
    Cancellation is explicit, never silently treated as an ISA step. *)
From Coq Require Import List Arith Lia.
Import ListNotations.
Module CheckedPendingQueue.
Section Queue.
Context {Token : Type}.
Variable token_eq_dec : forall x y : Token, {x = y} + {x <> y}.

Fixpoint consume (retiring queue : list Token) : option (list Token) :=
 match retiring, queue with
 | [], _ => Some queue
 | _ :: _, [] => None
 | x :: xs, y :: ys =>
   if token_eq_dec x y then consume xs ys else None
 end.

Theorem consume_sound retiring : forall queue kept,
 consume retiring queue = Some kept -> queue = retiring ++ kept.
Proof.
 induction retiring as [|x xs IH]; intros queue kept H; cbn in H.
 - inversion H; reflexivity.
 - destruct queue as [|y ys]; [discriminate|].
   destruct (token_eq_dec x y); [subst y|discriminate].
   cbn. f_equal. now apply IH.
Qed.

Theorem consume_complete retiring kept :
 consume retiring (retiring ++ kept) = Some kept.
Proof.
 induction retiring as [|x xs IH]; cbn; [reflexivity|].
 destruct (token_eq_dec x x); [exact IH|contradiction].
Qed.

Definition step (queue admitted retiring : list Token) (cancel : nat)
 : option (list Token * list Token) :=
 match consume retiring (queue ++ admitted) with
 | None => None
 | Some rest =>
   if cancel <=? length rest then
     Some (firstn (length rest - cancel) rest,
           skipn (length rest - cancel) rest)
   else None
 end.

Theorem step_partition queue admitted retiring cancel kept killed :
 step queue admitted retiring cancel = Some (kept, killed) ->
 queue ++ admitted = retiring ++ (kept ++ killed).
Proof.
 unfold step. destruct (consume retiring (queue ++ admitted)) as [rest|] eqn:H;
   [|discriminate].
 destruct (cancel <=? length rest); [|discriminate].
 intro HE. inversion HE; subst kept killed.
 rewrite (firstn_skipn (length rest - cancel) rest).
 now apply consume_sound.
Qed.

Theorem step_no_cancel_streaming queue admitted retiring kept killed :
 step queue admitted retiring 0 = Some (kept, killed) ->
 killed = [] /\ queue ++ admitted = retiring ++ kept.
Proof.
 unfold step. destruct (consume retiring (queue ++ admitted)) as [rest|] eqn:H;
   [|discriminate].
 cbn [Nat.leb]. rewrite Nat.sub_0_r, firstn_all, skipn_all.
 intro HE. inversion HE; subst. split; [reflexivity|].
 now apply consume_sound.
Qed.

Theorem step_accounting queue admitted retiring cancel kept killed :
 step queue admitted retiring cancel = Some (kept, killed) ->
 length queue + length admitted =
 length retiring + length kept + length killed.
Proof.
 intro H. pose proof (step_partition _ _ _ _ _ _ H) as HE.
 apply (f_equal (@length Token)) in HE.
 repeat rewrite app_length in HE. lia.
Qed.

Theorem step_cancel_count queue admitted retiring cancel kept killed :
 step queue admitted retiring cancel = Some (kept, killed) ->
 length killed = cancel.
Proof.
 unfold step. destruct (consume retiring (queue ++ admitted)) as [rest|];
   [|discriminate].
 destruct (cancel <=? length rest) eqn:HC; [|discriminate].
 intro H. inversion H; subst. rewrite skipn_length.
 apply Nat.leb_le in HC. lia.
Qed.

Theorem empty_boot : consume [] [] = Some [].
Proof. reflexivity. Qed.

Theorem rejects_wrong_head x y rest :
 x <> y -> consume [x] (y :: rest) = None.
Proof. intro H. cbn. destruct (token_eq_dec x y); [contradiction|reflexivity]. Qed.
End Queue.

(** Slot extraction is a candidate physical projection, not a proof that a
    selected carrier/PC/valid tuple represents a real architectural token. *)
Section Slots.
Context {State Token : Type}.
Variable observe_slot : nat -> State -> option Token.
Fixpoint snapshot (slots : list nat) (s : State) : list Token :=
 match slots with
 | [] => []
 | slot :: rest => match observe_slot slot s with
   | Some token => token :: snapshot rest s
   | None => snapshot rest s
   end
 end.

Theorem snapshot_capacity slots s : length (snapshot slots s) <= length slots.
Proof.
 induction slots as [|slot rest IH]; cbn; [lia|].
 destruct (observe_slot slot s); cbn; lia.
Qed.

Theorem snapshot_empty slots s :
 (forall slot, In slot slots -> observe_slot slot s = None) -> snapshot slots s = [].
Proof.
 induction slots as [|slot rest IH]; cbn; intros H; [reflexivity|].
 rewrite H by now left. apply IH. intros; apply H; now right.
Qed.

Theorem snapshot_extensional slots s t :
 (forall slot, In slot slots -> observe_slot slot s = observe_slot slot t) ->
 snapshot slots s = snapshot slots t.
Proof.
 induction slots as [|slot rest IH]; cbn; intros H; [reflexivity|].
 rewrite H by now left. destruct (observe_slot slot t); [f_equal|];
 apply IH; intros; apply H; now right.
Qed.
End Slots.
Print Assumptions step_partition.
Print Assumptions step_no_cancel_streaming.
Print Assumptions step_accounting.
Print Assumptions snapshot_extensional.
End CheckedPendingQueue.
