(** Compute a reference cut from a captured token and an ordered pending queue.
    This does not certify that the queue is the CPU's architectural order. *)
From Coq Require Import List Arith Lia.
Require Import Ex.External.CPUReferenceCuts Ex.External.CPUGeneratedJointTemplate.
Import ListNotations CPUReferenceCuts CPUGeneratedJointTemplate.
Module CPUComputedReferenceCut.
Section Compute.
Context {Architecture Token:Type}.
Variable effect:Token->Architecture->option Architecture.
Variable same:forall x y:Token,{x=y}+{x<>y}.

Fixpoint lookup_before (wanted:Token) (initial:Architecture) (pending:list Token)
 : option(nat*Architecture) :=
 match pending with
 | []=>None
 | head::rest=>
   if same wanted head then Some(0,initial)
   else match effect head initial with
   | None=>None
   | Some next=>match lookup_before wanted next rest with
     | None=>None |Some(index,before)=>Some(S index,before) end
   end
 end.

Theorem lookup_before_sound wanted pending initial index before:
 lookup_before wanted initial pending=Some(index,before) ->
 BeforeToken effect initial pending index wanted before.
Proof.
 revert initial index before;induction pending as[|head rest IH];
 intros initial index before;cbn[lookup_before];[discriminate|].
 destruct(same wanted head)as[HE|HN].
 - intro H;inversion H;subst;split;[reflexivity|].
   split;[cbn;lia|constructor].
 - destruct(effect head initial)as[next|]eqn:HS;[|discriminate].
   destruct(lookup_before wanted next rest)as[[pos state]|]eqn:HC;[|discriminate].
   intro H;inversion H;subst index before.
   destruct(IH next pos state HC)as[HT [HB HP]].
   split;[exact HT|];split;[cbn;lia|cbn; econstructor;eassumption].
Qed.

Theorem lookup_stops_before_target wanted initial rest:
 lookup_before wanted initial(wanted::rest)=Some(0,initial).
Proof. cbn[lookup_before];destruct(same wanted wanted);[reflexivity|contradiction]. Qed.

Theorem lookup_before_unique wanted pending initial index left right:
 lookup_before wanted initial pending=Some(index,left) ->
 BeforeToken effect initial pending index wanted right ->left=right.
Proof. intros HL HR;eapply fields_cannot_choose_different_states;
 [eapply lookup_before_sound;exact HL|exact HR]. Qed.

Theorem lookup_before_complete wanted pending initial index before:
 NoDup pending ->BeforeToken effect initial pending index wanted before ->
 lookup_before wanted initial pending=Some(index,before).
Proof.
 revert initial index before;induction pending as[|head rest IH];
 intros initial index before HN [HT [HB HP]].
 - destruct index;discriminate.
 - inversion HN as[|h ts HH HR];subst h ts.
   destruct index as[|index].
   + cbn in HT;inversion HT;subst head.
     cbn in HP;inversion HP;subst;apply lookup_stops_before_target.
   + cbn in HT,HP.
     assert(HD:wanted<>head).
     { intro HE;subst head;apply HH;eapply nth_error_In;exact HT. }
     inversion HP as[|a t middle tokens c HS HC];subst.
     cbn[lookup_before];destruct(same wanted head)as[HE|HE];[contradiction|].
     rewrite HS.
     rewrite(IH middle index before HR).
     * reflexivity.
     * split;[exact HT|];split;[cbn in HB;lia|exact HC].
Qed.
End Compute.
Print Assumptions lookup_before_sound.
Print Assumptions lookup_stops_before_target.
Print Assumptions lookup_before_unique.
Print Assumptions lookup_before_complete.
End CPUComputedReferenceCut.
