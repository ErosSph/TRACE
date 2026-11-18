(** Design-neutral present-state register scoreboard.
    Queue order is oldest first; values are pending ISA update values, not a
    promise about any future execution. Register zero is immutable. *)
From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.
Module PendingRegisterScoreboard.
Section Values.
Context {V:Type} (zero:V).
Definition RegisterFile:=Z->V.
Definition PendingWrite:=(Z*V)%type.
Definition apply_write (rf:RegisterFile)(w:PendingWrite):RegisterFile:=
 fun rs=>if Z.eqb rs 0 then zero else
 if Z.eqb rs(fst w) then snd w else rf rs.
Fixpoint overlay (rf:RegisterFile)(pending:list PendingWrite):RegisterFile:=
 match pending with []=>rf|w::ws=>overlay(apply_write rf w)ws end.
Fixpoint newest (rs:Z)(pending:list PendingWrite):option V:=
 match pending with
 |[]=>None
 |w::ws=>match newest rs ws with
   |Some v=>Some v
   |None=>if Z.eqb rs(fst w)then Some(snd w)else None end
 end.
Lemma overlay_append rf xs ys:
 overlay rf(xs++ys)=overlay(overlay rf xs)ys.
Proof. revert rf;induction xs;intros;cbn;[reflexivity|apply IHxs]. Qed.
Lemma overlay_retire rf w ws:overlay rf(w::ws)=overlay(apply_write rf w)ws.
Proof. reflexivity. Qed.
Lemma overlay_zero rf ws:rf 0=zero->overlay rf ws 0=zero.
Proof.
 revert rf;induction ws;intros rf H;[exact H|].
 apply IHws. reflexivity.
Qed.
Theorem newest_pending_source rf ws rs:rs<>0->
 overlay rf ws rs=match newest rs ws with Some v=>v|None=>rf rs end.
Proof.
 revert rf;induction ws as[|[rd v]ws IH];intros rf H;[reflexivity|].
 cbn[overlay newest]. rewrite IH by exact H.
 destruct(newest rs ws);[reflexivity|].
 unfold apply_write;cbn. assert((rs=?0)=false)by(now apply Z.eqb_neq).
 rewrite H0. destruct(rs=?rd);reflexivity.
Qed.
(** Two pending stages: MEM is older, EX is newer. *)
Theorem two_stage_priority rf mem ex rs:rs<>0->
 overlay rf[mem;ex]rs=
 if rs=?fst ex then snd ex else if rs=?fst mem then snd mem else rf rs.
Proof.
 intro H. rewrite newest_pending_source by exact H.
 cbn[newest]. destruct(rs=?fst ex), (rs=?fst mem);reflexivity.
Qed.
Definition Related (physical architectural:RegisterFile)(pending:list PendingWrite):Prop:=
 forall rs, architectural rs=overlay physical pending rs.
Definition stage_writes (slot:option PendingWrite):list PendingWrite:=
 match slot with None=>[]|Some w=>[w]end.
Definition stage_hit rs (slot:option PendingWrite):option V:=
 match slot with None=>None|Some(rd,v)=>if rs=?rd then Some v else None end.
Theorem optional_stage_priority rf mem ex rs:rs<>0->
 overlay rf(stage_writes mem++stage_writes ex)rs=
 match stage_hit rs ex with Some v=>v|None=>
 match stage_hit rs mem with Some v=>v|None=>rf rs end end.
Proof.
 intro H. destruct mem as[[mr mv]|],ex as[[er ev]|];
 rewrite newest_pending_source by exact H;
 cbn[stage_writes stage_hit newest app fst snd];
 repeat match goal with |- context[Z.eqb ?x ?y]=>destruct(Z.eqb x y)end;reflexivity.
Qed.
(** Retiring the oldest update changes the physical bank and removes exactly
    that update; the logical architectural register view is unchanged. *)
Theorem retirement_preserves_related physical architectural w ws:
 Related physical architectural(w::ws)->Related(apply_write physical w)architectural ws.
Proof. intros H rs;exact(H rs). Qed.
Theorem admission_preserves_related physical architectural ws w:
 Related physical architectural ws->
 Related physical(apply_write architectural w)(ws++[w]).
Proof.
 intros H rs. unfold Related in H. rewrite overlay_append.
 cbn[overlay]. unfold apply_write. destruct(rs=?0);[reflexivity|].
 destruct(rs=?fst w);[reflexivity|apply H].
Qed.
End Values.
Print Assumptions newest_pending_source.
Print Assumptions retirement_preserves_related.
Print Assumptions admission_preserves_related.
End PendingRegisterScoreboard.
