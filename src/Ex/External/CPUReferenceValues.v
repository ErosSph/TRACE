(** Compute a token's reference value by executing its actual queue prefix.
    Token keys distinguish dynamic instruction instances, not program PCs. *)
From Coq Require Import List Arith Lia.
Require Import Ex.External.CPUGeneratedJointTemplate Ex.External.CPUReferenceCuts.
Import ListNotations CPUGeneratedJointTemplate CPUReferenceCuts.
Module CPUReferenceValues.
Section Values.
Context {Architecture Token Value:Type}.
Variable effect:Token->Architecture->option Architecture.
Variable key:Token->nat.
Variable interpret:Token->Architecture->option Value.

Fixpoint lookup (initial:Architecture)(pending:list Token)(token:Token):option Value:=
 match pending with
 | []=>None
 | first::rest=>if Nat.eqb(key first)(key token) then interpret first initial else
   match effect first initial with Some next=>lookup next rest token|None=>None end
 end.

Theorem at_head initial token rest:
 lookup initial(token::rest)token=interpret token initial.
Proof. cbn[lookup];now rewrite Nat.eqb_refl. Qed.

Theorem committed_prefix initial committed after kept token:
 EffectChain effect initial committed after ->
 Forall(fun earlier=>key earlier<>key token)committed ->
 lookup initial(committed++kept)token=lookup after kept token.
Proof.
 intro HC;induction HC as[a|a t b ts c HE HC IH];intro HKeys;[reflexivity|].
 inversion HKeys;subst;cbn[app lookup].
 assert(HNeq:Nat.eqb(key t)(key token)=false)by(now apply Nat.eqb_neq).
 rewrite HNeq,HE;now apply IH.
Qed.

Theorem append_keeps_existing initial kept extra token:
 In(key token)(map key kept) ->
 lookup initial(kept++extra)token=lookup initial kept token.
Proof.
 revert initial;induction kept as[|first rest IH];intros initial HI;[contradiction|].
 cbn[app lookup];destruct(Nat.eqb(key first)(key token))eqn:HE;[reflexivity|].
 destruct(effect first initial)as[next|];[|reflexivity].
 apply IH;cbn[map]in HI;destruct HI as[HI|HI];[|exact HI].
 apply Nat.eqb_neq in HE;contradiction.
Qed.

Theorem at_reference_cut initial pending index token before:
 NoDup(map key pending) ->BeforeToken effect initial pending index token before ->
 lookup initial pending token=interpret token before.
Proof.
 revert initial index before;induction pending as[|first rest IH];intros initial index before HN[HT[HB HC]].
 - destruct index;discriminate.
 - inversion HN as[|head tail HNot HRest];subst;destruct index as[|index].
   + cbn in HT;inversion HT;subst token;cbn[firstn]in HC;inversion HC;subst before;apply at_head.
   + cbn[nth_error]in HT;cbn[firstn]in HC;
     inversion HC as[|a t next ts c HE HChain];subst.
     cbn[lookup].
     assert(HNeq:Nat.eqb(key first)(key token)=false).
     { apply Nat.eqb_neq;intro HKeyEq;apply HNot;rewrite HKeyEq;apply in_map;now apply nth_error_In in HT. }
     rewrite HNeq,HE;apply IH with(index:=index);[exact HRest|].
     split;[exact HT|];split;[cbn in HB;lia|assumption].
Qed.
End Values.
End CPUReferenceValues.
Print Assumptions CPUReferenceValues.at_head.
Print Assumptions CPUReferenceValues.committed_prefix.
Print Assumptions CPUReferenceValues.append_keeps_existing.
Print Assumptions CPUReferenceValues.at_reference_cut.
