(** Context-aware stage transport (design-independent, ISA-independent).

    [CPUPipelineStages.shape_transport] asks for per-index facts
    [R k t c -> R' k' t c] for an arbitrary cut [c]. A design with operand
    forwarding needs more: that [c] is the token's ACTUAL cut, and the
    relations of all OLDER stages up to that cut (the forwarding sources).
    [shape_transport_ctx] provides exactly that: the old stage list splits as
    [l1 ++ Some t :: l2] with [length l1 = k], and the older prefix [l1]
    satisfies [StagesRel] from the retired state to [c]. Combined with
    [forwarding_correct] on that prefix, the register value at [c] is the
    value forwarded from the older stages' write payloads.

    [shape_stages_ctx] carries [StagesRel] through any shape under these
    weaker obligations; it is proved by annotating the old relation with each
    token's position and prefix and reusing [shape_stages]. The plain
    [shape_transport] implies the context version ([transport_ctx_of_plain]),
    so nothing proved with the plain interface is lost. *)
From Coq Require Import List Lia Arith.
Require Import Ex.External.CPUGeneratedJointTemplate Ex.External.CPUPipelineQueue Ex.External.CPUPipelineStages.
Import ListNotations CPUGeneratedJointTemplate CPUPipelineQueue CPUPipelineStages.

Module CPUPipelineStagesContext.
Section Context.
Context {Arch Token:Type}.

(** A transport family: for every token [t] at position [length l1] of [old]
    (an index satisfying [P]) with actual cut [c], [R] at that index implies
    [R'] at [dest] of it. *)
Definition TransportFrom(effect:Token->Arch->option Arch)(R R':nat->Token->Arch->Prop)
 (retired:Arch)(old:list(option Token))(P:nat->Prop)(dest:nat->nat):Prop:=
 forall l1 t l2 c,old=l1++Some t::l2->P(length l1)->StagesRel effect R 0 retired l1 c->
  R(length l1)t c->R'(dest(length l1))t c.

Definition shape_transport_ctx(effect:Token->Arch->option Arch)(sh:Shape(Token:=Token))
 (R R':nat->Token->Arch->Prop)(retired:Arch)(old:list(option Token)):Prop:=
 match sh with
 |Advance _=>TransportFrom effect R R' retired old(fun k=>1<=k)(fun k=>k-1)
 |Bubble j=>j<length old/\TransportFrom effect R R' retired old(fun k=>1<=k<=j)(fun k=>k-1)/\
   TransportFrom effect R R' retired old(fun k=>j<k)(fun k=>k)
 |Freeze=>TransportFrom effect R R' retired old(fun _=>True)(fun k=>k) end.

(** Each token annotated with its position in [whole] and its older prefix. *)
Definition annotated(effect:Token->Arch->option Arch)(R:nat->Token->Arch->Prop)(retired:Arch)
 (whole:list(option Token)):nat->Token->Arch->Prop:=fun k t c=>
 R k t c/\exists l1 l2,whole=l1++Some t::l2/\length l1=k/\StagesRel effect R 0 retired l1 c.

Lemma annotate_gen(effect:Token->Arch->option Arch)(R:nat->Token->Arch->Prop)(retired:Arch)
 (whole l:list(option Token)):forall pre_l i a b,
 StagesRel effect R i a l b->pre_l++l=whole->length pre_l=i->StagesRel effect R 0 retired pre_l a->
 StagesRel effect(annotated effect R retired whole)i a l b.
Proof. induction l as[|o l IH];intros pre_l i a b H HW HL HP.
 - apply(sr_nil_inv effect)in H;subst;constructor.
 - destruct o as[t|].
   + destruct(sr_some_inv effect _ _ _ _ _ _ H)as[c[HE[HR HS]]].
     econstructor;[exact HE| |].
     * split;[exact HR|exists pre_l,l;split;[symmetry;exact HW|split;[exact HL|exact HP]]].
     * apply(IH(pre_l++[Some t])(S i)c b HS).
       -- rewrite<-app_assoc;exact HW.
       -- rewrite app_length;cbn;lia.
       -- apply(app_join effect)with(m:=a);[exact HP|].
          rewrite Nat.add_0_l,HL;econstructor;[exact HE|exact HR|constructor].
   + apply(sr_none_inv effect)in H;constructor.
     apply(IH(pre_l++[None])(S i)a b H).
     * rewrite<-app_assoc;exact HW.
     * rewrite app_length;cbn;lia.
     * apply(app_join effect)with(m:=a);[exact HP|].
       rewrite Nat.add_0_l,HL;constructor;constructor.
Qed.

Theorem annotate(effect:Token->Arch->option Arch)(R:nat->Token->Arch->Prop)(retired frontier:Arch)
 (old:list(option Token)):
 StagesRel effect R 0 retired old frontier->StagesRel effect(annotated effect R retired old)0 retired old frontier.
Proof. intro H;exact(annotate_gen effect R retired old old[]0 retired frontier H eq_refl eq_refl(sr_nil effect R 0 retired)). Qed.

Lemma transport_annotated(effect:Token->Arch->option Arch)(R R':nat->Token->Arch->Prop)(retired:Arch)
 (old:list(option Token))(P:nat->Prop)(dest:nat->nat):
 TransportFrom effect R R' retired old P dest->
 forall k t c,P k->annotated effect R retired old k t c->R'(dest k)t c.
Proof. intros HT k t c HP[HR[l1[l2[HO[HL HS]]]]];subst k;exact(HT l1 t l2 c HO HP HS HR). Qed.

Theorem shape_step_ctx(effect:Token->Arch->option Arch)(sh:Shape(Token:=Token))
 (R R':nat->Token->Arch->Prop)(retired:Arch)(old:list(option Token)):
 shape_transport_ctx effect sh R R' retired old->Step old(shape_admitted sh)(shape_post sh old)(shape_retiring sh old).
Proof. destruct sh as[a|j|];cbn[shape_transport_ctx shape_admitted shape_post shape_retiring];intro H.
 - apply step_advance.
 - destruct H as[H _];apply step_bubble;exact H.
 - apply step_freeze.
Qed.

Theorem shape_stages_ctx(effect:Token->Arch->option Arch)(sh:Shape(Token:=Token))
 (R R':nat->Token->Arch->Prop)(old:list(option Token))(retired frontier next:Arch):
 StagesRel effect R 0 retired old frontier->shape_transport_ctx effect sh R R' retired old->
 shape_admission effect sh R' old frontier next->
 exists advanced,EffectChain effect retired(shape_retiring sh old)advanced/\
  StagesRel effect R' 0 advanced(shape_post sh old)next.
Proof. intros H HT HA.
 apply(shape_stages effect sh(annotated effect R retired old)R' old retired frontier next(annotate effect R retired frontier old H)).
 - destruct sh as[a|j|];cbn[shape_transport_ctx]in HT;unfold shape_transport.
   + intros k t c HK HR;exact(transport_annotated effect R R' retired old _ _ HT k t c HK HR).
   + destruct HT as[HJ[H1 H2]];split;[exact HJ|split].
     * intros k t c HK HR;exact(transport_annotated effect R R' retired old _ _ H1 k t c HK HR).
     * intros k t c HK HR;exact(transport_annotated effect R R' retired old _ _ H2 k t c HK HR).
   + intros k t c HR;exact(transport_annotated effect R R' retired old _ _ HT k t c I HR).
 - exact HA.
Qed.

(** The plain interface implies the context version. *)
Theorem transport_ctx_of_plain(effect:Token->Arch->option Arch)(sh:Shape(Token:=Token))
 (R R':nat->Token->Arch->Prop)(retired:Arch)(old:list(option Token)):
 shape_transport sh R R' old->shape_transport_ctx effect sh R R' retired old.
Proof. destruct sh as[a|j|];unfold shape_transport;cbn[shape_transport_ctx];unfold TransportFrom.
 - intros HT l1 t l2 c _ HP _ HR;exact(HT _ t c HP HR).
 - intros[HJ[H1 H2]];split;[exact HJ|split];intros l1 t l2 c _ HP _ HR;[exact(H1 _ t c HP HR)|exact(H2 _ t c HP HR)].
 - intros HT l1 t l2 c _ _ _ HR;exact(HT _ t c HR).
Qed.
End Context.
End CPUPipelineStagesContext.
Print Assumptions CPUPipelineStagesContext.annotate.
Print Assumptions CPUPipelineStagesContext.shape_step_ctx.
Print Assumptions CPUPipelineStagesContext.shape_stages_ctx.
Print Assumptions CPUPipelineStagesContext.transport_ctx_of_plain.
