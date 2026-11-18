(** Generic stage-wise pipeline relation (design-independent, ISA-independent).

    [StagesRel effect R i a stages b]: walking the stage tags oldest first from index
    [i], every tagged token [t] at stage [k] satisfies the design's per-stage
    relation [R k t cut] at its cut (the state after all older tokens), its
    effect advances the cut, and the walk ends at [b]. It implies the ordered
    effect chain of Codex's template.

    Proved once here:
    - the three cycle shapes (advance / bubble j / freeze) carry [StagesRel]
      from the old cycle to the new one, given only per-index transport facts
      ("stage k's relation becomes stage k-1's", ...) and the admitted token's
      relation at the frontier;
    - forwarding: the register value at a cut equals the value forwarded from
      the older stages' write payloads (oldest to youngest, the youngest
      writer wins) on top of the retired register value, for any number of
      forwarding sources (including none). *)
From Coq Require Import List Lia Arith.
Require Import Ex.External.CPUGeneratedJointTemplate Ex.External.CPUPipelineQueue.
Import ListNotations CPUGeneratedJointTemplate CPUPipelineQueue.

Module CPUPipelineStages.
Section Stages.
Context {Arch Token Reg Val:Type}.

Inductive StagesRel(effect:Token->Arch->option Arch)(R:nat->Token->Arch->Prop):nat->Arch->list(option Token)->Arch->Prop:=
| sr_nil:forall i a,StagesRel effect R i a [] a
| sr_none:forall i a rest b,StagesRel effect R(S i)a rest b->StagesRel effect R i a(None::rest)b
| sr_some:forall i a t c rest b,effect t a=Some c->R i t a->StagesRel effect R(S i)c rest b->
   StagesRel effect R i a(Some t::rest)b.

Lemma sr_nil_inv(effect:Token->Arch->option Arch) R i a b:StagesRel effect R i a [] b->b=a.
Proof. intro H;inversion H;reflexivity. Qed.
Lemma sr_none_inv(effect:Token->Arch->option Arch) R i a rest b:StagesRel effect R i a(None::rest)b->StagesRel effect R(S i)a rest b.
Proof. intro H;inversion H;subst;assumption. Qed.
Lemma sr_some_inv(effect:Token->Arch->option Arch) R i a t rest b:StagesRel effect R i a(Some t::rest)b->
 exists c,effect t a=Some c/\R i t a/\StagesRel effect R(S i)c rest b.
Proof. intro H;inversion H;subst;eauto. Qed.

Theorem stages_chain(effect:Token->Arch->option Arch) R i a l b:StagesRel effect R i a l b->EffectChain effect a(present l)b.
Proof. induction 1 as[i a|i a rest b HS IH|i a t c rest b HE HR HS IH].
 - constructor.
 - rewrite present_none;exact IH.
 - rewrite present_cons;cbn[opt app];econstructor;[exact HE|exact IH].
Qed.

Theorem stages_empty(effect:Token->Arch->option Arch) R i a n:StagesRel effect R i a(repeat None n)a.
Proof. revert i;induction n as[|n IH];intro i;cbn[repeat];constructor;apply IH. Qed.

Lemma relabel(effect:Token->Arch->option Arch) R R' d l:forall i a b,StagesRel effect R(i+d)a l b->
 (forall k t c,i+d<=k->k<i+d+length l->R k t c->R'(k-d)t c)->StagesRel effect R' i a l b.
Proof. induction l as[|o l IH];intros i a b H HT.
 - apply (sr_nil_inv effect) in H;subst;constructor.
 - destruct o as[t|].
   + destruct(sr_some_inv effect _ _ _ _ _ _ H)as[c[HE[HR HS]]].
     econstructor;[exact HE| |].
     * replace i with(i+d-d)by lia;apply HT;[lia|cbn[length];lia|exact HR].
     * apply(IH(S i));[replace(S i+d)with(S(i+d))by lia;exact HS|].
       intros k t' c' H1 H2 H3;apply HT;[lia|cbn[length];lia|exact H3].
   + apply (sr_none_inv effect) in H;constructor.
     apply(IH(S i));[replace(S i+d)with(S(i+d))by lia;exact H|].
     intros k t' c' H1 H2 H3;apply HT;[lia|cbn[length];lia|exact H3].
Qed.

Lemma app_split(effect:Token->Arch->option Arch) R l1:forall l2 i a b,StagesRel effect R i a(l1++l2)b->
 exists m,StagesRel effect R i a l1 m/\StagesRel effect R(i+length l1)m l2 b.
Proof. induction l1 as[|o l1 IH];intros l2 i a b H.
 - exists a;split;[constructor|rewrite Nat.add_0_r;exact H].
 - cbn[app]in H;destruct o as[t|].
   + destruct(sr_some_inv effect _ _ _ _ _ _ H)as[c[HE[HR HS]]].
     destruct(IH l2(S i)c b HS)as[m[H1 H2]].
     exists m;split;[econstructor;eassumption|].
     cbn[length];replace(i+S(length l1))with(S i+length l1)by lia;exact H2.
   + apply (sr_none_inv effect) in H;destruct(IH l2(S i)a b H)as[m[H1 H2]].
     exists m;split;[constructor;exact H1|].
     cbn[length];replace(i+S(length l1))with(S i+length l1)by lia;exact H2.
Qed.

Lemma app_join(effect:Token->Arch->option Arch) R l1:forall l2 i a m b,StagesRel effect R i a l1 m->StagesRel effect R(i+length l1)m l2 b->
 StagesRel effect R i a(l1++l2)b.
Proof. induction l1 as[|o l1 IH];intros l2 i a m b H1 H2.
 - apply (sr_nil_inv effect) in H1;subst;rewrite Nat.add_0_r in H2;exact H2.
 - cbn[app length]in *;destruct o as[t|].
   + destruct(sr_some_inv effect _ _ _ _ _ _ H1)as[c[HE[HR HS]]].
     econstructor;[exact HE|exact HR|].
     apply(IH l2(S i)c m b HS);replace(S i+length l1)with(i+S(length l1))by lia;exact H2.
   + apply (sr_none_inv effect) in H1;constructor.
     apply(IH l2(S i)a m b H1);replace(S i+length l1)with(i+S(length l1))by lia;exact H2.
Qed.

Lemma head_split(effect:Token->Arch->option Arch) R retired o rest frontier:StagesRel effect R 0 retired(o::rest)frontier->
 exists advanced,EffectChain effect retired(opt o)advanced/\StagesRel effect R 1 advanced rest frontier.
Proof. intro H;destruct o as[t|].
 - destruct(sr_some_inv effect _ _ _ _ _ _ H)as[c[HE[_ HS]]].
   exists c;split;[econstructor;[exact HE|constructor]|exact HS].
 - exists retired;split;[constructor|exact(sr_none_inv effect _ _ _ _ _ H)].
Qed.

(** The three cycle shapes of [CPUPipelineQueue.Step], with their per-index
    transport facts and admission fact. *)
Inductive Shape:=Advance(admitted:option Token)|Bubble(j:nat)|Freeze.
Definition shape_admitted(sh:Shape):option Token:=match sh with Advance a=>a|_=>None end.
Definition shape_post(sh:Shape)(old:list(option Token)):list(option Token):=match sh with
 |Advance a=>tl(old++[a])|Bubble j=>firstn j(tl old)++None::skipn(S j)old|Freeze=>old end.
Definition shape_retiring(sh:Shape)(old:list(option Token)):list Token:=match sh with
 |Advance a=>opt(hd None(old++[a]))|Bubble _=>opt(hd None old)|Freeze=>[] end.
Definition shape_transport(sh:Shape)(R R':nat->Token->Arch->Prop)(old:list(option Token)):Prop:=
 match sh with
 |Advance _=>forall k t c,1<=k->R k t c->R'(k-1)t c
 |Bubble j=>j<length old/\(forall k t c,1<=k<=j->R k t c->R'(k-1)t c)/\
   (forall k t c,j<k->R k t c->R' k t c)
 |Freeze=>forall k t c,R k t c->R' k t c end.
Definition shape_admission(effect:Token->Arch->option Arch)(sh:Shape)(R':nat->Token->Arch->Prop)(old:list(option Token))(frontier next:Arch):Prop:=
 match shape_admitted sh with
 |Some t=>effect t frontier=Some next/\R'(pred(length old))t frontier
 |None=>next=frontier end.

Theorem shape_step(sh:Shape)(R R':nat->Token->Arch->Prop)(old:list(option Token)):
 shape_transport sh R R' old->Step old(shape_admitted sh)(shape_post sh old)(shape_retiring sh old).
Proof. destruct sh as[a|j|];cbn[shape_transport shape_admitted shape_post shape_retiring];intro H.
 - apply step_advance.
 - destruct H as[H _];apply step_bubble;exact H.
 - apply step_freeze.
Qed.

Theorem shape_stages(effect:Token->Arch->option Arch)(sh:Shape)(R R':nat->Token->Arch->Prop)(old:list(option Token))(retired frontier next:Arch):
 StagesRel effect R 0 retired old frontier->shape_transport sh R R' old->shape_admission effect sh R' old frontier next->
 exists advanced,EffectChain effect retired(shape_retiring sh old)advanced/\
  StagesRel effect R' 0 advanced(shape_post sh old)next.
Proof. intros H HT HA.
 destruct sh as[adm|j|];unfold shape_transport,shape_admission in *;cbn[shape_admitted shape_post shape_retiring]in *.
 - destruct old as[|o rest].
   + apply (sr_nil_inv effect) in H;subst frontier;destruct adm as[t|];cbn;cbn iota in HA.
     * destruct HA as[HE _];exists next;split;[econstructor;[exact HE|constructor]|constructor].
     * subst next;exists retired;split;constructor.
   + change(tl((o::rest)++[adm]))with(rest++[adm]).
     change(hd None((o::rest)++[adm]))with o.
     destruct(head_split effect R retired o rest frontier H)as[advanced[HC HS]].
     exists advanced;split;[exact HC|].
     apply (app_join effect) with(m:=frontier).
     * apply(relabel effect R R' 1 rest 0 advanced frontier HS).
       intros k t c H1 _ H3;exact(HT k t c H1 H3).
     * cbn[length pred]in HA;destruct adm as[t|];cbn iota in HA.
       -- destruct HA as[HE HR];econstructor;[exact HE|exact HR|constructor].
       -- subst next;constructor;constructor.
 - subst next;destruct HT as[HJ[H1T H2T]].
   destruct old as[|o rest];[cbn in HJ;lia|].
   cbn[length]in HJ.
   change(tl(o::rest))with rest.
   change(hd None(o::rest))with o.
   change(skipn(S j)(o::rest))with(skipn j rest).
   destruct(head_split effect R retired o rest frontier H)as[advanced[HC HS]].
   rewrite<-(firstn_skipn j rest)in HS.
   destruct(app_split effect R(firstn j rest)(skipn j rest)1 advanced frontier HS)as[m[HA1 HA2]].
   assert(HL:length(firstn j rest)=j)by(apply firstn_length_le;lia).
   rewrite HL in HA2.
   exists advanced;split;[exact HC|].
   apply (app_join effect) with(m:=m).
   + apply(relabel effect R R' 1(firstn j rest)0 advanced m HA1).
     intros k t c Hk1 Hk2 HR;apply H1T;[lia|exact HR].
   + rewrite HL;constructor.
     apply(relabel effect R R' 0(skipn j rest)(S j)m frontier).
     * replace(S j+0)with(1+j)by lia;exact HA2.
     * intros k t c Hk1 _ HR;rewrite Nat.sub_0_r;apply H2T;[lia|exact HR].
 - subst next;exists retired;split;[constructor|].
   apply(relabel effect R R' 0 old 0 retired frontier H).
   intros k t c _ _ HR;rewrite Nat.sub_0_r;exact(HT k t c HR).
Qed.

(** Forwarding over any number of older stages. [W k] is stage k's write
    payload (destination register and value) as the design's RTL presents it;
    [forward_from] is the youngest-writer-wins selection a forwarding mux
    implements (no stage = plain register-file read). *)
Definition upd(reg_eqb:Reg->Reg->bool)(w:option(Reg*Val))(r:Reg)(base:Val):Val:=
 match w with Some(rd,v)=>if reg_eqb rd r then v else base|None=>base end.
Fixpoint forward_from(reg_eqb:Reg->Reg->bool)(W:nat->option(Reg*Val))(i:nat)(l:list(option Token))(r:Reg)(base:Val):Val:=
 match l with
 |[]=>base
 |None::l'=>forward_from reg_eqb W(S i)l' r base
 |Some _::l'=>forward_from reg_eqb W(S i)l' r(upd reg_eqb(W i)r base) end.

Theorem forwarding_correct(effect:Token->Arch->option Arch)(reg:Arch->Reg->Val)(reg_eqb:Reg->Reg->bool)(R:nat->Token->Arch->Prop)(W:nat->option(Reg*Val))(i:nat)(a:Arch)
 (l:list(option Token))(b:Arch):
 StagesRel effect R i a l b->
 (forall k t c y,R k t c->effect t c=Some y->forall r,reg y r=upd reg_eqb(W k)r(reg c r))->
 forall r,reg b r=forward_from reg_eqb W i l r(reg a r).
Proof. induction 1 as[i a|i a rest b HS IH|i a t c rest b HE HR HS IH];intros HW r;cbn[forward_from].
 - reflexivity.
 - exact(IH HW r).
 - rewrite(IH HW r),(HW i t a c HR HE r);reflexivity.
Qed.
End Stages.
End CPUPipelineStages.
Print Assumptions CPUPipelineStages.stages_chain.
Print Assumptions CPUPipelineStages.stages_empty.
Print Assumptions CPUPipelineStages.shape_step.
Print Assumptions CPUPipelineStages.shape_stages.
Print Assumptions CPUPipelineStages.forwarding_correct.
