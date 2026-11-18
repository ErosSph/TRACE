(** Multi-retirement pipeline shape (design-independent, ISA-independent).

    [CPUPipelineStages] lets at most the single oldest token retire per
    cycle. Some pipelines retire more: e.g. CV32E40P can complete a load in
    WB and retire a scalar instruction from EX in the same cycle, the EX
    instruction leaving directly without entering WB. [retire_post k adm old]
    covers this: the oldest [k] slots leave (their present tokens retire, in
    order: [retire_retiring k old]); every later slot moves forward ONE
    position (as in [Advance]); the vacated older positions become empty;
    the admitted token enters the youngest slot. [Advance adm] is [k = 1].

    Proved once: the queue equation, the stage-list length, the stage
    relation carried through the move with context-aware per-index transport
    (indices [i >= k] go to [i - 1], with the token's actual cut), and the
    retiring chain. *)
From Coq Require Import List Lia Arith.
Require Import Ex.External.CPUGeneratedJointTemplate Ex.External.CPUPipelineQueue
 Ex.External.CPUPipelineStages Ex.External.CPUPipelineStagesContext.
Import ListNotations CPUGeneratedJointTemplate CPUPipelineQueue CPUPipelineStages CPUPipelineStagesContext.

Module CPUPipelineMultiRetire.
Section MultiRetire.
Context {Arch Token:Type}.

Definition retire_post(k:nat)(adm:option Token)(old:list(option Token)):list(option Token):=
 repeat None(k-1)++skipn k old++[adm].
Definition retire_retiring(k:nat)(old:list(option Token)):list Token:=present(firstn k old).

Lemma present_repeat_none n:present(repeat(@None Token)n)=[].
Proof. induction n as[|n IH];[reflexivity|exact IH]. Qed.

Theorem retire_queue(k:nat)(adm:option Token)(old:list(option Token)):
 present old++opt adm=retire_retiring k old++present(retire_post k adm old).
Proof. unfold retire_retiring,retire_post.
 rewrite !present_app,present_repeat_none.
 rewrite<-(firstn_skipn k old)at 1;rewrite present_app.
 change(present[adm])with(opt adm++[]);rewrite app_nil_r,<-app_assoc;reflexivity. Qed.

Theorem retire_length(k:nat)(adm:option Token)(old:list(option Token)):
 1<=k<=length old->length(retire_post k adm old)=length old.
Proof. intro HK;unfold retire_post;rewrite !app_length,repeat_length,skipn_length;cbn;lia. Qed.

Theorem retire_retiring_length(k:nat)(old:list(option Token)):
 (length(retire_retiring k old)<=k)%nat.
Proof. unfold retire_retiring;revert old;induction k as[|k IH];intro old;[reflexivity|].
 destruct old as[|o rest];[cbn;lia|];cbn[firstn];rewrite present_cons.
 destruct o;cbn[opt app length];specialize(IH rest);lia. Qed.

(** Per-index transport for the move: later slots go forward one position. *)
Definition retire_transport(effect:Token->Arch->option Arch)(k:nat)(R R':nat->Token->Arch->Prop)
 (retired:Arch)(old:list(option Token)):Prop:=
 TransportFrom effect R R' retired old(fun i=>k<=i)(fun i=>i-1).

Definition retire_admission(effect:Token->Arch->option Arch)(adm:option Token)(R':nat->Token->Arch->Prop)
 (old:list(option Token))(frontier next:Arch):Prop:=
 match adm with
 |Some t=>effect t frontier=Some next/\R'(pred(length old))t frontier
 |None=>next=frontier end.

Theorem retire_stages(effect:Token->Arch->option Arch)(k:nat)(adm:option Token)
 (R R':nat->Token->Arch->Prop)(old:list(option Token))(retired frontier next:Arch):
 1<=k<=length old->
 StagesRel effect R 0 retired old frontier->
 retire_transport effect k R R' retired old->
 retire_admission effect adm R' old frontier next->
 exists advanced,EffectChain effect retired(retire_retiring k old)advanced/\
  StagesRel effect R' 0 advanced(retire_post k adm old)next.
Proof. intros HK H HT HA.
 pose proof(annotate effect R retired frontier old H)as HAn.
 assert(HAn':StagesRel effect(annotated effect R retired old)0 retired(firstn k old++skipn k old)frontier)
  by(rewrite firstn_skipn;exact HAn).
 destruct(app_split effect _(firstn k old)(skipn k old)0 retired frontier HAn')as[m[H1 H2]].
 assert(HLk:length(firstn k old)=k)by(rewrite firstn_length_le;lia).
 rewrite HLk in H2.
 exists m;split.
 { unfold retire_retiring;exact(stages_chain effect _ 0 retired _ m H1). }
 unfold retire_post.
 apply(app_join effect)with(m:=m);[apply stages_empty|].
 rewrite Nat.add_0_l,repeat_length.
 apply(app_join effect)with(m:=frontier).
 - apply(relabel effect(annotated effect R retired old)R' 1(skipn k old)(k-1)m frontier).
   + replace(k-1+1)with k by lia;exact H2.
   + intros i t c Hi1 _ HR;exact(transport_annotated effect R R' retired old _ _ HT i t c ltac:(cbv beta;lia) HR).
 - rewrite skipn_length.
   destruct adm as[t|];cbn in HA.
   + destruct HA as[HE HR'];econstructor;[exact HE| |constructor].
     replace(k-1+(length old-k))with(pred(length old))by lia;exact HR'.
   + subst next;constructor;constructor.
Qed.

(** [Advance] is the case [k = 1]. *)
Theorem advance_is_retire_one(adm:option Token)(old:list(option Token)):
 old<>[]->shape_post(Advance adm)old=retire_post 1 adm old/\
  shape_retiring(Advance adm)old=retire_retiring 1 old.
Proof. destruct old as[|o rest];[contradiction|intros _].
 unfold retire_post,retire_retiring;cbn[shape_post shape_retiring repeat app tl hd skipn firstn].
 split;[reflexivity|rewrite present_cons;cbn[present concat map];rewrite app_nil_r;reflexivity]. Qed.
End MultiRetire.
End CPUPipelineMultiRetire.
Print Assumptions CPUPipelineMultiRetire.retire_queue.
Print Assumptions CPUPipelineMultiRetire.retire_length.
Print Assumptions CPUPipelineMultiRetire.retire_retiring_length.
Print Assumptions CPUPipelineMultiRetire.retire_stages.
Print Assumptions CPUPipelineMultiRetire.advance_is_retire_one.
