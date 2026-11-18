(** Generic N-stage pipeline queue (design-independent).

    A design describes its post-fetch stages as a list of optional tokens,
    oldest first (Bzeeno: WB, MEM, EX; DarkRISCV: none). The pending queue is
    the list of present tokens. One clock cycle moves the stages in one of
    three shapes:
    - advance: every stage takes its younger neighbour's token, the youngest
      takes the admitted token (if any), the oldest token retires;
    - bubble j: stages older than j advance, stage j becomes empty, younger
      stages hold, nothing is admitted (e.g. a load-use stall);
    - freeze: nothing moves, nothing is admitted or retired.
    For every shape the queue equation required by Codex's
    [CPUGeneratedJointTemplate.StreamingTransfer] holds:
      pending old ++ admitted = retiring ++ pending post.
    No RTL, ISA or CPU state appears here. *)
From Coq Require Import List Lia.
Import ListNotations.

Module CPUPipelineQueue.
Section Queue.
Context {Token:Type}.

Definition opt(o:option Token):list Token:=match o with Some t=>[t]|None=>[] end.
Definition present(stages:list(option Token)):list Token:=concat(map opt stages).

Lemma present_app a b:present(a++b)=present a++present b.
Proof. unfold present;rewrite map_app,concat_app;reflexivity. Qed.
Lemma present_cons o rest:present(o::rest)=opt o++present rest.
Proof. reflexivity. Qed.
Lemma present_none rest:present(None::rest)=present rest.
Proof. reflexivity. Qed.

(** The retiring list is the oldest present token, if it leaves. *)
Inductive Step:list(option Token) ->option Token ->list(option Token) ->list Token ->Prop:=
| step_advance:forall old admitted,
   Step old admitted(tl(old++[admitted]))(opt(hd None(old++[admitted])))
| step_bubble:forall old j,(j<length old)%nat ->
   Step old None(firstn j(tl old)++None::skipn(S j)old)(opt(hd None old))
| step_freeze:forall old,Step old None old [].

Lemma firstn_skipn_tail(old:list(option Token))j:(j<length old)%nat ->
 present(firstn j(tl old)++None::skipn(S j)old)=present(tl old).
Proof. revert j;destruct old as[|o rest];intros j HJ;[cbn in HJ;lia|].
 cbn[tl length]in *.
 rewrite present_app,present_none.
 replace(skipn(S j)(o::rest))with(skipn j rest)by reflexivity.
 rewrite <-present_app,firstn_skipn;reflexivity. Qed.

Theorem step_queue (old:list(option Token))(admitted:option Token)(post:list(option Token))(retiring:list Token):
 Step old admitted post retiring ->
 present old++opt admitted=retiring++present post.
Proof. intro H;destruct H as[old admitted|old j HJ|old].
 - destruct old as[|o rest].
   + destruct admitted;reflexivity.
   + change(tl((o::rest)++[admitted]))with(rest++[admitted]).
     change(hd None((o::rest)++[admitted]))with o.
     rewrite present_cons,present_app,<-app_assoc.
     change(present[admitted])with(opt admitted++[]);rewrite app_nil_r;reflexivity.
 - rewrite(firstn_skipn_tail old j HJ).
   destruct old as[|o rest];[cbn in HJ;lia|];cbn[tl hd opt];rewrite app_nil_r,present_cons;reflexivity.
 - rewrite app_nil_r;reflexivity. Qed.

(** The stage list keeps its length (the design's N) in every shape. *)
Theorem step_length (old:list(option Token))(admitted:option Token)(post:list(option Token))(retiring:list Token):
 Step old admitted post retiring ->length post=length old.
Proof. intro H;destruct H as[old admitted|old j HJ|old].
 - destruct old as[|o rest];[reflexivity|].
   change(tl((o::rest)++[admitted]))with(rest++[admitted]).
   rewrite app_length;cbn[length];lia.
 - destruct old as[|o rest];[cbn in HJ;lia|];cbn[tl length]in *.
   rewrite app_length;cbn[length];rewrite firstn_length_le by lia.
   replace(skipn(S j)(o::rest))with(skipn j rest)by reflexivity.
   rewrite skipn_length;lia.
 - reflexivity. Qed.

(** At most one token retires per cycle (the commit observer reports one). *)
Theorem step_retiring_single (old:list(option Token))(admitted:option Token)(post:list(option Token))(retiring:list Token):
 Step old admitted post retiring ->(length retiring<=1)%nat.
Proof. intro H;destruct H as[old admitted|old j HJ|old];cbn;
 [destruct(hd None(old++[admitted]))|destruct(hd None old)|];cbn;lia. Qed.

(** N = 0 (no post-fetch stage): the admitted token retires in the same cycle. *)
Theorem zero_stage_advance(admitted:option Token):
 Step [] admitted [] (opt admitted).
Proof. exact(step_advance [] admitted). Qed.
End Queue.
End CPUPipelineQueue.
Print Assumptions CPUPipelineQueue.step_queue.
Print Assumptions CPUPipelineQueue.step_length.
Print Assumptions CPUPipelineQueue.step_retiring_single.
Print Assumptions CPUPipelineQueue.zero_stage_advance.
