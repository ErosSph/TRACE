(** Infer a typed output map from the actual statement, then check the
    proved output-free producer rule. No guessed expected behavior is used. *)
From Coq Require Import List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVOutputsFree Lang.ExtendedSVOutputsFreeProducer
 Lang.ExtendedSVBlocking Lang.ExtendedSVCombIdempotence.
Import ExtendedSV ExtendedSVOutputsFree ExtendedSVOutputsFreeProducer
 ExtendedSVBlocking ExtendedSVCombIdempotence ListNotations.
Module ExtendedSVInferredProducerCertificate.
Fixpoint inferred_outputs st:OutputSpec:=match st with
 |SSkip=>[]|SAssign _ _(LVar w r)=>[(w,r)]|SAssign _ _ _=>[]
 |SSeq xs=>flat_map inferred_outputs xs
 |SIf _ yes no=>inferred_outputs yes++inferred_outputs no
 |SCase _ arms=>flat_map(fun arm=>inferred_outputs(snd arm))arms end.
Definition inferred_producerb proc:=
 let spec:=inferred_outputs(process_body proc)in
 coherent_specb spec&&output_free_stmtb spec(process_body proc)&&blocking_onlyb(process_body proc).
Theorem inferred_actual_producer_idempotent p proc:
 inferred_producerb proc=true->ProducerIdempotent p proc.
Proof.
 unfold inferred_producerb. intro H.
 apply andb_true_iff in H as[H HB]. apply andb_true_iff in H as[HW HI].
 exact(actual_outputs_free_producer_idempotent(inferred_outputs(process_body proc))p proc HW HI HB).
Qed.
Theorem inferred_actual_producer_list_idempotent p order:
 forallb inferred_producerb order=true->Forall(ProducerIdempotent p)order.
Proof.
 intro H. apply Forall_forall. intros proc Hin.
 apply inferred_actual_producer_idempotent.
 now apply forallb_forall with(x:=proc)in H.
Qed.
Lemma complete_filtered_exception A(P:A->Prop)f xs:
 Forall P(filter f xs)->Forall P(filter(fun x=>negb(f x))xs)->Forall P xs.
Proof.
 induction xs as[|x xs IH];cbn;intros Hyes Hno;[constructor|].
 destruct(f x)eqn:HF;cbn in *.
 - inversion Hyes;subst. constructor;[assumption|now apply IH].
 - inversion Hno;subst. constructor;[assumption|now apply IH].
Qed.
End ExtendedSVInferredProducerCertificate.
Print Assumptions ExtendedSVInferredProducerCertificate.inferred_actual_producer_list_idempotent.
