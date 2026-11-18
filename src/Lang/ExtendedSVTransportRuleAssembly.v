(** Use every registered sound transport backend, independently of which
    actual-fuel backend supplied the producer-idempotence certificates. *)
From Coq Require Import List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVCombIdempotence
 Lang.ExtendedSVCombRuleRegistry Lang.ExtendedSVForeignUpdateTransport.
Import ListNotations ExtendedSV ExtendedSVCombIdempotence
 ExtendedSVCombRuleRegistry ExtendedSVForeignUpdateTransport.
Module ExtendedSVTransportRuleAssembly.
Fixpoint transport_orderb rules order := match order with
 | []=>true
 | first::rest=>forallb (transport_accepted rules first) rest && transport_orderb rules rest
 end.
Theorem transport_order_sound p rules order :
 (0<statement_fuel p)%nat -> transport_orderb rules order=true -> OrderedPreservation p order.
Proof.
 intro HF. induction order as [|first rest IH]; cbn; intro HC; [exact I|].
 apply andb_true_iff in HC as [HH HT]. split; [|exact (IH HT)].
 apply Forall_forall. intros later HI.
 apply forallb_forall with (x:=later) in HH; [|exact HI].
 exact (accepted_transport_sound rules p first later HF HH).
Qed.
Theorem ordered_from_checked_transports p rules order :
 Forall (ProducerIdempotent p) order -> (0<statement_fuel p)%nat ->
 transport_orderb rules order=true -> OrderedProducerCertificate p order.
Proof.
 intros HP HF HT. exact (idempotent_producers_with_preservation_complete p order HP
   (transport_order_sound p rules order HF HT)).
Qed.
End ExtendedSVTransportRuleAssembly.
Print Assumptions ExtendedSVTransportRuleAssembly.transport_order_sound.
Print Assumptions ExtendedSVTransportRuleAssembly.ordered_from_checked_transports.
