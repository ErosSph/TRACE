(** Initialization of the concrete candidate, separate from preservation. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CV32E40PAddiJointCandidate
 Ex.External.CV32E40PAddiInitialRelated Ex.External.CV32E40PAddiCycleInduction
 Ex.External.CV32E40PAddiReachability Ex.External.CV32E40PAddiNopISAInvariant.
Require Import Ex.RvCore.Machine.
Import ListNotations CV32E40PAddiJointCandidate CV32E40PAddiInitialRelated
 CV32E40PAddiCycleInduction CV32E40PAddiReachability CV32E40PAddiNopISAInvariant.
Local Open Scope Z_scope.
Module CV32E40PAddiJointInitial.
 Lemma reset_id_empty : id_token reset_retirement = None.
 Proof. vm_compute; reflexivity. Qed.
 Lemma reset_packets_empty image : packets image reset_retirement [] = [].
 Proof. unfold packets. rewrite reset_id_empty. reflexivity. Qed.
 Theorem reset_joint_candidate image : ProgramScope image ->
   JointInv image reset_retirement (initial_isa image) [].
 Proof.
   intros Hp. constructor.
   - exact Hp.
   - constructor.
   - apply reset_architectural_relation.
   - apply reset_isa_well_formed.
   - vm_compute; reflexivity.
   - vm_compute; auto.
   - vm_compute; congruence.
   - vm_compute; intros [H | H]; discriminate.
   - vm_compute; congruence.
   - vm_compute; reflexivity.
   - cbn; lia.
   - vm_compute; reflexivity.
   - rewrite reset_packets_empty. constructor.
   - rewrite reset_packets_empty. exact I.
   - vm_compute; reflexivity.
   - cbn [initial_isa getPc]. rewrite reset_id_empty. vm_compute; reflexivity.
   - cbn [initial_isa getPc]. rewrite reset_packets_empty. vm_compute; discriminate.
   - vm_compute; reflexivity.
   - intros t H. discriminate.
 Qed.
 Print Assumptions reset_joint_candidate.
End CV32E40PAddiJointInitial.
