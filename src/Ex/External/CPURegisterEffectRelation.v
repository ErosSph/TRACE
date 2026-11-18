(** Register transport over actual ordered packed-bank operations. These
    lemmas do not establish which instruction owns a write or its ISA value. *)
From Coq Require Import ZArith List Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
 Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankPlan
 Ex.External.PicoISARF Ex.RvCore.FormalSpec
 coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth
 coqutil.Byte riscv.Spec.Decode riscv.Utility.MkMachineWidth riscv.Utility.Utility.
Import ExtendedSV ExtendedSVRootProjection ExtendedSVRegisterBank ExtendedSVBankPlan.
Local Open Scope Z_scope.
Module CPURegisterEffectRelation.

Definition BankRelated32 count := BankRelated 32 count.
Definition operation_effects32 := operation_effects 32.
Definition project_x0 (view:Z->Z) i := if i=?0 then 0 else view i.
Definition ViewRelated (physical architectural:Z->Z) : Prop :=
 forall i,0<=i<32 -> project_x0 physical i=architectural i.

Lemma operation_effect_at width op f g i : f i=g i ->
 operation_effect width f op i=operation_effect width g op i.
Proof.
 intro H; destruct op as[index value|total value].
 - change ((if Z.eqb i index then norm width value else f i)=
     (if Z.eqb i index then norm width value else g i)).
   destruct(Z.eqb i index);[reflexivity|exact H].
 - reflexivity.
Qed.
Lemma operations_effect_at width ops f g i : f i=g i ->
 operation_effects width f ops i=operation_effects width g ops i.
Proof.
 revert f g; induction ops as[|op rest IH];intros f g H;cbn;[exact H|].
 apply IH;now apply operation_effect_at.
Qed.
Lemma operations_append width ops more f :
 operation_effects width f (ops++more)=
 operation_effects width (operation_effects width f ops) more.
Proof. revert f;induction ops;intros;cbn;[reflexivity|apply IHops]. Qed.
Lemma projected_operations_congruent ops f g :
 (forall i,0<=i<32 -> project_x0 f i=project_x0 g i) ->
 forall i,0<=i<32 ->
 project_x0(operation_effects32 f ops)i=
 project_x0(operation_effects32 g ops)i.
Proof.
 intros H i HI;unfold project_x0;destruct(i=?0)eqn:HZ;[reflexivity|].
 apply operations_effect_at.
 specialize(H i HI);unfold project_x0 in H;now rewrite HZ in H.
Qed.
Lemma bank_operations_transport root oldbank newbank view ops :
 Forall(OperationValid 32 32)ops -> BankRelated32 32 oldbank view ->
 newbank=apply_updates_root_value root oldbank(operation_updates root 32 ops) ->
 BankRelated32 32 newbank(operation_effects32 view ops).
Proof. intros HV HR ->;now apply bank_related_operations. Qed.

(** A raw lane-zero mismatch is allowed here. Only the architectural
    projection forces x0=0, before and after any physical writes. *)
Theorem projected_bank_transport root oldbank newbank before after ops :
 Forall(OperationValid 32 32)ops ->
 ViewRelated (lane_read 32 oldbank) before ->
 newbank=apply_updates_root_value root oldbank(operation_updates root 32 ops) ->
 (forall i,0<=i<32 -> after i=
   project_x0(operation_effects32 before ops)i) ->
 ViewRelated (lane_read 32 newbank) after.
Proof.
 intros HV HR HE HA i HI;rewrite HA by exact HI.
 assert(Hbank:BankRelated32 32 newbank
   (operation_effects32 (lane_read 32 oldbank) ops)).
 { eapply bank_operations_transport;[exact HV| |exact HE].
   intros j HJ;reflexivity. }
 unfold project_x0;destruct(i=?0)eqn:HZ;[reflexivity|].
 rewrite Hbank by exact HI;apply operations_effect_at.
 specialize(HR i HI);unfold project_x0 in HR;now rewrite HZ in HR.
Qed.

Section ActualISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}.
Context {Registers:map.map Decode.Register word}{Mem:map.map word byte}.
Definition ISAView (isa:FormalSpec.State) := PicoISARF.isa_value(getRegs isa).
Definition RegisterRelated (physical:Z->Z)(isa:FormalSpec.State) :=
 ViewRelated physical (ISAView isa).
Definition ISARegisterEffects (before after:FormalSpec.State) ops :=
 forall i,0<=i<32 -> ISAView after i=operation_effects32 (ISAView before) ops i.
Definition ISAProjectedRegisterEffects (before after:FormalSpec.State) ops :=
 forall i,0<=i<32 -> ISAView after i=
 project_x0(operation_effects32 (ISAView before) ops)i.

Lemma isa_view_x0 isa : ISAView isa 0=0.
Proof. reflexivity. Qed.
Lemma isa_effects_project before after ops :
 ISARegisterEffects before after ops -> ISAProjectedRegisterEffects before after ops.
Proof.
 intros H i HI;unfold project_x0;destruct(i=?0)eqn:HZ.
 - apply Z.eqb_eq in HZ;subst i;reflexivity.
 - now apply H.
Qed.
Lemma related_frame view before after :
 RegisterRelated view before ->
 (forall i,0<=i<32 -> ISAView after i=ISAView before i) ->
 RegisterRelated view after.
Proof. intros HR HE i HI;rewrite HE by exact HI;now apply HR. Qed.
Lemma register_related_rf bank isa :
 RegisterRelated (lane_read 32 bank) isa <-> PicoISARF.RFRelated bank(getRegs isa).
Proof. reflexivity. Qed.

Theorem actual_projected_bank_transport root oldbank newbank before after ops :
 Forall(OperationValid 32 32)ops ->
 RegisterRelated (lane_read 32 oldbank) before ->
 newbank=apply_updates_root_value root oldbank(operation_updates root 32 ops) ->
 ISAProjectedRegisterEffects before after ops ->
 RegisterRelated (lane_read 32 newbank) after.
Proof. apply projected_bank_transport. Qed.
Theorem actual_bank_transport root oldbank newbank before after ops :
 Forall(OperationValid 32 32)ops ->
 RegisterRelated (lane_read 32 oldbank) before ->
 newbank=apply_updates_root_value root oldbank(operation_updates root 32 ops) ->
 ISARegisterEffects before after ops ->
 RegisterRelated (lane_read 32 newbank) after.
Proof.
 intros HV HR HE HI;eapply actual_projected_bank_transport;eauto using isa_effects_project.
Qed.
Theorem raw_bank_transport root oldbank newbank before after ops :
 Forall(OperationValid 32 32)ops ->
 BankRelated32 32 oldbank(ISAView before) ->
 newbank=apply_updates_root_value root oldbank(operation_updates root 32 ops) ->
 ISARegisterEffects before after ops -> BankRelated32 32 newbank(ISAView after).
Proof.
 intros HV HR HE HI.
 pose proof(bank_operations_transport root oldbank newbank _ ops HV HR HE)as HP.
 intros i Hindex;rewrite HI by exact Hindex;now apply HP.
Qed.
Lemma isa_effects_nil before after :
 (forall i,0<=i<32 -> ISAView after i=ISAView before i) ->
 ISARegisterEffects before after nil.
Proof. exact(fun H=>H). Qed.
Lemma isa_effects_append before middle after ops more :
 ISARegisterEffects before middle ops -> ISARegisterEffects middle after more ->
 ISARegisterEffects before after(ops++more).
Proof.
 intros H1 H2 i HI;rewrite H2 by exact HI.
 unfold operation_effects32;rewrite operations_append.
 apply operations_effect_at;now apply H1.
Qed.
Lemma isa_projected_effects_append before middle after ops more :
 ISAProjectedRegisterEffects before middle ops ->
 ISAProjectedRegisterEffects middle after more ->
 ISAProjectedRegisterEffects before after(ops++more).
Proof.
 intros H1 H2 i HI;rewrite H2 by exact HI.
 unfold operation_effects32;rewrite operations_append.
 unfold project_x0;destruct(i=?0)eqn:HZ;[reflexivity|].
 apply operations_effect_at.
 specialize(H1 i HI);unfold project_x0 in H1;now rewrite HZ in H1.
Qed.
Theorem actual_state_bank_transport root pre post before after ops :
 Forall(OperationValid 32 32)ops ->
 RegisterRelated (lane_read 32 (read_signal pre root)) before ->
 read_signal post root=read_signal
   (apply_updates pre(operation_updates root 32 ops)) root ->
 ISAProjectedRegisterEffects before after ops ->
 RegisterRelated (lane_read 32 (read_signal post root)) after.
Proof.
 intros HV HR HE HI;eapply actual_projected_bank_transport;
 [exact HV|exact HR| |exact HI].
 rewrite HE;apply read_signal_apply_updates.
Qed.

(** Explicit component evidence: original ISA execution AND agreement of
    its actual register effects. Neither conjunct is supplied by this library. *)
Record Run1RegisterComponent (before after:FormalSpec.State) ops : Prop := {
 component_run1 : FormalSpec.run1 before=(Some tt,after);
 component_register_effects : ISARegisterEffects before after ops
}.
Theorem run1_component_transport root oldbank newbank before after ops :
 Forall(OperationValid 32 32)ops ->
 RegisterRelated (lane_read 32 oldbank) before ->
 newbank=apply_updates_root_value root oldbank(operation_updates root 32 ops) ->
 Run1RegisterComponent before after ops ->
 FormalSpec.run1 before=(Some tt,after) /\
 RegisterRelated (lane_read 32 newbank) after.
Proof.
 intros HV HR HE[HS HI];split;[exact HS|].
 eapply actual_bank_transport;eassumption.
Qed.

(** This interface consumes the generated certificate of the ACTUAL phase.
    ISA value/ownership agreement remains a separate, explicit obligation. *)
Theorem actual_phase_register_transport p root total entries :
 BankRootCertificate p root total entries ->
 forall ev pre before after,
 changed_signal ev<>root ->
 RegisterRelated (lane_read 32 (read_signal pre root)) before ->
 ISAProjectedRegisterEffects before after
   (bank_phase_operations total pre (phase_driven_state p ev pre) entries) ->
 RegisterRelated
   (lane_read 32 (read_signal (PhaseSemantics p ev pre) root)) after.
Proof.
 intros HC ev pre before after HE HR HI.
 pose proof(bank_phase_related p root total entries HC ev pre
   (lane_read 32 (read_signal pre root)) HE
   (fun i _=>eq_refl)) as HB.
 intros i Hindex;rewrite HI by exact Hindex.
 unfold project_x0;destruct(i=?0)eqn:HZ;[reflexivity|].
 rewrite HB by exact Hindex;apply operations_effect_at.
 specialize(HR i Hindex);unfold project_x0 in HR;now rewrite HZ in HR.
Qed.
Theorem actual_phase_run1_register_transport p root total entries :
 BankRootCertificate p root total entries ->
 forall ev pre before after,
 changed_signal ev<>root ->
 RegisterRelated (lane_read 32 (read_signal pre root)) before ->
 Run1RegisterComponent before after
   (bank_phase_operations total pre (phase_driven_state p ev pre) entries) ->
 FormalSpec.run1 before=(Some tt,after) /\
 RegisterRelated
   (lane_read 32 (read_signal (PhaseSemantics p ev pre) root)) after.
Proof.
 intros HC ev pre before after HE HR[HS HI];split;[exact HS|].
 eapply actual_phase_register_transport;
 [exact HC|exact HE|exact HR|now apply isa_effects_project].
Qed.
End ActualISA.
End CPURegisterEffectRelation.
Print Assumptions CPURegisterEffectRelation.actual_projected_bank_transport.
Print Assumptions CPURegisterEffectRelation.run1_component_transport.
Print Assumptions CPURegisterEffectRelation.actual_phase_register_transport.
Print Assumptions CPURegisterEffectRelation.actual_phase_run1_register_transport.
