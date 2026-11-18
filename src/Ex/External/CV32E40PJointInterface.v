(** Shared current-state joint relation. This is an interface and initialization
    proof, NOT an inductive preservation or progress theorem. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Ex.RvCore.FormalSpec Ex.RvCore.Machine
 Ex.External.CV32E40PReq39Trace Ex.External.CV32E40PAddiReachability
 Ex.External.CV32E40PAddiJointCandidate Ex.External.CV32E40PAddiJointInitial
 Ex.External.CV32E40PAddiInitialRelated Ex.External.CV32E40PAddiCycleInduction
 Ex.External.CV32E40PAddiNopISAInvariant Ex.External.CV32E40PReq40StateRel
 Ex.External.CV32E40PRequestCycleBalance Ex.External.CV32E40PRequestOccupancyConnection
 Ex.External.CV32E40PFetchFIFOQueue Ex.External.CV32E40PAddiRFPreservation
 Ex.External.CV32E40PDataOpProgramScope.
Require Import coqutil.Word.Interface.
Import ListNotations ExtendedSV CV32E40PReq39Trace CV32E40PAddiReachability
 CV32E40PAddiJointCandidate CV32E40PAddiJointInitial CV32E40PAddiInitialRelated
 CV32E40PAddiCycleInduction CV32E40PAddiNopISAInvariant CV32E40PReq40StateRel
 CV32E40PRequestCycleBalance CV32E40PRequestOccupancyConnection CV32E40PFetchFIFOQueue
 CV32E40PAddiRFPreservation CV32E40PDataOpProgramScope.
Local Open Scope Z_scope.
Module CV32E40PJointInterface.
 Record JointCore image s (isa : FormalSpec.State) (fifo : list IssueToken) : Prop := {
   core_reachable : ResetReachable image s;
   core_architecture : StateRel (projection image s) isa;
   core_isa_shape : ISAInvariant image isa;
   core_accounting : Count s = Pending s;
   core_controller : In (norm 5 (read_signal (trace_rtl (physical_state s)) 1130%nat)) [0;1;4;5];
   core_busy : Count s <> 0 -> norm 1 (read_signal (trace_rtl (physical_state s)) 305%nat) = 1;
   core_gate : ExternalRequest image s = 1 \/ Pending s = 1 -> Gate image s = 1;
   core_no_overwrite : NoTokenOverwrite image s;
   core_fifo_size : Z.of_nat (length fifo) = FifoCount s;
   core_fifo_capacity : (length fifo <= 2)%nat;
   core_fifo_storage : view (read_signal (trace_rtl (physical_state s)) 481%nat)
     (read_signal (trace_rtl (physical_state s)) 475%nat) (FifoCount s) = map token_instruction fifo;
   core_packet_values : Forall (packet_matches image) (packets image s fifo);
   core_packet_order : ordered_from (word.unsigned (getPc isa)) (packets image s fifo);
   core_aligned : norm 3 (read_signal (trace_rtl (physical_state s)) 525%nat) = 0;
   core_aligner_cursor : norm 32 (read_signal (trace_rtl (physical_state s)) 529%nat) =
     (word.unsigned (getPc isa) + 4 * Z.of_nat
       (length (opt_list (pending_token s) ++ opt_list (id_token s)))) mod 2^32;
   core_request_address : ExternalRequest image s = 1 ->
     norm 32 (read_signal (environment_state_image image (physical_state s)) 19%nat) =
       (word.unsigned (getPc isa) + 4 * Z.of_nat (length (packets image s fifo))) mod 2^32;
   core_no_data : read_signal (environment_state_image image (physical_state s)) 21%nat = 0
 }.
 Definition PendingADDI image s isa t := exists rd rs imm,
   legal_reg rd /\ legal_reg rs /\ legal_addi_imm imm /\
   Decode.decode Decode.RV32I (token_instruction t) = Decode.IInstruction (Decode.Addi rd rs imm) /\
   OperandsRelated clk_rise (environment_state_image image (physical_state s)) isa rs imm.
 Definition JointWith
   (scope : InstructionImage -> Prop)
   (pipeline : InstructionImage -> RetirementState -> FormalSpec.State -> IssueToken -> Prop)
   image s isa fifo := scope image /\ JointCore image s isa fifo /\
     (forall t, pending_token s = Some t -> pipeline image s isa t).

 Theorem legacy_addi_exact image s isa fifo :
   JointInv image s isa fifo <-> JointWith ProgramScope PendingADDI image s isa fifo.
 Proof.
   split.
   - intros H. destruct H. split; [assumption|]. split; [constructor; assumption|assumption].
   - intros [HP [HC HD]]. destruct HC. constructor; assumption.
 Qed.

 (** The pipeline argument is intentionally explicit. Instantiating it is not
     a proof that any reachable nonempty pipeline satisfies that argument. *)
 Definition DataOpPipeline
   (pipeline : RetirementState -> FormalSpec.State -> Decode.InstructionI -> Prop)
   (_ : InstructionImage) s isa t := exists i,
     DataOp21 i /\ Decode.decode Decode.RV32I (token_instruction t) = Decode.IInstruction i /\
     pipeline s isa i.
 Definition DataOpJoint pipeline := JointWith DataOpProgram (DataOpPipeline pipeline).

 Theorem reset_joint_core image : JointCore image reset_retirement (initial_isa image) [].
 Proof.
   constructor.
   - constructor.
   - apply reset_architectural_relation.
   - apply reset_isa_well_formed.
   - vm_compute; reflexivity.
   - vm_compute; auto.
   - vm_compute; congruence.
   - vm_compute; intros [H|H]; discriminate.
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
 Qed.
 Theorem reset_dataop_joint pipeline image : DataOpProgram image ->
   DataOpJoint pipeline image reset_retirement (initial_isa image) [].
 Proof.
   intros HP. split; [exact HP|]. split; [apply reset_joint_core|].
   intros t H. discriminate.
 Qed.
 Theorem joint_pending_identity image s isa fifo t :
   JointCore image s isa fifo -> pending_token s = Some t ->
   token_pc t = word.unsigned (getPc isa) /\
   token_instruction t = norm 32 (instruction_from_image image (word.unsigned (getPc isa))).
 Proof.
   intros HC HT.
   pose proof (core_packet_order _ _ _ _ HC) as HO.
   pose proof (core_packet_values _ _ _ _ HC) as HV.
   unfold packets in HO, HV. rewrite HT in HO, HV.
   cbn [opt_list app ordered_from] in HO, HV.
   destruct HO as [HPC _]. split; [exact HPC|].
   inversion HV as [|a q HA HQ]; subst.
   unfold packet_matches in HA. now rewrite HPC in HA.
 Qed.
Print Assumptions legacy_addi_exact.
Print Assumptions reset_dataop_joint.
End CV32E40PJointInterface.
