(** Concrete, current-state candidate. No preservation/progress claim is made.
    FIFO token addresses are ghost metadata, never a replacement RTL FIFO. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Ex.External.CV32E40PReq39Trace
 Ex.External.CV32E40PAddiReachability Ex.External.CV32E40PAddiNopROM
 Ex.External.CV32E40PAddiNopISAInvariant Ex.External.CV32E40PReq40StateRel
 Ex.External.CV32E40PReq40ConcreteRefinement Ex.External.CV32E40PReq40NextCommit Ex.External.CV32E40PFetchFIFOQueue
 Ex.External.CV32E40PRequestCycleBalance Ex.External.CV32E40PRequestOccupancyConnection
 Ex.External.CV32E40PAddiRFPreservation Ex.External.CV32E40PAddiCycleInduction.
Require Import Ex.RvCore.FormalSpec coqutil.Word.Interface.
Import ListNotations ExtendedSV CV32E40PReq39Trace CV32E40PAddiReachability
 CV32E40PAddiNopROM CV32E40PAddiNopISAInvariant CV32E40PReq40StateRel
 CV32E40PReq40ConcreteRefinement CV32E40PReq40NextCommit CV32E40PFetchFIFOQueue CV32E40PRequestCycleBalance
 CV32E40PRequestOccupancyConnection CV32E40PAddiRFPreservation CV32E40PAddiCycleInduction.
Local Open Scope Z_scope.
Module CV32E40PAddiJointCandidate.
 Definition packet image pc := {| token_pc := pc;
   token_instruction := norm 32 (instruction_from_image image pc) |}.
 Definition opt_list {A : Type} (o : option A) := match o with Some x => [x] | None => [] end.
 Definition id_token s := let rtl := trace_rtl (physical_state s) in
   if norm 1 (read_signal rtl 336%nat) =? 0 then None else
     Some {| token_pc := norm 32 (read_signal rtl 341%nat);
             token_instruction := norm 32 (read_signal rtl 337%nat) |}.
 Definition response_token image s := option_map (packet image)
   (trace_instruction_pending (physical_state s)).
 Definition packets image s fifo := opt_list (pending_token s) ++ opt_list (id_token s) ++
   fifo ++ opt_list (response_token image s).
 Fixpoint ordered_from pc (q : list IssueToken) : Prop := match q with
   | [] => True
   | t :: rest => token_pc t = pc /\ ordered_from ((pc + 4) mod 2^32) rest
   end.
 Definition packet_matches image t := token_instruction t =
   norm 32 (instruction_from_image image (token_pc t)).
 Definition projection image s : RTLArchitecturalState :=
   {| rtl_arch_pc := architectural_cursor s;
      rtl_arch_next_pc := (architectural_cursor s + 4) mod 2^32;
      rtl_arch_rf := fun r => if (0 <=? r) && (r <? 32)
        then rf_register (trace_rtl (physical_state s)) (Z.to_nat r) else 0;
      rtl_arch_imem := nop_rom image;
      rtl_arch_dmem := word_formal_dmem (trace_memory_word (physical_state s)) |}.
 Record JointInv image s (isa : FormalSpec.State) (fifo : list IssueToken) : Prop := {
   program_scope : ProgramScope image;
   real_reachable : ResetReachable image s;
   architecture : StateRel (projection image s) isa;
   isa_shape : ISAInvariant image isa;
   request_accounting : Count s = Pending s;
   controller_phase : In (norm 5 (read_signal (trace_rtl (physical_state s)) 1130%nat)) [0; 1; 4; 5];
   outstanding_busy : Count s <> 0 -> norm 1 (read_signal (trace_rtl (physical_state s)) 305%nat) = 1;
   transaction_gate : ExternalRequest image s = 1 \/ Pending s = 1 -> Gate image s = 1;
   token_no_overwrite : NoTokenOverwrite image s;
   fifo_size : Z.of_nat (length fifo) = FifoCount s;
   fifo_capacity : (length fifo <= 2)%nat;
   fifo_storage : view (read_signal (trace_rtl (physical_state s)) 481%nat)
     (read_signal (trace_rtl (physical_state s)) 475%nat) (FifoCount s) = map token_instruction fifo;
   packet_values : Forall (packet_matches image) (packets image s fifo);
   packet_order : ordered_from (word.unsigned (getPc isa)) (packets image s fifo);
   aligned32 : norm 3 (read_signal (trace_rtl (physical_state s)) 525%nat) = 0;
   aligner_cursor : norm 32 (read_signal (trace_rtl (physical_state s)) 529%nat) =
     (word.unsigned (getPc isa) + 4 * Z.of_nat
       (length (opt_list (pending_token s) ++ opt_list (id_token s)))) mod 2^32;
   request_address : ExternalRequest image s = 1 ->
     norm 32 (read_signal (environment_state_image image (physical_state s)) 19%nat) =
       (word.unsigned (getPc isa) + 4 * Z.of_nat (length (packets image s fifo))) mod 2^32;
   no_data_transaction : read_signal (environment_state_image image (physical_state s)) 21%nat = 0;
   pending_operands : forall t, pending_token s = Some t -> exists rd rs imm,
     legal_reg rd /\ legal_reg rs /\ legal_addi_imm imm /\
     Decode.decode Decode.RV32I (token_instruction t) = Decode.IInstruction (Decode.Addi rd rs imm) /\
     OperandsRelated clk_rise (environment_state_image image (physical_state s)) isa rs imm
 }.
 (** No future execution occurs in JointInv. Busy history and gate/FSM cases
     still need inductive justification and possibly strengthening; this candidate is intentionally
     NOT exported as a proved inductive invariant. *)
 Definition CandidateRelation image s isa := exists fifo, JointInv image s isa fifo.
 Theorem candidate_implies_architecture image s isa : CandidateRelation image s isa ->
   StateRel (projection image s) isa.
 Proof. intros [fifo H]. exact (architecture image s isa fifo H). Qed.
End CV32E40PAddiJointCandidate.
