(** Persistent scalar-control fields to real ALU and EX selection ports. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVCombCut
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiAdderInputs
 Ex.External.CV32E40PAddiIDEXAccept Ex.External.CV32E40PAddiOperandCone
 Ex.External.CV32E40PAddiFullCoreALU Ex.External.CV32E40PAddiWritebackCone.
Import ExtendedSV ExtendedSVCombCut CV32E40PExtendedAST CV32E40PAddiAdderInputs
 CV32E40PAddiIDEXAccept CV32E40PAddiOperandCone CV32E40PAddiFullCoreALU
 CV32E40PAddiWritebackCone.
Local Open Scope Z_scope.
Module CV32E40PScalarControlWiring.
 Lemma wire_width s proc w src dst :
   process_body proc = SAssign false (EVar w src) (LVar w dst) ->
   norm w (read_signal (run_process cv32e40p_program s proc) dst) =
   norm w (read_signal s src).
 Proof. intros H. rewrite (assign_value s proc w dst (EVar w src) H).
   cbn [eval_expr]. apply norm_twice. Qed.
 #[local] Opaque before_process comb_round run_process read_signal.
 Lemma round_opcode s : norm 7 (read_signal (round s) 1303%nat) =
   norm 7 (read_signal s 601%nat).
 Proof.
   unfold round.
   rewrite (comb_cut_root cv32e40p_program 410 process_410 s 1303%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_410 7 1194%nat 1303%nat eq_refl).
   rewrite <- (cut_final_root cv32e40p_program 410 s 1194%nat ltac:(vm_compute; reflexivity)).
   rewrite (comb_cut_root cv32e40p_program 409 process_409 s 1194%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_409 7 136%nat 1194%nat eq_refl).
   rewrite <- (cut_final_root cv32e40p_program 409 s 136%nat ltac:(vm_compute; reflexivity)).
   rewrite (comb_cut_root cv32e40p_program 250 process_250 s 136%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_250 7 601%nat 136%nat eq_refl).
   rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Lemma round_vector s : norm 2 (read_signal (round s) 1307%nat) =
   norm 2 (read_signal s 595%nat).
 Proof.
   unfold round.
   rewrite (comb_cut_root cv32e40p_program 585 process_585 s 1307%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_585 2 1202%nat 1307%nat eq_refl).
   rewrite <- (cut_final_root cv32e40p_program 585 s 1202%nat ltac:(vm_compute; reflexivity)).
   rewrite (comb_cut_root cv32e40p_program 584 process_584 s 1202%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_584 2 143%nat 1202%nat eq_refl).
   rewrite <- (cut_final_root cv32e40p_program 584 s 143%nat ltac:(vm_compute; reflexivity)).
   rewrite (comb_cut_root cv32e40p_program 258 process_258 s 143%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_258 2 595%nat 143%nat eq_refl).
   rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Lemma round_subrot s : norm 1 (read_signal (round s) 1312%nat) =
   norm 1 (read_signal s 603%nat).
 Proof.
   unfold round.
   rewrite (comb_cut_root cv32e40p_program 620 process_620 s 1312%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_620 1 1204%nat 1312%nat eq_refl).
   rewrite <- (cut_final_root cv32e40p_program 620 s 1204%nat ltac:(vm_compute; reflexivity)).
   rewrite (comb_cut_root cv32e40p_program 619 process_619 s 1204%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_619 1 145%nat 1204%nat eq_refl).
   rewrite <- (cut_final_root cv32e40p_program 619 s 145%nat ltac:(vm_compute; reflexivity)).
   rewrite (comb_cut_root cv32e40p_program 260 process_260 s 145%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_260 1 603%nat 145%nat eq_refl).
   rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Lemma round_complex s : norm 1 (read_signal (round s) 1311%nat) =
   norm 1 (read_signal s 602%nat).
 Proof.
   unfold round.
   rewrite (comb_cut_root cv32e40p_program 618 process_618 s 1311%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_618 1 1203%nat 1311%nat eq_refl).
   rewrite <- (cut_final_root cv32e40p_program 618 s 1203%nat ltac:(vm_compute; reflexivity)).
   rewrite (comb_cut_root cv32e40p_program 617 process_617 s 1203%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_617 1 144%nat 1203%nat eq_refl).
   rewrite <- (cut_final_root cv32e40p_program 617 s 144%nat ltac:(vm_compute; reflexivity)).
   rewrite (comb_cut_root cv32e40p_program 259 process_259 s 144%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_259 1 602%nat 144%nat eq_refl).
   rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Lemma round_mask s : norm 5 (read_signal (round s) 1309%nat) =
   norm 5 (read_signal s 593%nat).
 Proof.
   unfold round.
   rewrite (comb_cut_root cv32e40p_program 576 process_576 s 1309%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_576 5 1200%nat 1309%nat eq_refl).
   rewrite <- (cut_final_root cv32e40p_program 576 s 1200%nat ltac:(vm_compute; reflexivity)).
   rewrite (comb_cut_root cv32e40p_program 575 process_575 s 1200%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_575 5 141%nat 1200%nat eq_refl).
   rewrite <- (cut_final_root cv32e40p_program 575 s 141%nat ltac:(vm_compute; reflexivity)).
   rewrite (comb_cut_root cv32e40p_program 256 process_256 s 141%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_256 5 593%nat 141%nat eq_refl).
   rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Lemma round_alu_enable s : norm 1 (read_signal (round s) 1198%nat) =
   norm 1 (read_signal s 600%nat).
 Proof.
   unfold round.
   rewrite (comb_cut_root cv32e40p_program 407 process_407 s 1198%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_407 1 135%nat 1198%nat eq_refl).
   rewrite <- (cut_final_root cv32e40p_program 407 s 135%nat ltac:(vm_compute; reflexivity)).
   rewrite (comb_cut_root cv32e40p_program 249 process_249 s 135%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_249 1 600%nat 135%nat eq_refl).
   rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Lemma round_mult_enable s : norm 1 (read_signal (round s) 1210%nat) =
   norm 1 (read_signal s 609%nat).
 Proof.
   unfold round.
   rewrite (comb_cut_root cv32e40p_program 652 process_652 s 1210%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_652 1 151%nat 1210%nat eq_refl).
   rewrite <- (cut_final_root cv32e40p_program 652 s 151%nat ltac:(vm_compute; reflexivity)).
   rewrite (comb_cut_root cv32e40p_program 267 process_267 s 151%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_267 1 609%nat 151%nat eq_refl).
   rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Lemma round_csr_enable s : norm 1 (read_signal (round s) 1260%nat) =
   norm 1 (read_signal s 637%nat).
 Proof.
   unfold round.
   rewrite (comb_cut_root cv32e40p_program 732 process_732 s 1260%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_732 1 196%nat 1260%nat eq_refl).
   rewrite <- (cut_final_root cv32e40p_program 732 s 196%nat ltac:(vm_compute; reflexivity)).
   rewrite (comb_cut_root cv32e40p_program 292 process_292 s 196%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)), (wire_width _ process_292 1 637%nat 196%nat eq_refl).
   rewrite before_process_keeps_root by (vm_compute; reflexivity). reflexivity.
 Qed.
 Definition ScalarAddFields s :=
   norm 7 (read_signal s 601%nat) = 24 /\
   norm 2 (read_signal s 595%nat) = 0 /\
   norm 1 (read_signal s 603%nat) = 0 /\
   norm 1 (read_signal s 602%nat) = 0 /\
   norm 5 (read_signal s 593%nat) = 0.
 Theorem scalar_add_from_fields s : ScalarAddFields s -> ScalarADD s.
 Proof. unfold ScalarAddFields, ScalarADD.
   rewrite round_opcode, round_vector, round_subrot, round_complex, round_mask.
   trivial. Qed.
 Theorem ex_selection_from_fields s :
   norm 1 (read_signal s 600%nat) = 1 ->
   norm 1 (read_signal s 609%nat) = 0 ->
   norm 1 (read_signal s 637%nat) = 0 -> ALUSelected s.
 Proof.
   intros HA HM HC. unfold ALUSelected, cut.
   rewrite <- (cut_final_root cv32e40p_program 1789 s 1198%nat ltac:(vm_compute; reflexivity)).
   rewrite <- (cut_final_root cv32e40p_program 1789 s 1210%nat ltac:(vm_compute; reflexivity)).
   rewrite <- (cut_final_root cv32e40p_program 1789 s 1260%nat ltac:(vm_compute; reflexivity)).
   rewrite round_alu_enable, round_mult_enable, round_csr_enable. auto.
 Qed.
 Print Assumptions scalar_add_from_fields.
 Print Assumptions ex_selection_from_fields.
End CV32E40PScalarControlWiring.
