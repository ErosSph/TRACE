(** Generated process-entry equations; no fixed-point premise. *)
From Coq Require Import List ZArith Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarBlockBinding
 Ex.Generated.CV32E40PGeneratedRFPorts Ex.Generated.CV32E40PExtendedAST.
Import ExtendedSV ExtendedSVScalarBlockBinding.
Lemma port_0_local_checked : scalar_fold_bindingb CV32E40PGeneratedRFPorts.block_0_order 0%nat = true.
Proof. vm_compute. reflexivity. Qed.
Theorem port_0_process s :
 norm 32 (read_signal (run_process CV32E40PExtendedAST.cv32e40p_program s CV32E40PExtendedAST.process_1398) 888%nat)
 = norm 32 (eval_expr s CV32E40PGeneratedRFPorts.port_0_rhs).
Proof.
 rewrite (CV32E40PGeneratedRFPorts.block_0_decomposes s).
 exact (checked_scalar_fold_binding CV32E40PExtendedAST.cv32e40p_program CV32E40PGeneratedRFPorts.block_0_order 0%nat
 CV32E40PGeneratedRFPorts.block_0_scalar_0 false CV32E40PGeneratedRFPorts.port_0_rhs 32%nat 888%nat
 eq_refl eq_refl port_0_local_checked ltac:(cbn;lia) s).
Qed.
Lemma port_1_local_checked : scalar_fold_bindingb CV32E40PGeneratedRFPorts.block_1_order 0%nat = true.
Proof. vm_compute. reflexivity. Qed.
Theorem port_1_process s :
 norm 32 (read_signal (run_process CV32E40PExtendedAST.cv32e40p_program s CV32E40PExtendedAST.process_1405) 890%nat)
 = norm 32 (eval_expr s CV32E40PGeneratedRFPorts.port_1_rhs).
Proof.
 rewrite (CV32E40PGeneratedRFPorts.block_1_decomposes s).
 exact (checked_scalar_fold_binding CV32E40PExtendedAST.cv32e40p_program CV32E40PGeneratedRFPorts.block_1_order 0%nat
 CV32E40PGeneratedRFPorts.block_1_scalar_0 false CV32E40PGeneratedRFPorts.port_1_rhs 32%nat 890%nat
 eq_refl eq_refl port_1_local_checked ltac:(cbn;lia) s).
Qed.
Lemma port_2_local_checked : scalar_fold_bindingb CV32E40PGeneratedRFPorts.block_2_order 0%nat = true.
Proof. vm_compute. reflexivity. Qed.
Theorem port_2_process s :
 norm 32 (read_signal (run_process CV32E40PExtendedAST.cv32e40p_program s CV32E40PExtendedAST.process_1432) 892%nat)
 = norm 32 (eval_expr s CV32E40PGeneratedRFPorts.port_2_rhs).
Proof.
 rewrite (CV32E40PGeneratedRFPorts.block_2_decomposes s).
 exact (checked_scalar_fold_binding CV32E40PExtendedAST.cv32e40p_program CV32E40PGeneratedRFPorts.block_2_order 0%nat
 CV32E40PGeneratedRFPorts.block_2_scalar_0 false CV32E40PGeneratedRFPorts.port_2_rhs 32%nat 892%nat
 eq_refl eq_refl port_2_local_checked ltac:(cbn;lia) s).
Qed.
Goal True. idtac "RF_PORT_ASSUMPTIONS_0". exact I. Qed.
Print Assumptions port_0_process.
Goal True. idtac "RF_PORT_ASSUMPTIONS_1". exact I. Qed.
Print Assumptions port_1_process.
Goal True. idtac "RF_PORT_ASSUMPTIONS_2". exact I. Qed.
Print Assumptions port_2_process.
