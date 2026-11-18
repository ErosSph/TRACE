(** Generated actual LFP reader-output equations; no ISA identity assumed. *)
From Coq Require Import List ZArith Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarBlockBinding
 Ex.Generated.CV32E40PExtendedAST.
Import ListNotations ExtendedSV ExtendedSVScalarBlockBinding.
Definition actual_combs := filter is_comb (processes CV32E40PExtendedAST.cv32e40p_program).
Definition block_0_scalar_0 : Process :=
 {| process_kind := Combinational; process_events := [];
    process_body := (SAssign false (ECond 32 (ESel 1 (EVar 6 887) (EConst 3 5)) (ESel 32 (EConst 1024 0) (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (ESel 5 (EVar 6 887) (EConst 3 0))) (EConst 32 5)) (EConst 32 0))) (ESel 32 (EVar 1024 902) (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (ESel 5 (EVar 6 887) (EConst 3 0))) (EConst 32 5)) (EConst 32 0)))) (LVar 32 888)); process_source_line := 0 |}.
Definition block_0_order : list Process := [block_0_scalar_0].
Lemma block_0_registered : nth_error actual_combs 1245%nat
 = Some CV32E40PExtendedAST.process_1398.
Proof. vm_compute. reflexivity. Qed.
Lemma block_0_decomposes s : run_process CV32E40PExtendedAST.cv32e40p_program s CV32E40PExtendedAST.process_1398 =
 fold_left (run_process CV32E40PExtendedAST.cv32e40p_program) block_0_order s.
Proof. reflexivity. Qed.
Definition block_1_scalar_0 : Process :=
 {| process_kind := Combinational; process_events := [];
    process_body := (SAssign false (ECond 32 (ESel 1 (EVar 6 889) (EConst 3 5)) (ESel 32 (EConst 1024 0) (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (ESel 5 (EVar 6 889) (EConst 3 0))) (EConst 32 5)) (EConst 32 0))) (ESel 32 (EVar 1024 902) (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (ESel 5 (EVar 6 889) (EConst 3 0))) (EConst 32 5)) (EConst 32 0)))) (LVar 32 890)); process_source_line := 0 |}.
Definition block_1_order : list Process := [block_1_scalar_0].
Lemma block_1_registered : nth_error actual_combs 1252%nat
 = Some CV32E40PExtendedAST.process_1405.
Proof. vm_compute. reflexivity. Qed.
Lemma block_1_decomposes s : run_process CV32E40PExtendedAST.cv32e40p_program s CV32E40PExtendedAST.process_1405 =
 fold_left (run_process CV32E40PExtendedAST.cv32e40p_program) block_1_order s.
Proof. reflexivity. Qed.
Definition block_2_scalar_0 : Process :=
 {| process_kind := Combinational; process_events := [];
    process_body := (SAssign false (ECond 32 (ESel 1 (EVar 6 891) (EConst 3 5)) (ESel 32 (EConst 1024 0) (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (ESel 5 (EVar 6 891) (EConst 3 0))) (EConst 32 5)) (EConst 32 0))) (ESel 32 (EVar 1024 902) (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (ESel 5 (EVar 6 891) (EConst 3 0))) (EConst 32 5)) (EConst 32 0)))) (LVar 32 892)); process_source_line := 0 |}.
Definition block_2_order : list Process := [block_2_scalar_0].
Lemma block_2_registered : nth_error actual_combs 1279%nat
 = Some CV32E40PExtendedAST.process_1432.
Proof. vm_compute. reflexivity. Qed.
Lemma block_2_decomposes s : run_process CV32E40PExtendedAST.cv32e40p_program s CV32E40PExtendedAST.process_1432 =
 fold_left (run_process CV32E40PExtendedAST.cv32e40p_program) block_2_order s.
Proof. reflexivity. Qed.
Definition port_0_rhs : Expr := (ECond 32 (ESel 1 (EVar 6 887) (EConst 3 5)) (ESel 32 (EConst 1024 0) (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (ESel 5 (EVar 6 887) (EConst 3 0))) (EConst 32 5)) (EConst 32 0))) (ESel 32 (EVar 1024 902) (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (ESel 5 (EVar 6 887) (EConst 3 0))) (EConst 32 5)) (EConst 32 0)))).
Lemma port_0_checked : scalar_block_bindingb actual_combs 1245%nat
 block_0_order 0%nat = true.
Proof. vm_compute. reflexivity. Qed.
Theorem port_0_lfp seed fixed : CombLFP CV32E40PExtendedAST.cv32e40p_program seed fixed ->
 norm 32 (read_signal fixed 888%nat) = norm 32 (eval_expr fixed port_0_rhs).
Proof.
 exact (checked_scalar_block_binding CV32E40PExtendedAST.cv32e40p_program actual_combs 1245%nat CV32E40PExtendedAST.process_1398
 block_0_order 0%nat block_0_scalar_0 false port_0_rhs 32%nat 888%nat seed fixed
 eq_refl block_0_registered eq_refl eq_refl block_0_decomposes
 port_0_checked ltac:(cbn;lia)).
Qed.
Definition port_1_rhs : Expr := (ECond 32 (ESel 1 (EVar 6 889) (EConst 3 5)) (ESel 32 (EConst 1024 0) (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (ESel 5 (EVar 6 889) (EConst 3 0))) (EConst 32 5)) (EConst 32 0))) (ESel 32 (EVar 1024 902) (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (ESel 5 (EVar 6 889) (EConst 3 0))) (EConst 32 5)) (EConst 32 0)))).
Lemma port_1_checked : scalar_block_bindingb actual_combs 1252%nat
 block_1_order 0%nat = true.
Proof. vm_compute. reflexivity. Qed.
Theorem port_1_lfp seed fixed : CombLFP CV32E40PExtendedAST.cv32e40p_program seed fixed ->
 norm 32 (read_signal fixed 890%nat) = norm 32 (eval_expr fixed port_1_rhs).
Proof.
 exact (checked_scalar_block_binding CV32E40PExtendedAST.cv32e40p_program actual_combs 1252%nat CV32E40PExtendedAST.process_1405
 block_1_order 0%nat block_1_scalar_0 false port_1_rhs 32%nat 890%nat seed fixed
 eq_refl block_1_registered eq_refl eq_refl block_1_decomposes
 port_1_checked ltac:(cbn;lia)).
Qed.
Definition port_2_rhs : Expr := (ECond 32 (ESel 1 (EVar 6 891) (EConst 3 5)) (ESel 32 (EConst 1024 0) (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (ESel 5 (EVar 6 891) (EConst 3 0))) (EConst 32 5)) (EConst 32 0))) (ESel 32 (EVar 1024 902) (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (ESel 5 (EVar 6 891) (EConst 3 0))) (EConst 32 5)) (EConst 32 0)))).
Lemma port_2_checked : scalar_block_bindingb actual_combs 1279%nat
 block_2_order 0%nat = true.
Proof. vm_compute. reflexivity. Qed.
Theorem port_2_lfp seed fixed : CombLFP CV32E40PExtendedAST.cv32e40p_program seed fixed ->
 norm 32 (read_signal fixed 892%nat) = norm 32 (eval_expr fixed port_2_rhs).
Proof.
 exact (checked_scalar_block_binding CV32E40PExtendedAST.cv32e40p_program actual_combs 1279%nat CV32E40PExtendedAST.process_1432
 block_2_order 0%nat block_2_scalar_0 false port_2_rhs 32%nat 892%nat seed fixed
 eq_refl block_2_registered eq_refl eq_refl block_2_decomposes
 port_2_checked ltac:(cbn;lia)).
Qed.
Goal True. idtac "RF_PORT_ASSUMPTIONS_0". exact I. Qed.
Print Assumptions port_0_lfp.
Goal True. idtac "RF_PORT_ASSUMPTIONS_1". exact I. Qed.
Print Assumptions port_1_lfp.
Goal True. idtac "RF_PORT_ASSUMPTIONS_2". exact I. Qed.
Print Assumptions port_2_lfp.
