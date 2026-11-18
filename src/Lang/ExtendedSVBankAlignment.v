(** Structural, CPU-independent recognition of 32-bit lane offsets.
    All literal tests concern normalized literals, not their source spelling. *)
From Coq Require Import ZArith Lia Bool.
Require Import Lang.ExtendedSV.
Import ExtendedSV.
Local Open Scope Z_scope.
Module ExtendedSVBankAlignment.

Definition literal (e : Expr) : option Z :=
 match e with EConst w v => Some(norm w v) | _ => None end.
Definition literal_eqb (e : Expr) (v : Z) : bool :=
 match literal e with Some z => Z.eqb z v | None => false end.
Definition literal_ge5b (e : Expr) : bool :=
 match literal e with Some z => Z.leb 5 z | None => false end.

Fixpoint aligned32b (e : Expr) : bool :=
 match e with
 | EConst w v => Z.eqb (norm w v mod 32) 0
 | EBinary w BMul a b =>
     (5 <=? w)%nat && (literal_eqb a 32 || literal_eqb b 32)
 | EBinary w BShiftL _ count => (5 <=? w)%nat && literal_ge5b count
 | ESel w body offset =>
     (5 <=? w)%nat && (literal_eqb offset 0 && aligned32b body)
 | EExtend w false body => (5 <=? w)%nat && aligned32b body
 | _ => false
 end.
Definition small_mul32b (e : Expr) : bool :=
 match e with
 | EBinary _ BMul a b =>
   (literal_eqb a 32 && (expr_width b <=? 5)%nat) ||
   (literal_eqb b 32 && (expr_width a <=? 5)%nat)
 | _ => false
 end.
Definition bounded32b (e : Expr) : bool :=
 aligned32b e && ((expr_width e <=? 10)%nat || small_mul32b e).

Lemma norm_mod w v : norm w v = v mod 2^Z.of_nat w.
Proof.
 unfold norm,mask. replace (2^Z.of_nat w-1) with (Z.ones(Z.of_nat w))
 by (rewrite Z.ones_equiv; reflexivity).
 apply Z.land_ones; lia.
Qed.
Lemma norm_bounds w v : 0 <= norm w v < 2^Z.of_nat w.
Proof. rewrite norm_mod; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia. Qed.
Lemma power32_factor n : 5<=n -> 2^n=32*2^(n-5).
Proof.
 intro H. replace n with (5+(n-5)) at 1 by lia.
 rewrite Z.pow_add_r by lia; reflexivity.
Qed.
Lemma norm_aligned32 w v : (5<=w)%nat -> v mod 32=0 -> norm w v mod 32=0.
Proof.
 intros HW HV. rewrite norm_mod.
 apply Z.mod_divide in HV; [|lia]. destruct HV as [k HK].
 apply Z.mod_divide; [lia|].
 pose proof(Z.div_mod v (2^Z.of_nat w) ltac:(apply Z.pow_nonzero;lia)) as HD.
 rewrite (power32_factor (Z.of_nat w) ltac:(lia)) in HD at 1.
 exists (k - 2^(Z.of_nat w-5)*(v/(2^Z.of_nat w))). nia.
Qed.
Lemma eval_bounds s e : 0<=eval_expr s e <2^Z.of_nat(expr_width e).
Proof. destruct e; cbn[eval_expr expr_width]; apply norm_bounds. Qed.
Lemma literal_eqb_sound e z : literal_eqb e z=true -> forall s,eval_expr s e=z.
Proof.
 destruct e; cbn[literal_eqb literal]; try discriminate.
 intro H; apply Z.eqb_eq in H; intro s; exact H.
Qed.
Lemma literal_ge5b_sound e : literal_ge5b e=true -> forall s,5<=eval_expr s e.
Proof.
 destruct e; cbn[literal_ge5b literal]; try discriminate.
 intro H; apply Z.leb_le in H; intro s; exact H.
Qed.
Lemma mul32_aligned a : (a*32) mod 32=0.
Proof. apply Z.mod_divide; [lia|exists a; ring]. Qed.
Lemma shift32_aligned a n : 5<=n -> Z.shiftl a n mod 32=0.
Proof.
 intro H; rewrite Z.shiftl_mul_pow2 by lia.
 rewrite power32_factor by exact H.
 apply Z.mod_divide; [lia|exists(a*2^(n-5)); ring].
Qed.

Theorem aligned32b_sound e : aligned32b e=true -> forall s,
 0<=eval_expr s e /\ eval_expr s e mod 32=0.
Proof.
 intro HC; intro s; split; [apply(eval_bounds s e)|].
 revert HC; induction e; cbn[aligned32b]; try discriminate.
 - intro H; apply Z.eqb_eq in H; exact H.
 - intro H; apply andb_true_iff in H as [HW H].
   apply Nat.leb_le in HW; apply andb_true_iff in H as [HZ HB].
   cbn[eval_expr]; rewrite(literal_eqb_sound _ _ HZ s),Z.shiftr_0_r.
   apply norm_aligned32; [exact HW|now apply IHe1].
 - destruct signed; [discriminate|].
   intro H; apply andb_true_iff in H as [HW HB]; apply Nat.leb_le in HW.
   cbn[eval_expr]; apply norm_aligned32; [exact HW|now apply IHe].
 - destruct op; try discriminate.
   + intro H; apply andb_true_iff in H as [HW HD]; apply Nat.leb_le in HW.
     cbn[eval_expr]; apply norm_aligned32; [exact HW|].
     apply orb_true_iff in HD as [HL|HR].
     * rewrite(literal_eqb_sound _ _ HL s),Z.mul_comm; apply mul32_aligned.
     * rewrite(literal_eqb_sound _ _ HR s); apply mul32_aligned.
   + intro H; apply andb_true_iff in H as [HW HD]; apply Nat.leb_le in HW.
     cbn[eval_expr]; apply norm_aligned32; [exact HW|].
     apply shift32_aligned; exact(literal_ge5b_sound _ HD s).
Qed.

Lemma small_operand_bound e s : (expr_width e<=5)%nat ->
 0<=eval_expr s e<32.
Proof.
 intro HW;pose proof(eval_bounds s e)as[HL HU];split;[exact HL|].
 assert(HP:2^Z.of_nat(expr_width e)<=32).
 { change(2^Z.of_nat(expr_width e)<=2^5).
   apply Z.pow_le_mono_r;lia. }
 lia.
Qed.
Lemma norm_le_nonnegative w v : 0<=v -> norm w v<=v.
Proof.
 intro HV;rewrite norm_mod;apply Z.mod_le;[exact HV|].
 apply Z.pow_pos_nonneg;lia.
Qed.
Lemma small_mul32b_bound e : small_mul32b e=true ->forall s,
 eval_expr s e<1024.
Proof.
 destruct e;cbn[small_mul32b];try discriminate.
 destruct op;try discriminate.
 intro H;apply orb_true_iff in H as[H|H];
 apply andb_true_iff in H as[HC HW];apply Nat.leb_le in HW;intro s;
 cbn[eval_expr].
 - rewrite(literal_eqb_sound _ _ HC s).
   pose proof(small_operand_bound e2 s HW)as[HL HU].
   pose proof(norm_le_nonnegative width (32*eval_expr s e2) ltac:(lia));lia.
 - rewrite(literal_eqb_sound _ _ HC s).
   pose proof(small_operand_bound e1 s HW)as[HL HU].
   pose proof(norm_le_nonnegative width (eval_expr s e1*32) ltac:(lia));lia.
Qed.
Theorem bounded32b_sound e : bounded32b e=true -> forall s,
 0<=eval_expr s e /32<32 /\ eval_expr s e mod 32=0.
Proof.
 unfold bounded32b; rewrite andb_true_iff; intros[HA HW] s.
 destruct(aligned32b_sound e HA s)as[Hpos Hmod].
 assert(Hupper:eval_expr s e<1024).
 { apply orb_true_iff in HW as[HW|HW].
   - apply Nat.leb_le in HW;pose proof(eval_bounds s e)as[_ HU].
     assert(HP:2^Z.of_nat(expr_width e)<=1024).
     { change(2^Z.of_nat(expr_width e)<=2^10).
       apply Z.pow_le_mono_r;lia. } lia.
   - exact(small_mul32b_bound e HW s). }
 split; [split|exact Hmod].
 - apply Z.div_pos; lia.
 - apply Z.div_lt_upper_bound; lia.
Qed.
(** Constructor-shape regressions; symbolic signal IDs remain parameters. *)
Example indexed_multiply r : aligned32b
 (EBinary 12 BMul (EVar 5 r) (EConst 12 32))=true.
Proof. reflexivity. Qed.
Example indexed_multiply_left r : aligned32b
 (EBinary 12 BMul (EConst 12 32) (EVar 5 r))=true.
Proof. reflexivity. Qed.
Example bounded_indexed_multiply r : bounded32b
 (EBinary 12 BMul (EVar 5 r) (EConst 12 32))=true.
Proof. reflexivity. Qed.
Example bounded_indexed_multiply_left r : bounded32b
 (EBinary 12 BMul (EConst 12 32) (EVar 5 r))=true.
Proof. reflexivity. Qed.
Example reject_wide_index r : bounded32b
 (EBinary 12 BMul (EVar 6 r) (EConst 12 32))=false.
Proof. reflexivity. Qed.
Example truncated_shift r : bounded32b
 (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (EVar 5 r))
 (EConst 32 5)) (EConst 32 0))=true.
Proof. reflexivity. Qed.
Example constant_lane : bounded32b (EConst 10 992)=true.
Proof. reflexivity. Qed.
Example normalized_literal_lane : bounded32b (EConst 10 1056)=true.
Proof. reflexivity. Qed.
Example reject_narrow_multiplier_literal r : aligned32b
 (EBinary 12 BMul (EVar 5 r) (EConst 5 32))=false.
Proof. reflexivity. Qed.
Example reject_nonzero_slice r : aligned32b
 (ESel 10 (EBinary 12 BMul (EVar 5 r) (EConst 12 32))
 (EConst 5 1))=false.
Proof. reflexivity. Qed.
Example reject_short_shift r : aligned32b
 (EBinary 12 BShiftL (EVar 5 r) (EConst 5 4))=false.
Proof. reflexivity. Qed.
End ExtendedSVBankAlignment.
Print Assumptions ExtendedSVBankAlignment.aligned32b_sound.
Print Assumptions ExtendedSVBankAlignment.bounded32b_sound.
