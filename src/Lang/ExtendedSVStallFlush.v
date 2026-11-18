(** State-threaded stall/redirect tail rules, not a CPU correctness axiom. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVAssignment Lang.ExtendedSVRootProjection
 Lang.ExtendedSVWordInvariant Lang.ExtendedSVAutoAdapterEffects Lang.ExtendedSVCombCut
 Lang.ExtendedSVBankAlignment.
Import ListNotations ExtendedSV ExtendedSVAssignment ExtendedSVRootProjection
 ExtendedSVWordInvariant ExtendedSVAutoAdapterEffects ExtendedSVCombCut ExtendedSVBankAlignment.
Module ExtendedSVStallFlush.

Definition scalar_write width root value s:=apply_update s(resolve_update s(LVar width root)value).
Lemma scalar_write_same width root value s:
 norm width(read_signal(scalar_write width root value s)root)=norm width value.
Proof.
 unfold scalar_write,apply_update,resolve_update;cbn[resolve_lvalue update_signal update_offset update_width update_value].
 rewrite read_signal_write_same,norm_full_low_write,norm_idempotent;reflexivity.
Qed.
Lemma scalar_write_other width root other value s:root<>other ->
 read_signal(scalar_write width root value s)other=read_signal s other.
Proof. intro H;apply read_signal_apply_update_other;exact H. Qed.
Lemma norm_zero width:norm width 0=0%Z.
Proof. unfold norm;apply Z.land_0_l. Qed.
Lemma one_bit_cases s root:norm 1(read_signal s root)=0%Z \/norm 1(read_signal s root)=1%Z.
Proof. pose proof(norm_bounds 1(read_signal s root));change(0<=norm 1(read_signal s root)<2)%Z in H;lia. Qed.

Definition gate_tail width gate selector flag:=FSeq[
 FIf(EUnary 1 UNot(EVar 1 gate))(FAssign false(EConst width 0)(LVar width selector))FEmpty;
 FIf(EBinary 1 BNeq(EConst width 0)(EVar width selector))(FAssign false(EConst 1 1)(LVar 1 flag))FEmpty].
Definition clear_state width gate selector s:=if Z.eqb(norm 1(read_signal s gate))0
 then scalar_write width selector 0 s else s.
Definition flag_state width selector flag s:=if Z.eqb(norm width(read_signal s selector))0
 then s else scalar_write 1 flag 1 s.
Definition tail_state width gate selector flag s:=flag_state width selector flag(clear_state width gate selector s).

Lemma not_bit_test s root:
 Z.eqb(eval_expr s(EUnary 1 UNot(EVar 1 root)))0=negb(Z.eqb(norm 1(read_signal s root))0).
Proof. destruct(one_bit_cases s root)as[H|H];cbn[eval_expr];rewrite H;reflexivity. Qed.
Lemma nonzero_test width s root:
 Z.eqb(eval_expr s(EBinary 1 BNeq(EConst width 0)(EVar width root)))0=
 Z.eqb(norm width(read_signal s root))0.
Proof.
 cbn[eval_expr];rewrite norm_zero,(Z.eqb_sym 0(norm width(read_signal s root))).
 destruct(Z.eqb(norm width(read_signal s root))0);reflexivity.
Qed.

Theorem effect_tail_state width gate selector flag es:
 blocking_state(eval_effect(gate_tail width gate selector flag)es)=
 tail_state width gate selector flag(blocking_state es).
Proof.
 unfold gate_tail,tail_state,clear_state,flag_state.
 cbn[eval_effect fold_left blocking_state pending_nba emitted_updates].
 rewrite not_bit_test;destruct(Z.eqb(norm 1(read_signal(blocking_state es)gate))0);
 cbn[eval_effect blocking_state];rewrite ?norm_zero,nonzero_test;
 destruct(Z.eqb _ 0);reflexivity.
Qed.

Theorem tail_flush_requires_enable width gate selector flag s:
 selector<>gate ->flag<>gate ->selector<>flag ->
 norm 1(read_signal s flag)=0%Z ->
 norm 1(read_signal(tail_state width gate selector flag s)flag)<>0%Z ->
 norm 1(read_signal(tail_state width gate selector flag s)gate)<>0%Z.
Proof.
 intros Hsg Hfg Hsf HF;unfold tail_state,clear_state.
 destruct(Z.eqb(norm 1(read_signal s gate))0)eqn:HG.
 - unfold flag_state;rewrite scalar_write_same,norm_zero,Z.eqb_refl.
   rewrite scalar_write_other by exact Hsf;intro H;contradiction.
 - apply Z.eqb_neq in HG;unfold flag_state.
   destruct(Z.eqb(norm width(read_signal s selector))0);intro H;[exact HG|].
   rewrite scalar_write_other by exact Hfg;exact HG.
Qed.

Theorem checked_effect_frame fuel st plan root:
 compile_effect fuel st=Some plan ->existsb(Nat.eqb root)(stmt_writers st)=false ->
 forall es,read_signal(blocking_state(eval_effect plan es))root=read_signal(blocking_state es)root.
Proof.
 intros HC Hnone es;rewrite <-(compile_effect_sound fuel st plan es HC).
 apply(exec_stmt_preserves_unwritten_root fuel st root es).
 intro HI;assert(HE:existsb(Nat.eqb root)(stmt_writers st)=true).
 { apply existsb_exists;exists root;split;[exact HI|apply Nat.eqb_refl]. }
 rewrite Hnone in HE;discriminate.
Qed.

Theorem effect_seq_append xs ys es:
 eval_effect(FSeq(xs++ys))es=eval_effect(FSeq ys)(eval_effect(FSeq xs)es).
Proof. cbn[eval_effect];now rewrite fold_left_app. Qed.

Theorem effect_seq_sandwich before after action es:
 eval_effect(FSeq(before++action::after))es=
 eval_effect(FSeq after)(eval_effect action(eval_effect(FSeq before)es)).
Proof. rewrite effect_seq_append;reflexivity. Qed.

Theorem actual_lfp_relation p index proc left right(R:Z->Z->Prop):
 nth_error(processes p)index=Some proc ->is_comb proc=true ->
 avoids_root left(filter is_comb(skipn(S index)(processes p)))=true ->
 avoids_root right(filter is_comb(skipn(S index)(processes p)))=true ->
 (forall s,R(read_signal(run_process p s proc)left)(read_signal(run_process p s proc)right)) ->
 forall seed fixed,CombLFP p seed fixed ->R(read_signal fixed left)(read_signal fixed right).
Proof.
 intros HI HC HL HR HP seed fixed HF;destruct HF as[n fixed Hiter Hfixed].
 rewrite <-Hfixed;rewrite(comb_cut_root p index proc fixed left HI HC HL),
 (comb_cut_root p index proc fixed right HI HC HR);apply HP.
Qed.

Print Assumptions effect_tail_state.
Print Assumptions tail_flush_requires_enable.
Print Assumptions checked_effect_frame.
Print Assumptions effect_seq_append.
Print Assumptions effect_seq_sandwich.
Print Assumptions actual_lfp_relation.
End ExtendedSVStallFlush.
