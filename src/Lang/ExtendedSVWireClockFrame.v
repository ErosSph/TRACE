(** Item-level certificates for an ordered wire cone. No fixed-point
    hypothesis is needed to establish the actual post-phase clock value. *)
From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVAssignment Lang.ExtendedSVConstantRoot
 Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice Lang.ExtendedSVStallFlush Lang.ExtendedSVWordInvariant.
Import ListNotations ExtendedSV ExtendedSVAssignment ExtendedSVConstantRoot
 ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVStallFlush.
Module ExtendedSVWireClockFrame.
Definition Known input roots s:=forall root,In root roots ->
 norm 1(read_signal s root)=norm 1(read_signal s input).
Definition frameb input roots proc:=forallb(fun root=>roots_unwrittenb root[proc])(input::roots).

Lemma frame_known p input roots proc s:
 frameb input roots proc=true ->Known input roots s ->Known input roots(run_process p s proc).
Proof.
 intros HC HK root HI;unfold frameb in HC.
 assert(Hinput:~In input(process_writers proc)).
 { exact(roots_unwrittenb_sound input[proc](proj1(forallb_forall _ _)HC input(or_introl eq_refl))proc(or_introl eq_refl)). }
 assert(Hroot:~In root(process_writers proc)).
 { exact(roots_unwrittenb_sound root[proc](proj1(forallb_forall _ _)HC root(or_intror HI))proc(or_introl eq_refl)). }
 rewrite(run_process_preserves_unwritten_root p proc root s Hroot),
 (run_process_preserves_unwritten_root p proc input s Hinput);now apply HK.
Qed.

Lemma copy_known p input roots proc dst src s:
 process_body proc=SAssign false(EVar 1 src)(LVar 1 dst) ->
 (0<statement_fuel p)%nat ->In src roots ->dst<>input ->
 Known input roots s ->Known input(dst::roots)(run_process p s proc).
Proof.
 intros HB HF HS HD HK.
 rewrite(assignment_run_process p proc s false(EVar 1 src)(LVar 1 dst)HB HF).
 change(Known input(dst::roots)(scalar_write 1 dst(norm 1(read_signal s src))s)).
 intros root HI;unfold Known in HK.
 rewrite(scalar_write_other 1 dst input(norm 1(read_signal s src))s HD).
 destruct HI as[HR|HR].
 - subst root;rewrite scalar_write_same,ExtendedSVWordInvariant.norm_idempotent;exact(HK src HS).
 - destruct(Nat.eq_dec dst root)as[HE|HE].
   + subst root;rewrite scalar_write_same,ExtendedSVWordInvariant.norm_idempotent;exact(HK src HS).
   + rewrite(scalar_write_other 1 dst root(norm 1(read_signal s src))s HE);exact(HK root HR).
Qed.

Inductive WireTrace(p:Program)(input:signal):list signal->list Process->list signal->Prop:=
| TraceNil:forall roots,WireTrace p input roots[]roots
| TraceFrame:forall roots proc rest final,
 frameb input roots proc=true ->WireTrace p input roots rest final ->
 WireTrace p input roots(proc::rest)final
| TraceCopy:forall roots proc rest final dst src,
 process_body proc=SAssign false(EVar 1 src)(LVar 1 dst) ->In src roots ->dst<>input ->
 WireTrace p input(dst::roots)rest final ->WireTrace p input roots(proc::rest)final.

Theorem trace_sound p input before order after:
 WireTrace p input before order after ->(0<statement_fuel p)%nat ->
 forall s,Known input before s ->Known input after(fold_left(run_process p)order s).
Proof.
 intro HC;induction HC;intros HF s HK;cbn[fold_left].
 - exact HK.
 - apply IHHC;[exact HF|exact(frame_known p input roots proc s H HK)].
 - apply IHHC;[exact HF|exact(copy_known p input roots proc dst src s H HF H0 H1 HK)].
Qed.

Lemma all_unwritten_comb p input:
 roots_unwrittenb input(processes p)=true ->comb_root_unwrittenb p input=true.
Proof.
 intro HA;unfold comb_root_unwrittenb;apply forallb_forall;intros proc HI.
 apply filter_In in HI as[HI HC];exact(proj1(forallb_forall _ _)HA proc HI).
Qed.

Lemma selected_updates_keep_input p input s order:
 roots_unwrittenb input(processes p)=true ->
 (forall proc,In proc order ->In proc(processes p)) ->
 read_signal(apply_updates s(flat_map(process_updates p s)order))input=read_signal s input.
Proof.
 intros HA HO;rewrite read_signal_apply_updates;apply apply_root_avoids.
 intros update HU HE;apply in_flat_map in HU as[proc[HP HU]].
 pose proof(process_emitted_writers p s proc update HU)as HW;rewrite HE in HW.
 exact(roots_unwrittenb_sound input(processes p)HA proc(HO proc HP)HW).
Qed.

Section Clock.
Variable p:Program.
Variable input output:signal.
Hypothesis Hinput:roots_unwrittenb input(processes p)=true.
Hypothesis Hround:forall s,norm 1(read_signal(comb_round p s)output)=norm 1(read_signal s input).

Theorem iter_clock fuel:(0<fuel)%nat ->forall s,
 norm 1(read_signal(comb_iter p fuel s)output)=norm 1(read_signal s input).
Proof.
 induction fuel as[|n IH];intros HF s;[lia|].
 destruct n as[|n].
 - exact(Hround s).
 - change(norm 1(read_signal(comb_iter p(S n)(comb_round p s))output)=norm 1(read_signal s input)).
   rewrite(IH ltac:(lia)(comb_round p s)),
    (comb_round_preserves_unwritten_root p input(all_unwritten_comb p input Hinput)s);reflexivity.
Qed.

Theorem candidate_clock:(0<lfp_fuel p)%nat ->forall s,
 norm 1(read_signal(lfp_candidate p s)output)=norm 1(read_signal s input).
Proof. intro HF;unfold lfp_candidate;exact(iter_clock(lfp_fuel p)HF). Qed.

Theorem phase_clock_stable:(0<lfp_fuel p)%nat ->forall ev pre,
 norm 1(read_signal(PhaseSemantics p ev pre)output)=
 norm 1(read_signal(phase_driven_state p ev pre)output).
Proof.
 intros HF ev pre;unfold PhaseSemantics,phase_execute_order,execute_process_order.
 rewrite(candidate_clock HF).
 rewrite(selected_updates_keep_input p input(phase_driven_state p ev pre)
   (selected_on_transition p pre(phase_driven_state p ev pre))Hinput).
 - unfold phase_driven_state;rewrite(candidate_clock HF),
    (lfp_candidate_preserves_unwritten_root p input(all_unwritten_comb p input Hinput));reflexivity.
 - intros proc HI;unfold selected_on_transition in HI;apply filter_In in HI;tauto.
Qed.
End Clock.
Print Assumptions frame_known.
Print Assumptions copy_known.
Print Assumptions trace_sound.
Print Assumptions selected_updates_keep_input.
Print Assumptions phase_clock_stable.
End ExtendedSVWireClockFrame.
