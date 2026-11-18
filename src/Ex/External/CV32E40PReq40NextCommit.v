(** Req40: executable next-commit relation over the real CV32E40P phase
    scheduler.

    A boundary is a sliding pipeline window.  Its architectural RF/RAM view
    is taken one cycle after the issue observation; advancing the window by
    one real [full_cycle_image] therefore makes the preceding post-view
    definitionally equal to the next pre-view.  This is the composition fact
    that the concrete Req39 fixture did not provide. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV.
Require Import Ex.External.CV32E40PReq39Trace.
Require Import Ex.External.CV32E40PReq40StateRel.
Require Import Ex.External.BzeenoBaselineDataOps.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine.
Require Import coqutil.Map.Interface coqutil.Word.Interface
  coqutil.Word.Bitwidth coqutil.Word.Properties coqutil.Byte.
Require Import riscv.Utility.MkMachineWidth.

Import ListNotations.
Import ExtendedSV CV32E40PReq39Trace CV32E40PReq40StateRel.
Import BzeenoBaselineDataOps.
Local Open Scope Z_scope.

Module CV32E40PReq40NextCommit.

Section WithContext.
  Context {word : Interface.word 32} {BW : Bitwidth 32}.
  Context {Registers : map.map Decode.Register word}
          {Mem : map.map word byte}.
  Context {word_ok : word.ok word} {registers_ok : map.ok Registers}
          {mem_ok : map.ok Mem}.

  (** Conversion must treat a real CPU cycle as a semantic boundary.  Its
      definition remains executable (test files may explicitly make it
      transparent), while proof-term checking below never expands the 1,800
      signal state merely to compare two wrapper types. *)
  #[local] Opaque full_cycle_image.

  Fixpoint index_image_from (index : Z) (image : InstructionImage)
      : list (Z * Z) :=
    match image with
    | [] => []
    | instruction :: rest =>
        (index, instruction) :: index_image_from (index + 1) rest
    end.

  Definition image_program (image : InstructionImage) : list (Z * Z) :=
    index_image_from 0 image.

  Definition image_formal_imem (image : InstructionImage) : Mem :=
    FormalSpec.formal_initial_imem (image_program image).

  Definition word_formal_dmem (data : Z) : Mem :=
    FormalSpec.formal_initial_imem [(0, norm 32 data)].

  Lemma word_formal_dmem_congr : forall left right,
      left = right -> word_formal_dmem left = word_formal_dmem right.
  Proof. intros left right ->. reflexivity. Qed.

  Record CommitWindow : Type := {
    window_image : InstructionImage;
    window_cursor : TraceState
  }.

  Definition advance_window (w : CommitWindow) : CommitWindow :=
    {| window_image := w.(window_image);
       window_cursor := full_cycle_image w.(window_image) w.(window_cursor) |}.

  Definition nthz (xs : list Z) (n : nat) : Z := nth n xs 0.

  Definition window_issue (w : CommitWindow) : list Z :=
    issue_projection w.(window_cursor).(trace_rtl).

  Definition window_rf_state (w : CommitWindow) : TraceState :=
    full_cycle_image w.(window_image) w.(window_cursor).

  (** Name every architectural scalar before building the record.  These
      names are a proof firewall: projection proofs never ask conversion to
      unfold the multi-cycle FullCore term. *)
  Definition window_pre_pc (w : CommitWindow) : Z :=
    read_signal w.(window_cursor).(trace_rtl) architectural_pc_signal.
  Definition window_pre_next_pc (w : CommitWindow) : Z :=
    (window_pre_pc w + 4) mod 2 ^ 32.
  Definition window_pre_rf (w : CommitWindow) (r : Z) : Z :=
    if (0 <=? r) && (r <? 32)
    then rf_register (window_rf_state w).(trace_rtl) (Z.to_nat r) else 0.
  Definition window_pre_imem (w : CommitWindow) : Mem :=
    image_formal_imem w.(window_image).
  Definition window_pre_dmem (w : CommitWindow) : Mem :=
    word_formal_dmem (window_rf_state w).(trace_memory_word).

  Definition window_pre_projection (w : CommitWindow)
      : RTLArchitecturalState :=
    {| rtl_arch_pc := window_pre_pc w;
       rtl_arch_next_pc := window_pre_next_pc w;
       rtl_arch_rf := window_pre_rf w;
       rtl_arch_imem := window_pre_imem w;
       rtl_arch_dmem := window_pre_dmem w |}.

  Definition window_post_projection (w : CommitWindow)
      : RTLArchitecturalState := window_pre_projection (advance_window w).

  Theorem post_is_next_pre : forall w,
      window_post_projection w = window_pre_projection (advance_window w).
  Proof. reflexivity. Qed.

  Definition registers32 : list Z := map Z.of_nat (seq 0 32).

  Definition rf_projection_checkb
      (actual expected : Z -> Z) : bool :=
    forallb (fun r => Z.eqb (actual r) (expected r))
      registers32.

  Definition addi_issue_valid_checkb (w : CommitWindow) : bool :=
    Z.eqb (nthz (window_issue w) 1) 1.

  Definition addi_instruction_checkb (w : CommitWindow)
      (rd rs1 imm : Z) : bool :=
    Z.eqb (nthz (window_issue w) 2) (enc_i (Decode.Addi rd rs1 imm)).

  Definition addi_actual_post_pc (w : CommitWindow) : Z :=
    window_pre_pc (advance_window w).
  Definition addi_expected_post_pc (w : CommitWindow) (rd rs1 imm : Z) : Z :=
    window_pre_next_pc w.
  Definition addi_pc_checkb (w : CommitWindow) (rd rs1 imm : Z) : bool :=
    Z.eqb (addi_actual_post_pc w) (addi_expected_post_pc w rd rs1 imm).

  Definition addi_actual_post_next_pc (w : CommitWindow) : Z :=
    window_pre_next_pc (advance_window w).
  Definition addi_expected_post_next_pc (w : CommitWindow)
      (rd rs1 imm : Z) : Z :=
    (window_pre_next_pc w + 4) mod 2 ^ 32.
  Definition addi_next_pc_checkb (w : CommitWindow) (rd rs1 imm : Z) : bool :=
    Z.eqb (addi_actual_post_next_pc w)
      (addi_expected_post_next_pc w rd rs1 imm).

  Definition addi_actual_post_rf (w : CommitWindow) : Z -> Z :=
    window_pre_rf (advance_window w).
  Definition addi_expected_post_rf (w : CommitWindow)
      (rd rs1 imm r : Z) : Z :=
    if Z.eq_dec rd 0 then window_pre_rf w r
    else if Z.eq_dec r rd
         then (window_pre_rf w rs1 + imm) mod 2 ^ 32
         else window_pre_rf w r.
  Definition addi_rf_checkb (w : CommitWindow) (rd rs1 imm : Z) : bool :=
    rf_projection_checkb (addi_actual_post_rf w)
      (addi_expected_post_rf w rd rs1 imm).

  Definition addi_expected_projection (w : CommitWindow)
      (rd rs1 imm : Z) : RTLArchitecturalState :=
    {| rtl_arch_pc := addi_expected_post_pc w rd rs1 imm;
       rtl_arch_next_pc := addi_expected_post_next_pc w rd rs1 imm;
       rtl_arch_rf := addi_expected_post_rf w rd rs1 imm;
       rtl_arch_imem := window_pre_imem w;
       rtl_arch_dmem := window_pre_dmem w |}.

  Lemma addi_expected_projection_is_rtl_addi_post : forall w rd rs1 imm,
      addi_expected_projection w rd rs1 imm =
        rtl_addi_post (window_pre_projection w) rd rs1 imm.
  Proof. reflexivity. Qed.

  Definition addi_actual_post_memory (w : CommitWindow) : Z :=
    (window_rf_state (advance_window w)).(trace_memory_word).
  Definition addi_pre_memory (w : CommitWindow) : Z :=
    (window_rf_state w).(trace_memory_word).
  Definition addi_memory_checkb (w : CommitWindow) : bool :=
    Z.eqb (addi_actual_post_memory w) (addi_pre_memory w).

  Definition addi_window_checkb (w : CommitWindow) (rd rs1 imm : Z) : bool :=
    andb (addi_issue_valid_checkb w)
    (andb (addi_instruction_checkb w rd rs1 imm)
    (andb (addi_pc_checkb w rd rs1 imm)
    (andb (addi_next_pc_checkb w rd rs1 imm)
    (andb (addi_rf_checkb w rd rs1 imm)
      (addi_memory_checkb w))))).

  (** Call-by-value evaluator for the same proposition.  The original
      compositional checker above is convenient for proofs, but each field
      projection can independently re-evaluate [full_cycle_image].  This
      version binds the two real successor states once and shares them across
      PC, RF and memory checks. *)
  Definition addi_window_checkb_shared
      (w : CommitWindow) (rd rs1 imm : Z) : bool :=
    let image := w.(window_image) in
    let c0 := w.(window_cursor) in
    let c1 := full_cycle_image image c0 in
    let c2 := full_cycle_image image c1 in
    let issue := issue_projection c0.(trace_rtl) in
    let pre_pc := read_signal c0.(trace_rtl) architectural_pc_signal in
    let post_pc := read_signal c1.(trace_rtl) architectural_pc_signal in
    let pre_rf := fun r : Z =>
      if (0 <=? r) && (r <? 32)
      then rf_register c1.(trace_rtl) (Z.to_nat r) else 0 in
    let post_rf := fun r : Z =>
      if (0 <=? r) && (r <? 32)
      then rf_register c2.(trace_rtl) (Z.to_nat r) else 0 in
    let expected_rf := fun r : Z =>
      if Z.eq_dec rd 0 then pre_rf r
      else if Z.eq_dec r rd
           then (pre_rf rs1 + imm) mod 2 ^ 32
           else pre_rf r in
    andb (Z.eqb (nthz issue 1) 1)
    (andb (Z.eqb (nthz issue 2) (enc_i (Decode.Addi rd rs1 imm)))
    (andb (Z.eqb post_pc ((pre_pc + 4) mod 2 ^ 32))
    (andb (Z.eqb
             ((post_pc + 4) mod 2 ^ 32)
             (((pre_pc + 4) mod 2 ^ 32 + 4) mod 2 ^ 32))
    (andb (rf_projection_checkb post_rf expected_rf)
      (Z.eqb c2.(trace_memory_word) c1.(trace_memory_word)))))).

  Lemma addi_window_checkb_shared_equiv : forall w rd rs1 imm,
      addi_window_checkb_shared w rd rs1 imm =
        addi_window_checkb w rd rs1 imm.
  Proof. reflexivity. Qed.

  Lemma addi_window_checkb_components : forall w rd rs1 imm,
      addi_window_checkb w rd rs1 imm =
      andb (addi_issue_valid_checkb w)
      (andb (addi_instruction_checkb w rd rs1 imm)
      (andb (addi_pc_checkb w rd rs1 imm)
      (andb (addi_next_pc_checkb w rd rs1 imm)
      (andb (addi_rf_checkb w rd rs1 imm)
        (addi_memory_checkb w))))).
  Proof. reflexivity. Qed.

  (** A physical execution fact contains no architectural expectation: it
      only says that [post] is the state obtained by running the real
      CV32E40P phase scheduler once.  Keeping this relation separate from
      the effect certificate prevents a Boolean post-state comparison from
      being mislabeled as "RTL execution". *)
  Record CV32NextCommitExecution
      (pre post : CommitWindow) : Prop := {
    next_commit_is_real_scheduler : post = advance_window pre
  }.

  Lemma advance_window_is_real_execution : forall w,
      CV32NextCommitExecution w (advance_window w).
  Proof. intros. constructor. reflexivity. Qed.

  Record ADDICommitLabel
      (w : CommitWindow) (rd rs1 imm : Z) : Prop := {
    addi_label_valid : nthz (window_issue w) 1 = 1;
    addi_label_instruction :
      nthz (window_issue w) 2 = enc_i (Decode.Addi rd rs1 imm)
  }.

  (** The architectural effect is deliberately a separate proposition.
      Later symbolic/LFP cone proofs may construct it without using the
      executable regression checker. *)
  Record ADDIArchitecturalEffect
      (pre post : CommitWindow) (rd rs1 imm : Z) : Prop := {
    addi_effect_pc :
      window_pre_pc post = addi_expected_post_pc pre rd rs1 imm;
    addi_effect_next_pc :
      window_pre_next_pc post = addi_expected_post_next_pc pre rd rs1 imm;
    addi_effect_rf : forall r, legal_reg r ->
      window_pre_rf post r = addi_expected_post_rf pre rd rs1 imm r;
    addi_effect_imem : window_pre_imem post = window_pre_imem pre;
    addi_effect_dmem : window_pre_dmem post = window_pre_dmem pre
  }.

  Record CheckedADDINextCommit
      (w : CommitWindow) (rd rs1 imm : Z) : Type := {
    checked_addi_post : CommitWindow;
    checked_addi_execution :
      CV32NextCommitExecution w checked_addi_post;
    checked_addi_label : ADDICommitLabel w rd rs1 imm;
    checked_addi_effect :
      ADDIArchitecturalEffect w checked_addi_post rd rs1 imm
  }.

  Definition CV32ADDICheckedNextCommit
      (w : CommitWindow) (rd rs1 imm : Z) : Prop :=
    addi_window_checkb w rd rs1 imm = true.

  (** Compatibility name used by the first Req40 adapter.  New clients
      should use [CV32ADDICheckedNextCommit]; this proposition includes an
      effect check and is not the pure execution relation above. *)
  Definition CV32ADDIExecutesToNextCommit := CV32ADDICheckedNextCommit.

  Lemma registers32_complete : forall r,
      legal_reg r -> In r registers32.
  Proof.
    intros r Hr. unfold legal_reg in Hr.
    unfold registers32. apply in_map_iff.
    exists (Z.to_nat r). split.
    - now rewrite Z2Nat.id by lia.
    - apply in_seq. split; [lia|].
      assert ((Z.to_nat r < 32)%nat).
      { apply (proj1 (Z2Nat.inj_lt r 32 ltac:(lia) ltac:(lia))). lia. }
      lia.
  Qed.

  Lemma rf_projection_checkb_sound : forall actual expected,
      rf_projection_checkb actual expected = true ->
      forall r, legal_reg r ->
        actual r = expected r.
  Proof.
    intros actual expected Hcheck r Hr.
    unfold rf_projection_checkb in Hcheck.
    apply forallb_forall with (x := r) in Hcheck.
    - now apply Z.eqb_eq in Hcheck.
    - now apply registers32_complete.
  Qed.

  Definition CV32StateRel (w : CommitWindow) (isa : FormalSpec.State) : Prop :=
    window_pre_pc w = word.unsigned (getPc isa) /\
    window_pre_next_pc w = word.unsigned (getNextPc isa) /\
    (forall r, legal_reg r -> window_pre_rf w r = isa_rf_value isa r) /\
    window_pre_imem w = getInstMem isa /\
    window_pre_dmem w = getDataMem isa.

  Lemma cv32_state_rel_generic : forall w isa,
      CV32StateRel w isa <-> StateRel (window_pre_projection w) isa.
  Proof.
    intros w isa. unfold CV32StateRel, StateRel, window_pre_projection.
    cbn [rtl_arch_pc rtl_arch_next_pc rtl_arch_rf rtl_arch_imem rtl_arch_dmem].
    tauto.
  Qed.

  Record ADDINextCommitAgreement
      (w : CommitWindow) (rd rs1 imm : Z) : Prop := {
    agree_pc : addi_actual_post_pc w = addi_expected_post_pc w rd rs1 imm;
    agree_next_pc : addi_actual_post_next_pc w =
      addi_expected_post_next_pc w rd rs1 imm;
    agree_rf : forall r, legal_reg r ->
      addi_actual_post_rf w r = addi_expected_post_rf w rd rs1 imm r;
    agree_imem : window_pre_imem (advance_window w) = window_pre_imem w;
    agree_dmem : window_pre_dmem (advance_window w) = window_pre_dmem w
  }.

  Lemma addi_window_checkb_sound : forall w rd rs1 imm,
      addi_window_checkb w rd rs1 imm = true ->
      nthz (window_issue w) 1 = 1 /\
      nthz (window_issue w) 2 = enc_i (Decode.Addi rd rs1 imm) /\
      ADDINextCommitAgreement w rd rs1 imm.
  Proof.
    intros w rd rs1 imm H.
    rewrite addi_window_checkb_components in H.
    apply andb_true_iff in H as [Hvalid H].
    apply andb_true_iff in H as [Hinst H].
    apply andb_true_iff in H as [Hpc H].
    apply andb_true_iff in H as [Hnext H].
    apply andb_true_iff in H as [Hrf Hmem].
    unfold addi_issue_valid_checkb in Hvalid. apply Z.eqb_eq in Hvalid.
    unfold addi_instruction_checkb in Hinst. apply Z.eqb_eq in Hinst.
    unfold addi_pc_checkb in Hpc. apply Z.eqb_eq in Hpc.
    unfold addi_next_pc_checkb in Hnext. apply Z.eqb_eq in Hnext.
    unfold addi_memory_checkb in Hmem. apply Z.eqb_eq in Hmem.
    split; [exact Hvalid|]. split; [exact Hinst|].
    constructor.
    - exact Hpc.
    - exact Hnext.
    - unfold addi_rf_checkb in Hrf.
      now apply rf_projection_checkb_sound.
    - unfold window_pre_imem, advance_window. reflexivity.
    - unfold addi_actual_post_memory, addi_pre_memory in Hmem.
      unfold window_pre_dmem.
      now apply word_formal_dmem_congr.
  Qed.

  Theorem checked_addi_next_commit_certificate : forall w rd rs1 imm,
      CV32ADDICheckedNextCommit w rd rs1 imm ->
      CheckedADDINextCommit w rd rs1 imm.
  Proof.
    intros w rd rs1 imm Hcheck.
    destruct (addi_window_checkb_sound w rd rs1 imm Hcheck)
      as (Hvalid & Hinstruction & Hagree).
    refine {| checked_addi_post := advance_window w;
              checked_addi_execution := advance_window_is_real_execution w;
              checked_addi_label := _;
              checked_addi_effect := _ |}.
    - constructor; assumption.
    - destruct Hagree as [Hpc Hnext Hrf Himem Hdmem].
      constructor; assumption.
  Qed.

  (** Core composition theorem.  Unlike the original wrapper, its execution
      hypothesis does not contain the expected post-state.  The effect is a
      separately named proof obligation which can be discharged either by
      the executable checker or by a symbolic item/LFP derivation. *)
  Theorem cv32e40p_addi_effect_preserves_StateRel :
      forall w post isa rd rs1 imm,
        legal_reg rd -> legal_reg rs1 -> legal_addi_imm imm ->
        ADDIAtPC isa rd rs1 imm ->
        CV32StateRel w isa ->
        CV32NextCommitExecution w post ->
        ADDIArchitecturalEffect w post rd rs1 imm ->
        exists isa',
          FormalSpec.run1 isa = (Some tt, isa') /\
          CV32StateRel post isa'.
  Proof.
    intros w post isa rd rs1 imm Hrd Hrs Himm Hfetch Hrel Hexec Heffect.
    destruct (state_rel_after_run1_addi
      (window_pre_projection w) isa rd rs1 imm
      Hrd Hrs Himm Hfetch (proj1 (cv32_state_rel_generic w isa) Hrel))
      as (isa' & Hrun & Hexpected).
    exists isa'. split; [exact Hrun|].
    destruct Hexec as [Hpost]. subst post.
    destruct Heffect as [Hpc Hnext Hrf Himem Hdmem].
    rewrite <- addi_expected_projection_is_rtl_addi_post in Hexpected.
    destruct Hexpected as (Rpc & Rnext & Rrf & Rimem & Rdmem).
    unfold CV32StateRel. repeat split.
    - rewrite Hpc. exact Rpc.
    - rewrite Hnext. exact Rnext.
    - intros r Hr. rewrite Hrf by exact Hr. now apply Rrf.
    - rewrite Himem. exact Rimem.
    - rewrite Hdmem. exact Rdmem.
  Qed.

  (** Main Req40 one-step theorem.  [CV32ADDIExecutesToNextCommit] is an
      executable proposition over [full_cycle_image], not a supplied final
      projection equality. *)
  Theorem cv32e40p_addi_next_commit_preserves_StateRel :
      forall w isa rd rs1 imm,
        legal_reg rd -> legal_reg rs1 -> legal_addi_imm imm ->
        ADDIAtPC isa rd rs1 imm ->
        CV32StateRel w isa ->
        CV32ADDIExecutesToNextCommit w rd rs1 imm ->
        exists isa',
          FormalSpec.run1 isa = (Some tt, isa') /\
          CV32StateRel (advance_window w) isa'.
  Proof.
    intros w isa rd rs1 imm Hrd Hrs Himm Hfetch Hrel Hchecked.
    destruct (checked_addi_next_commit_certificate w rd rs1 imm Hchecked)
      as [post Hexec Hlabel Heffect].
    cbn in Hexec, Heffect.
    destruct Hexec as [Hpost]. subst post.
    exact (cv32e40p_addi_effect_preserves_StateRel
      w (advance_window w) isa rd rs1 imm
      Hrd Hrs Himm Hfetch Hrel
      (advance_window_is_real_execution w) Heffect).
  Qed.

  (** Two adjacent instructions use the first window's actual successor as
      the second theorem's pre-window.  There is no reset/fixture constructor
      between the calls. *)
  Theorem two_addi_commits_compose_without_reset :
      forall w isa0 isa1 rd0 rs10 imm0 rd1 rs11 imm1,
        legal_reg rd0 -> legal_reg rs10 -> legal_addi_imm imm0 ->
        legal_reg rd1 -> legal_reg rs11 -> legal_addi_imm imm1 ->
        ADDIAtPC isa0 rd0 rs10 imm0 ->
        ADDIAtPC isa1 rd1 rs11 imm1 ->
        FormalSpec.run1 isa0 = (Some tt, isa1) ->
        CV32StateRel w isa0 ->
        CV32ADDIExecutesToNextCommit w rd0 rs10 imm0 ->
        CV32ADDIExecutesToNextCommit (advance_window w) rd1 rs11 imm1 ->
        exists isa2,
          FormalSpec.run1 isa1 = (Some tt, isa2) /\
          CV32StateRel (advance_window (advance_window w)) isa2.
  Proof.
    intros w isa0 isa1 rd0 rs10 imm0 rd1 rs11 imm1
      Hrd0 Hrs0 Himm0 Hrd1 Hrs1 Himm1 Hfetch0 Hfetch1 Hrun0
      Hrel0 Hexec0 Hexec1.
    destruct (cv32e40p_addi_next_commit_preserves_StateRel
      w isa0 rd0 rs10 imm0 Hrd0 Hrs0 Himm0 Hfetch0 Hrel0 Hexec0)
      as (isa1' & Hrun0' & Hrel1).
    rewrite Hrun0 in Hrun0'. inversion Hrun0'; subst isa1'.
    exact (cv32e40p_addi_next_commit_preserves_StateRel
      (advance_window w) isa1 rd1 rs11 imm1
      Hrd1 Hrs1 Himm1 Hfetch1 Hrel1 Hexec1).
  Qed.

End WithContext.
End CV32E40PReq40NextCommit.
