#!/usr/bin/env python3
"""Reset layer (item 3) of the Bzeeno template route: the real boot events leave the pipeline empty and every register at its reset value.

F.boot image = phase_run P [reset_assert; rise; fall; reset_release] (F.seed image).   (GeneratedSeedBoot.FrozenEnvironment)
  s0 = F.seed image (all zero except ROM root 330 = image and resetn = 1; NOT a combinational fixed point)
  s1 = reset_assert on s0  : only the inverted-clock net edge fires (process_5, the RF); registers keep their seed value
  s2 = rise with reset = 0 : every clock-rise process takes its reset branch (valid bits 0, IF/ID word = reset NOP, ...)
  s3 = fall with reset = 0 : only the RF process fires (reset branch: bank = 0); all other registers framed
  s4 = reset_release       : no process fires (no Posedge on the reset): everything framed
All steps use the reset layer of the edge/stage generators (cpu_tmpl_edge.py --reset-events, cpu_tmpl_stage.py --reset-*).
The reset value of every register is read from the reset branch of the sequential process in the AST, and Coq checks it against
the decision tree (texpr) of the process.  Untrusted generator; Coq checks everything.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
"""
import json
import sys
from pathlib import Path
import cpu_tmpl_roles as roles
import cpu_tmpl_ast as T
import cpu_tmpl_edge as E


def flat(s):
    if s[0] == 'SSeq':
        return [x for c in s[1] for x in flat(c)]
    return [s]


def reset_table(ast, procs):
    """{process: (reset net, [(register, width, reset constant)])} for the clock-rise processes with a full-width reset branch"""
    out = {}
    for i, _ in procs:
        if i == 5:
            continue   # the RF process (part-select bank) is handled separately
        body = ast.procs[i]['body']
        t = body[1][0][1][0]
        if t[0] != 'SIf' or t[1][0] != 'EVar':
            continue
        net = t[1][2]
        regs = []
        for s in flat(t[3]):
            if s[0] == 'SAssign' and s[2][0] == 'EConst' and s[3][0] == 'LVar':
                regs.append((s[3][2], s[3][1], s[2][2]))
        if regs:
            out[i] = (net, regs)
    return out


HDR = r"""From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVCheckedAssignmentBinding Lang.ExtendedSVWordInvariant Lang.ExtendedSVStallFlush
 Lang.ExtendedSVBankAlignment Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVBankOperand Lang.ExtendedSVSeqTree
 Lang.ExtendedSVScalarHistory Lang.ExtendedSVPackedROM Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVBoundedCatalogPhase
 GeneratedRuntimeInput.ConfiguredAST GeneratedDependencyCatalog.Catalog GeneratedBoundedPhase.Phase
 GeneratedSeedBoot.FrozenEnvironment GeneratedSeedBoot.Bootstrap
 TmplBzEdge.BzTmplEdge TmplBzResetEdge.BzTmplEdgeR TmplBzStage.BzTmplStage TmplBzResetStage.BzTmplResetStage
 TmplBzResetFrame.BzTmplResetFrame TmplBzResetRam.BzTmplResetRam TmplBzRF.BzTmplRF TmplBzEnv.BzTmplEnv.
Import ListNotations ExtendedSV ExtendedSVCheckedAssignmentBinding ExtendedSVWordInvariant ExtendedSVStallFlush ExtendedSVBankAlignment
 ExtendedSVEmptyPipeline ExtendedSVBankOperand ExtendedSVSeqTree ExtendedSVScalarHistory ExtendedSVDependencyCatalog ExtendedSVBoundedCatalogPhase
 BzeenoLoadUseJalASTConfigured3122be4a95.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics phase_driven_state phase_run BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program.
"""


def build(design, module):
    ast, pr, tr = roles.load_all(design)
    clk0, rst0, net, chain, procs = E.nets(ast, pr)
    order = E.net_order(ast, pr)
    table = reset_table(ast, procs)
    rf = pr['rf_write']
    bank = rf['bank']['id']
    ram = pr['ram']
    rbank, we = ram['bank']['id'], ram['write_enable']['id']
    # copy chain of the RAM write enable down to a stage register
    chain_we, s = [], we
    while s in ast.comb and ast.comb[s]['rhs'][0] == 'EVar':
        chain_we.append(s)
        s = ast.comb[s]['rhs'][2]
    wreg = s
    assert any(wreg == R for _, (_, regs) in table.items() for R, _, _ in regs), 'RAM write enable is not a stage register copy'
    fall_net = None
    for sp in tr['sequential_processes']:
        if sp['process'] == pr['rf_write']['process']:
            fall_net = [e['signal']['id'] for e in sp['events'] if e['edge'] == 'Negedge' and not e['inverted']][0]
    rf_proc = int(rf['process'].split('_')[1])
    reset_nets = sorted({n for n, _ in table.values()} | {fall_net})
    L = []
    P = 'bzeeno_load_use_jal_program'
    L += ['Module E := TmplBzEdge.BzTmplEdge.BzTmplEdge.', 'Module ER := TmplBzResetEdge.BzTmplEdgeR.BzTmplEdgeR.',
          'Module S := TmplBzStage.BzTmplStage.BzTmplStage.', 'Module RS := TmplBzResetStage.BzTmplResetStage.BzTmplResetStage.',
          'Module RF := TmplBzResetFrame.BzTmplResetFrame.BzTmplResetFrame.', 'Module RR := TmplBzResetRam.BzTmplResetRam.BzTmplResetRam.',
          'Module RFM := TmplBzRF.BzTmplRF.BzTmplRF.', 'Module EN := TmplBzEnv.BzTmplEnv.BzTmplEnv.',
          'Module F := GeneratedSeedBoot.FrozenEnvironment.', 'Module B := GeneratedSeedBoot.Bootstrap.', 'Module Phi := GeneratedBoundedPhase.Phase.',
          f'Notation P := {P} (only parsing).', 'Notation Cat := GeneratedDependencyCatalog.Catalog.actual_catalog.']
    # ---- generic step lemmas
    L += [
        'Lemma boot_ev : CatalogEvent P Cat F.reset_assert /\\ CatalogEvent P Cat F.rise /\\ CatalogEvent P Cat F.fall /\\ CatalogEvent P Cat F.reset_release.',
        'Proof. pose proof B.boot_events_allowed as H. unfold F.boot_events in H. inversion H as [|a l H1 H2 Ea]; subst.',
        ' inversion H2 as [|a2 l2 H3 H4 Eb]; subst. inversion H4 as [|a3 l3 H5 H6 Ec]; subst. inversion H6 as [|a4 l4 H7 H8 Ed]; subst. auto. Qed.',
        'Lemma step_ok ev pre : CatalogEvent P Cat ev -> CatalogShape P Cat pre ->',
        ' CatalogShape P Cat (PhaseSemantics P ev pre) /\\ CombLFP P (write_signal pre (changed_signal ev) (new_value ev)) (phase_driven_state P ev pre) /\\',
        ' exists seed, CombLFP P seed (PhaseSemantics P ev pre).',
        'Proof. intros Hev HS. pose proof (Phi.original_phase ev pre Hev HS) as HP. cbv zeta in HP. destruct HP as [H1 [H2 _]].',
        ' refine (conj (Phi.original_phase_shape ev pre Hev HS) (conj H1 _)). eexists. exact H2. Qed.',
        f'Lemma in_clk ev pre : read_signal (PhaseSemantics P ev pre) {clk0}%nat = read_signal (write_signal pre (changed_signal ev) (new_value ev)) {clk0}%nat.',
        f'Proof. exact (phase_input P {clk0}%nat ev pre ltac:(vm_compute; reflexivity)). Qed.',
        f'Lemma in_rst ev pre : read_signal (PhaseSemantics P ev pre) {rst0}%nat = read_signal (write_signal pre (changed_signal ev) (new_value ev)) {rst0}%nat.',
        f'Proof. exact (phase_input P {rst0}%nat ev pre ltac:(vm_compute; reflexivity)). Qed.',
        f'Lemma shape_networds s : CatalogShape P Cat s -> Word 1 (read_signal s {clk0}%nat) -> Word 1 (read_signal s {rst0}%nat) -> E.NetWords s.',
        'Proof. intros [Hlen Hw] H0 H1. unfold E.NetWords. repeat split.',
        ' all: first [exact H0 | exact H1 | (eapply Hw; apply EN.net_in; unfold EN.nets; cbn; tauto)]. Qed.',
        'Definition s0 (image : Z) : State := F.seed image.',
        'Definition s1 (image : Z) : State := PhaseSemantics P F.reset_assert (s0 image).',
        'Definition s2 (image : Z) : State := PhaseSemantics P F.rise (s1 image).',
        'Definition s3 (image : Z) : State := PhaseSemantics P F.fall (s2 image).',
        'Definition s4 (image : Z) : State := PhaseSemantics P F.reset_release (s3 image).',
        'Lemma boot_is_s4 image : F.boot image = s4 image.',
        'Proof. unfold F.boot, F.boot_events, s4, s3, s2, s1, s0. cbn [phase_run]. reflexivity. Qed.',
        f'Lemma seed_clk image : read_signal (s0 image) {clk0}%nat = 0. Proof. vm_compute. reflexivity. Qed.',
        f'Lemma seed_rst image : read_signal (s0 image) {rst0}%nat = 1. Proof. vm_compute. reflexivity. Qed.',
        'Lemma seed_zero image : ER.NetsZero (s0 image). Proof. unfold ER.NetsZero. vm_compute. repeat split. Qed.',
        'Lemma seed_shape image : CatalogShape P Cat (s0 image). Proof. exact (B.seed_shape image). Qed.',
    ]
    # ---- the chain of shapes, input values, hypotheses
    L += [
        'Lemma st1 image : CatalogShape P Cat (s1 image) /\\ CombLFP P (write_signal (s0 image) (changed_signal F.reset_assert) (new_value F.reset_assert)) (phase_driven_state P F.reset_assert (s0 image)) /\\ exists seed, CombLFP P seed (s1 image).',
        'Proof. destruct boot_ev as (E1 & _). exact (step_ok _ _ E1 (seed_shape image)). Qed.',
        f'Lemma in1 image : read_signal (s1 image) {clk0}%nat = 0 /\\ read_signal (s1 image) {rst0}%nat = 0.',
        f'Proof. unfold s1. rewrite in_clk, in_rst. unfold F.reset_assert. cbn [changed_signal new_value]. split.',
        f' - rewrite read_signal_write_other by discriminate. apply seed_clk.',
        f' - apply read_signal_write_same. Qed.',
        'Lemma st2 image : CatalogShape P Cat (s2 image) /\\ CombLFP P (write_signal (s1 image) (changed_signal F.rise) (new_value F.rise)) (phase_driven_state P F.rise (s1 image)) /\\ exists seed, CombLFP P seed (s2 image).',
        'Proof. destruct boot_ev as (_ & E2 & _). destruct (in1 image) as [H0 H1]. destruct (st1 image) as (S1 & _). exact (step_ok _ _ E2 S1). Qed.',
        f'Lemma in2 image : read_signal (s2 image) {clk0}%nat = 1 /\\ read_signal (s2 image) {rst0}%nat = 0.',
        f'Proof. unfold s2. rewrite in_clk, in_rst. unfold F.rise. cbn [changed_signal new_value]. split.',
        f' - apply read_signal_write_same.',
        f' - rewrite read_signal_write_other by discriminate. exact (proj2 (in1 image)). Qed.',
        'Lemma st3 image : CatalogShape P Cat (s3 image) /\\ CombLFP P (write_signal (s2 image) (changed_signal F.fall) (new_value F.fall)) (phase_driven_state P F.fall (s2 image)) /\\ exists seed, CombLFP P seed (s3 image).',
        'Proof. destruct boot_ev as (_ & _ & E3 & _). destruct (st2 image) as (S2 & _). exact (step_ok _ _ E3 S2). Qed.',
        f'Lemma in3 image : read_signal (s3 image) {clk0}%nat = 0 /\\ read_signal (s3 image) {rst0}%nat = 0.',
        f'Proof. unfold s3. rewrite in_clk, in_rst. unfold F.fall. cbn [changed_signal new_value]. split.',
        f' - apply read_signal_write_same.',
        f' - rewrite read_signal_write_other by discriminate. exact (proj2 (in2 image)). Qed.',
        'Lemma st4 image : CatalogShape P Cat (s4 image) /\\ CombLFP P (write_signal (s3 image) (changed_signal F.reset_release) (new_value F.reset_release)) (phase_driven_state P F.reset_release (s3 image)) /\\ exists seed, CombLFP P seed (s4 image).',
        'Proof. destruct boot_ev as (_ & _ & _ & E4). destruct (st3 image) as (S3 & _). exact (step_ok _ _ E4 S3). Qed.',
        f'Lemma in4 image : read_signal (s4 image) {clk0}%nat = 0 /\\ read_signal (s4 image) {rst0}%nat = 1.',
        f'Proof. unfold s4. rewrite in_clk, in_rst. unfold F.reset_release. cbn [changed_signal new_value]. split.',
        f' - rewrite read_signal_write_other by discriminate. exact (proj1 (in3 image)).',
        f' - apply read_signal_write_same. Qed.',
    ]
    # NetWords of s1, s2, s3 (hypotheses of the next steps)
    for k, (cv, rv) in ((1, (0, 0)), (2, (1, 0)), (3, (0, 0))):
        L += [f'Lemma nw{k} image : E.NetWords (s{k} image).',
              f'Proof. destruct (st{k} image) as (S & _). destruct (in{k} image) as [H0 H1]. apply (shape_networds _ S); [rewrite H0|rewrite H1]; vm_compute; reflexivity. Qed.']
    L += ['Lemma nw0 image : E.NetWords (s0 image).',
          f'Proof. apply (shape_networds _ (seed_shape image)); [rewrite seed_clk|rewrite seed_rst]; vm_compute; reflexivity. Qed.']
    # ---- step hypotheses bundles
    L += ['Lemma step1_sel image : selected_on_transition P (s0 image) (phase_driven_state P F.reset_assert (s0 image)) = [' +
          ';'.join(f'process_{i}' for i in E.expected_scen(procs, clk0, rst0, E.SCEN["bootassert"])) + '].',
          'Proof. destruct (st1 image) as (_ & HD & _). exact (ER.sel_bootassert F.reset_assert (s0 image) eq_refl eq_refl (seed_clk image) (seed_rst image) (seed_zero image) (nw0 image) HD). Qed.',
          f'Lemma hyps1 image : changed_signal F.reset_assert = {rst0}%nat /\\ new_value F.reset_assert = 0 /\\ read_signal (s0 image) {clk0}%nat = 0 /\\ read_signal (s0 image) {rst0}%nat = 1 /\\',
          ' ER.NetsZero (s0 image) /\\ E.NetWords (s0 image) /\\ CombLFP P (write_signal (s0 image) (changed_signal F.reset_assert) (new_value F.reset_assert)) (phase_driven_state P F.reset_assert (s0 image)).',
          'Proof. destruct (st1 image) as (_ & HD & _). exact (conj eq_refl (conj eq_refl (conj (seed_clk image) (conj (seed_rst image) (conj (seed_zero image) (conj (nw0 image) HD)))))). Qed.']
    for k, ev, chg, newv, cv, rv in ((2, 'F.rise', clk0, 1, 0, 0), (3, 'F.fall', clk0, 0, 1, 0), (4, 'F.reset_release', rst0, 1, 0, 0)):
        prev = k - 1
        L += [f'Lemma hyps{k} image : changed_signal {ev} = {chg}%nat /\\ new_value {ev} = {newv} /\\ read_signal (s{prev} image) {clk0}%nat = {cv} /\\ read_signal (s{prev} image) {rst0}%nat = {rv} /\\',
              f' E.NetWords (s{prev} image) /\\ (exists seed, CombLFP P seed (s{prev} image)) /\\',
              f' CombLFP P (write_signal (s{prev} image) (changed_signal {ev}) (new_value {ev})) (phase_driven_state P {ev} (s{prev} image)).',
              f'Proof. destruct (st{k} image) as (_ & HD & _). destruct (in{prev} image) as [H0 H1]. destruct (st{prev} image) as (_ & _ & HS).',
              f' exact (conj eq_refl (conj eq_refl (conj H0 (conj H1 (conj (nw{prev} image) (conj HS HD)))))). Qed.']
    # reset-net values in the rise driven state
    for rn in reset_nets:
        assert not net[rn][1], 'inverted reset net'
        L += [f'Lemma rnet_{rn} image : norm 1 (read_signal (phase_driven_state P F.rise (s1 image)) {rn}%nat) = 0.',
              'Proof. destruct (hyps2 image) as (Hc & Hv & H0 & H1 & HW & (seed & HL) & HD). set (d := phase_driven_state P F.rise (s1 image)).',
              ' assert (Wd : E.NetWords d) by (apply E.words_driven; [exact Hc | rewrite Hv; vm_compute; reflexivity | exact HW]).',
              ' destruct (E.prim_driven F.rise (s1 image) Hc) as [D0 D1]. rewrite H1 in D1. fold d in D0, D1.',
              f' pose proof (E.rawp_{rn} _ d HD Wd) as R. rewrite D1 in R. rewrite R. reflexivity. Qed.']
    names = []
    # ---- per register: reset values
    names = []
    for i, (rnet, regs) in sorted(table.items()):
        for R, w, c in regs:
            L += [f'Lemma rv_{R} : exists A, texpr {w}%nat {R}%nat (S.tree_of process_{i}) = ECond {w}%nat (EVar 1 {rnet}%nat) A (EConst {w}%nat {c}).',
                  'Proof. unfold S.tree_of, S.conv_of. vm_compute. eexists. reflexivity. Qed.',
                  f'Lemma step2_{R} image : norm {w} (read_signal (s2 image) {R}%nat) = {c}.',
                  f'Proof. destruct (hyps2 image) as (Hc & Hv & H0 & H1 & HW & (seed & HL) & HD).',
                  f' pose proof (RS.rise0_{R} F.rise (s1 image) seed Hc Hv H0 H1 HW HL HD) as H. destruct rv_{R} as [A HA]. rewrite HA in H.',
                  f' cbn [eval_expr] in H. rewrite (rnet_{rnet} image) in H. cbn in H. exact H. Qed.',
                  f'Lemma step3_{R} image : read_signal (s3 image) {R}%nat = read_signal (s2 image) {R}%nat.',
                  f'Proof. destruct (hyps3 image) as (Hc & Hv & H0 & H1 & HW & (seed & HL) & HD). exact (RF.fall0_frame_{R} F.fall (s2 image) seed Hc Hv H0 H1 HW HL HD). Qed.',
                  f'Lemma step4_{R} image : read_signal (s4 image) {R}%nat = read_signal (s3 image) {R}%nat.',
                  f'Proof. destruct (hyps4 image) as (Hc & Hv & H0 & H1 & HW & (seed & HL) & HD). exact (RF.rrelease0_frame_{R} F.reset_release (s3 image) seed Hc Hv H0 H1 HW HL HD). Qed.',
                  f'Theorem boot_reset_{R} image : norm {w} (read_signal (F.boot image) {R}%nat) = {c}.',
                  f'Proof. rewrite boot_is_s4, step4_{R}, step3_{R}. exact (step2_{R} image). Qed.']
            names.append(f'boot_reset_{R}')
    # ---- clock boundary
    L += ['Theorem boot_clock_boundary image : read_signal (F.boot image) 0%nat = 0 /\\ read_signal (F.boot image) 1%nat = 1.',
          'Proof. rewrite boot_is_s4. exact (in4 image). Qed.']
    names.append('boot_clock_boundary')
    # ---- the valid bits (named, as the cycle layer uses them)
    valid = [141, 250, 286, 308]
    for v in valid:
        L += [f'Theorem boot_valid_{v} image : norm 1 (read_signal (F.boot image) {v}%nat) = 0. Proof. exact (boot_reset_{v} image). Qed.']
        names.append(f'boot_valid_{v}')
    # ---- RF bank: all-zero abstract register file
    L += [f'Theorem boot_rf image : RFRel (read_signal (F.boot image) {bank}%nat) (fun _ => 0).',
          f'Proof. rewrite boot_is_s4. unfold s4. destruct (hyps4 image) as (Hc & Hv & H0 & H1 & HW & (seed & HL) & HD).',
          f' rewrite (RF.rrelease0_frame_{bank} F.reset_release (s3 image) seed Hc Hv H0 H1 HW HL HD).',
          f' destruct (hyps3 image) as (Hc3 & Hv3 & H03 & H13 & HW3 & (seed3 & HL3) & HD3).',
          f' set (d := phase_driven_state P F.fall (s2 image)).',
          f' assert (Wd : E.NetWords d) by (apply E.words_driven; [exact Hc3 | rewrite Hv3; vm_compute; reflexivity | exact HW3]).',
          f' destruct (E.prim_driven F.fall (s2 image) Hc3) as [D0 D1]. rewrite H13 in D1. fold d in D0, D1.',
          f' pose proof (E.rawp_{fall_net} _ d HD3 Wd) as R. rewrite D1 in R.',
          f' exact (RFM.rf_rel_reset F.fall (s2 image) (ltac:(rewrite Hc3; discriminate)) (ER.fall0_match_{rf_proc} F.fall (s2 image) seed3 Hc3 Hv3 H03 H13 HW3 HL3 HD3) (ltac:(cbn [eval_expr]; fold d; rewrite R; reflexivity))). Qed.']
    names.append('boot_rf')
    # ---- RAM
    ram_text = ram_block(ast, pr, procs, rbank, we, chain_we, wreg, fall_net)
    L += ram_text
    names += ['boot_ram', 'boot_ram_zero']
    body = (f'(** {design}: reset layer: the real boot events (F.boot) leave the pipeline empty (four valid bits 0) and every sequential register at its reset value.\n'
            f'    Generated by tools/cpu_tmpl_bzreset.py. proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + HDR +
            f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\n')
    body += ''.join(f'Print Assumptions {module}.{n}.\n' for n in names)
    return body, [f'{module}.{n}' for n in names], dict(registers=sum(len(r) for _, (_, r) in table.items()), reset_nets=reset_nets, rf=bank, ram=rbank)


def ram_block(ast, pr, procs, rbank, we, chain_we, wreg, fall_net):
    clk0, rst0 = pr['events']['clock']['id'], pr['events']['reset']['id']
    L = []
    # copy-wire lemmas of the write-enable chain
    for s in chain_we:
        c = ast.comb[s]
        t_ = c['rhs'][2]
        L += [f'Definition orig_w{s}:Expr:={T.coq(c["rhs"])}.',
              f'Theorem eq_w{s} seed fixed:CombLFP P seed fixed->norm 1(read_signal fixed {s}%nat)=norm 1(eval_expr fixed orig_w{s}).',
              f'Proof. intro HL. refine(checked_assignment_binding P _ {c["k"]}%nat {c["name"]} false orig_w{s} 1%nat {s}%nat seed fixed eq_refl _ _ _ _ HL).',
              ' all: first[vm_compute;reflexivity|(vm_compute;lia)]. Qed.',
              f'Theorem cp_{s} seed d : CombLFP P seed d -> norm 1(read_signal d {s}%nat)=norm 1(read_signal d {t_}%nat).',
              f'Proof. intro HL. rewrite(eq_w{s} seed d HL). unfold orig_w{s}. cbn[eval_expr]. rewrite norm_idempotent. reflexivity. Qed.']
    # we = 0 at the rise driven state
    steps = ' '.join(f'rewrite (cp_{s} _ _ HD).' for s in chain_we)
    L += [f'Lemma we_zero image : norm 1 (read_signal (phase_driven_state P F.rise (s1 image)) {we}%nat) = 0.',
          'Proof. destruct (hyps2 image) as (Hc & Hv & H0 & H1 & HW & (seed & HL) & HD).',
          ' destruct (hyps1 image) as (Hc1 & Hv1 & H01 & H11 & HZ1 & HW1 & HD1).',
          ' ' + steps,
          f' rewrite (driven_unchanged P F.rise (s1 image) {wreg}%nat S.comb_unw_{wreg} ltac:(rewrite Hc; discriminate)).',
          f' pose proof (RF.bootassert_frame_{wreg} F.reset_assert (s0 image) ' + 'Hc1 Hv1 H01 H11 HZ1 HW1 HD1) as Fr.',
          ' unfold s1. rewrite Fr. vm_compute. reflexivity. Qed.']
    L += ['Theorem boot_ram image : read_signal (F.boot image) ' + f'{rbank}%nat = read_signal (F.seed image) {rbank}%nat.',
          'Proof. rewrite boot_is_s4. unfold s4.',
          ' destruct (hyps4 image) as (Hc4 & Hv4 & H04 & H14 & HW4 & (seed4 & HL4) & HD4).',
          f' rewrite (RF.rrelease0_frame_{rbank} F.reset_release (s3 image) seed4 Hc4 Hv4 H04 H14 HW4 HL4 HD4).',
          ' destruct (hyps3 image) as (Hc3 & Hv3 & H03 & H13 & HW3 & (seed3 & HL3) & HD3).',
          ' unfold s3.',
          f' rewrite (RF.fall0_frame_{rbank} F.fall (s2 image) seed3 Hc3 Hv3 H03 H13 HW3 HL3 HD3).',
          ' destruct (hyps2 image) as (Hc & Hv & H0 & H1 & HW & (seed & HL) & HD).',
          f' unfold s2. rewrite (RR.ram_hold0 F.rise (s1 image) seed Hc Hv H0 H1 HW HL HD (we_zero image)).',
          ' destruct (hyps1 image) as (Hc1 & Hv1 & H01 & H11 & HZ1 & HW1 & HD1).',
          ' unfold s1. exact (' + f'RF.bootassert_frame_{rbank} F.reset_assert (s0 image) Hc1 Hv1 H01 H11 HZ1 HW1 HD1)' + '. Qed.',
          f'Theorem boot_ram_zero image : read_signal (F.boot image) {rbank}%nat = 0.',
          'Proof. rewrite boot_ram. vm_compute. reflexivity. Qed.']
    return L


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', default='bzeeno')
    ap.add_argument('--module', default='BzTmplReset')
    ap.add_argument('--out', required=True)
    ap.add_argument('--namespace', default='TmplBzReset')
    ap.add_argument('--accept', action='store_true')
    ap.add_argument('--provider', action='append', default=[])
    a = ap.parse_args()
    body, exports, info = build(a.design, a.module)
    if a.accept:
        import cpu_tmpl_accept as acc
        prov = json.loads(Path('results/r-tmpl-bz-env-20261103-a2/providers.json').read_text())
        prov += [dict(namespace='TmplBzEnv', directory=str(Path('results/r-tmpl-bz-env-20261103-a2').resolve()))]
        prov += [dict(namespace=x.split('=')[0], directory=str(Path(x.split('=')[1]).resolve())) for x in a.provider]
        r = acc.accept(a.out, a.namespace, a.module, body, exports, [('results/pending-configured-input-20261024-a4-bzeeno', 'GeneratedRuntimeInput')], providers=prov,
                       extra=dict(generator='tools/cpu_tmpl_bzreset.py', design=a.design, info=info,
                                  reused_low_level_facts=['GeneratedBoundedPhase.Phase.original_phase', 'GeneratedBoundedPhase.Phase.original_phase_shape',
                                                          'GeneratedSeedBoot.Bootstrap.seed_shape', 'GeneratedSeedBoot.Bootstrap.boot_events_allowed',
                                                          'GeneratedSeedBoot.FrozenEnvironment (definitions of seed/boot/events)']))
        print(json.dumps({k: r[k] for k in r if k in ('accepted', 'coqc_seconds', 'coqchk_seconds', 'assumptions')}))
        sys.exit(0 if r['accepted'] else 1)
    Path(a.out).write_text(body)
    print(a.out, len(body.splitlines()), 'lines', info)
