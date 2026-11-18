#!/usr/bin/env python3
"""Stage-register steps at the primary rising edge for a pipeline whose sequential processes are decision trees
(reset / flush / enable guards; leaves are blocks of non-blocking assignments), clocked through derived nets.

For every register R written by a sequential process Q that fires on the rise (template_roles.fires_on_rise), emit
  rise_<R>: (rise hypotheses of the edge layer) -> norm w (read (PhaseSemantics P ev pre) R) = norm w (eval driven (tree_expr w R tree(Q)))
proved by ExtendedSVSeqTree.seq_tree_value with the selection fact from the edge layer. Registers written through part selects
(the RF bank) are not handled here; they belong to the RF layer.
Untrusted generator; Coq checks everything. proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
"""
import json
import sys
from pathlib import Path
import cpu_tmpl_roles as roles
import cpu_tmpl_ast as T
import cpu_tmpl_edge as E


def full_width_regs(ast, i, rootmap):
    """registers of process i all of whose writes are full-width LVar (no part select)"""
    out = {}

    def walk(s):
        if s[0] == 'SAssign':
            lv = s[3]
            if lv[0] != 'LVar':
                r = lv
                while r[0] == 'LSel':
                    r = r[2]
                out[r[2]] = None
            else:
                out.setdefault(lv[2], lv[1])
        elif s[0] == 'SSeq':
            for c in s[1]:
                walk(c)
        elif s[0] == 'SIf':
            walk(s[2]); walk(s[3])
    walk(ast.procs[i]['body'])
    return out


def convertible(s):
    """Mirror of ExtendedSVSeqTree.conv shapes: SIf trees whose leaves are NBA blocks (additive: lets the generator skip processes the library cannot convert)."""
    if s[0] == 'SSkip' or (s[0] == 'SAssign' and s[1]):
        return True
    if s[0] == 'SIf':
        return convertible(s[2]) and convertible(s[3])
    if s[0] == 'SSeq':
        if all(c[0] == 'SAssign' and c[1] for c in s[1]):
            return True
        return len(s[1]) == 1 and s[1][0][0] == 'SIf' and convertible(s[1][0])
    return False


def build(design, module, edge_mod, rise_procs=None):
    ast, pr, tr = roles.load_all(design)
    clk0, rst0, net, chain, procs = E.nets(ast, pr)
    rise = rise_procs or E.expected(procs, clk0, rst0, 0, 1, E.RST_IDLE)
    prog = pr['ast']['program']
    pmod = prog.split('.')[0]
    hdr = E.HDR.replace('@AST@', pr['ast']['module'] + ' Lang.ExtendedSVSeqTree Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice ' + edge_mod.rsplit('.', 1)[0]).replace('@OPEN@', pmod + ' ExtendedSVSeqTree ExtendedSVRootProjection ExtendedSVProcessSlice')
    hyps = (f' changed_signal ev = {clk0}%nat -> new_value ev = 1 -> read_signal pre {clk0}%nat = 0 ->'
            f' read_signal pre {rst0}%nat = {E.RST_IDLE} -> {edge_mod}.NetWords pre -> CombLFP P seed pre ->'
            f' CombLFP P(write_signal pre(changed_signal ev)(new_value ev))(phase_driven_state P ev pre) ->')
    args = 'Hc Hv H0 H1 HW HL HD'
    L = [f'Notation P := {prog.split(".")[-1]} (only parsing).',
         'Definition inner_of (q : Process) : Stmt := match process_body q with SSeq [SSeq [t]] => t | _ => SSkip end.',
         'Definition conv_of (q : Process) := conv 64%nat (inner_of q).',
         'Definition need_of (q : Process) : nat := match conv_of q with Some (d, _) => d | None => 0%nat end.',
         'Definition tree_of (q : Process) : Tree := match conv_of q with Some (_, T) => T | None => TLeaf [] end.']
    flat = lambda i: not (ast.procs[i]['body'][0] == 'SSeq' and len(ast.procs[i]['body'][1]) == 1 and ast.procs[i]['body'][1][0][0] == 'SSeq')
    if any(flat(i) for i in rise):    # additive: processes whose body is SSeq [t] (Steel); library ExtendedSVSeqTreeFlat
        hdr = hdr.replace('Lang.ExtendedSVSeqTree ', 'Lang.ExtendedSVSeqTree Lang.ExtendedSVSeqTreeFlat ', 1)
        hdr = hdr.replace(' ExtendedSVSeqTree ExtendedSVRootProjection', ' ExtendedSVSeqTree ExtendedSVSeqTreeFlat ExtendedSVRootProjection', 1)
        L += ['Definition inner_of_f (q : Process) : Stmt := match process_body q with SSeq [t] => t | _ => SSkip end.',
              'Definition conv_of_f (q : Process) := conv 64%nat (inner_of_f q).',
              'Definition need_of_f (q : Process) : nat := match conv_of_f q with Some (d, _) => d | None => 0%nat end.',
              'Definition tree_of_f (q : Process) : Tree := match conv_of_f q with Some (_, T) => T | None => TLeaf [] end.']
    names, skipped = [], []
    for i in rise:
        regs = full_width_regs(ast, i, None)
        if any(w is None for w in regs.values()):
            skipped.append((i, [r for r, w in regs.items() if w is None]))
        bd = ast.procs[i]['body']
        if flat(i):
            inner_ok = len(bd[1]) == 1 and convertible(bd[1][0])
        else:
            inner_ok = len(bd[1][0][1]) == 1 and convertible(bd[1][0][1][0])
        if not inner_ok:    # the library cannot convert this body (e.g. several statements next to a tree): no lemma, recorded
            skipped.append((i, ['not_convertible']))
            continue
        if flat(i):
            L += [f'Lemma body_{i} : process_body process_{i} = SSeq [inner_of_f process_{i}]. Proof. reflexivity. Qed.',
                  f'Lemma conv_{i} : conv 64%nat (inner_of_f process_{i}) = Some (need_of_f process_{i}, tree_of_f process_{i}).',
                  f'Proof. unfold need_of_f, tree_of_f, conv_of_f. destruct (conv 64%nat (inner_of_f process_{i})) as [[d T]|] eqn:E; [reflexivity|]. vm_compute in E. discriminate. Qed.',
                  f'Lemma rel_{i} : Rel (need_of_f process_{i}) (inner_of_f process_{i}) (tree_of_f process_{i}). Proof. exact (conv_sound _ _ _ _ conv_{i}). Qed.',
                  f'Lemma depth_{i} : (need_of_f process_{i} + 1 <= statement_fuel P)%nat. Proof. vm_compute; lia. Qed.']
        else:
                L += [f'Lemma body_{i} : process_body process_{i} = SSeq [SSeq [inner_of process_{i}]]. Proof. reflexivity. Qed.',
                  f'Lemma conv_{i} : conv 64%nat (inner_of process_{i}) = Some (need_of process_{i}, tree_of process_{i}).',
                  f'Proof. unfold need_of, tree_of, conv_of. destruct (conv 64%nat (inner_of process_{i})) as [[d T]|] eqn:E; [reflexivity|]. vm_compute in E. discriminate. Qed.',
                  f'Lemma rel_{i} : Rel (need_of process_{i}) (inner_of process_{i}) (tree_of process_{i}). Proof. exact (conv_sound _ _ _ _ conv_{i}). Qed.',
                  f'Lemma depth_{i} : (need_of process_{i} + 2 <= statement_fuel P)%nat. Proof. vm_compute; lia. Qed.']
        sfx = '_f' if flat(i) else ''
        lem = 'seq_tree_value_flat' if flat(i) else 'seq_tree_value'
        for R, w in sorted(regs.items()):
            if w is None:
                continue
            L += [f'Lemma comb_unw_{R} : comb_root_unwrittenb P {R}%nat = true. Proof. vm_compute; reflexivity. Qed.',
                  f'Lemma writers_{R} : filter (writes_rootb {R}%nat) (processes P) = [process_{i}]. Proof. vm_compute; reflexivity. Qed.',
                  f'Lemma wf_{R} : twf {w}%nat {R}%nat (tree_of{sfx} process_{i}) = true. Proof. vm_compute; reflexivity. Qed.',
                  f'Theorem rise_{R} ev pre seed :{hyps}',
                  f' norm {w}(read_signal(PhaseSemantics P ev pre){R}%nat)=norm {w}(eval_expr(phase_driven_state P ev pre)(texpr {w}%nat {R}%nat (tree_of{sfx} process_{i}))).',
                  f'Proof. intros {args}.',
                  f' refine({lem} P ev pre {R}%nat process_{i} (inner_of{sfx} process_{i}) (tree_of{sfx} process_{i}) (need_of{sfx} process_{i}) {w}%nat comb_unw_{R}'
                  f' (fun H => let Hn : {clk0}%nat = {R}%nat := eq_trans (eq_sym Hc) H in ltac:(discriminate Hn)) body_{i} rel_{i} depth_{i} _ wf_{R}).',
                  f' rewrite writers_{R}. cbn[filter]. rewrite({edge_mod}.sel_rise_match_{i} ev pre seed {args}). reflexivity. Qed.']
            names.append(f'rise_{R}')
    body = (f'(** {design}: stage-register steps at the primary rising edge, generated by tools/cpu_tmpl_stage.py.\n'
            f'    proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + hdr +
            f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\n')
    body += ''.join(f'Print Assumptions {module}.{n}.\n' for n in names)
    return body, [f'{module}.{n}' for n in names], dict(processes=[f'process_{i}' for i in rise], registers=len(names), skipped_part_select=skipped)


def frame_text(design, module, edge_mod):
    """Frame lemmas: registers of sequential processes that do not fire on an edge keep their value over that phase."""
    ast, pr, tr = roles.load_all(design)
    clk0, rst0, net, chain, procs = E.nets(ast, pr)
    prog = pr['ast']['program']
    pmod = prog.split('.')[0]
    hdr = E.HDR.replace('@AST@', pr['ast']['module'] + ' Lang.ExtendedSVSeqTree Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice ' + edge_mod.rsplit('.', 1)[0]).replace('@OPEN@', pmod + ' ExtendedSVSeqTree ExtendedSVRootProjection ExtendedSVProcessSlice')
    args = 'Hc Hv H0 H1 HW HL HD'
    L = [f'Notation P := {prog.split(".")[-1]} (only parsing).']
    names = []
    seqs = {i for i, _ in procs}
    written = {i: E.assigned_roots(ast.procs[i]['body']) for i in seqs}
    for nm, old, new in (('rise', 0, 1), ('fall', 1, 0)):
        fire = E.expected(procs, clk0, rst0, old, new, E.RST_IDLE)
        hyps = (f' changed_signal ev = {clk0}%nat -> new_value ev = {new} -> read_signal pre {clk0}%nat = {old} ->'
                f' read_signal pre {rst0}%nat = {E.RST_IDLE} -> {edge_mod}.NetWords pre -> CombLFP P seed pre ->'
                f' CombLFP P(write_signal pre(changed_signal ev)(new_value ev))(phase_driven_state P ev pre) ->')
        roots = sorted({r for i in seqs if i not in fire for r in written[i]})
        for R in roots:
            ws = [i for i in seqs if R in written[i]]
            if any(i in fire for i in ws):
                continue            # also written by a firing process: not a frame
            rw = ', '.join(f'{edge_mod}.sel_{nm}_match_{i} ev pre seed {args}' for i in sorted(ws))
            L += [f'Lemma comb_unw_{R} : comb_root_unwrittenb P {R}%nat = true. Proof. vm_compute; reflexivity. Qed.'
                  if f'comb_unw_{R} ' not in '\n'.join(L) else '',
                  f'Lemma writers_{R} : filter (writes_rootb {R}%nat) (processes P) = [' + ';'.join(f'process_{i}' for i in sorted(ws)) + ']. Proof. vm_compute; reflexivity. Qed.'
                  if f'Lemma writers_{R} ' not in '\n'.join(L) else '',
                  f'Theorem {nm}_frame_{R} ev pre seed :{hyps}',
                  f' read_signal(PhaseSemantics P ev pre){R}%nat=read_signal pre {R}%nat.',
                  f'Proof. intros {args}. refine(seq_frame P ev pre {R}%nat comb_unw_{R} (fun H => let Hn : {clk0}%nat = {R}%nat := eq_trans (eq_sym Hc) H in ltac:(discriminate Hn)) _).',
                  f' rewrite writers_{R}. cbn[filter]. rewrite ({rw}). reflexivity. Qed.']
            names.append(f'{nm}_frame_{R}')
    body = (f'(** {design}: frame lemmas of non-firing sequential processes, generated by tools/cpu_tmpl_stage.py --frame.\n'
            f'    proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + hdr + f'Module {module}.\n' + '\n'.join(x for x in L if x) +
            f'\nEnd {module}.\n' + ''.join(f'Print Assumptions {module}.{n}.\n' for n in names))
    return body, [f'{module}.{n}' for n in names], dict(frames=len(names))


def ram_text(design, module, edge_mod, stage_mod):
    """RAM hold at the rising edge when the write enable is 0 (part-select write tree guarded by the enable)."""
    ast, pr, tr = roles.load_all(design)
    clk0, rst0, net, chain, procs = E.nets(ast, pr)
    ram = pr['ram']
    bank, we = ram['bank']['id'], ram['write_enable']['id']
    wp = int(ram['write_process'].split('_')[1])
    assert wp in E.expected(procs, clk0, rst0, 0, 1, E.RST_IDLE)
    prog = pr['ast']['program']
    pmod = prog.split('.')[0]
    hdr = E.HDR.replace('@AST@', pr['ast']['module'] + ' Lang.ExtendedSVSeqTree Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice ' + edge_mod.rsplit('.', 1)[0] + ' ' + stage_mod.rsplit('.', 1)[0]).replace('@OPEN@', pmod + ' ExtendedSVSeqTree ExtendedSVRootProjection ExtendedSVProcessSlice')
    args = 'Hc Hv H0 H1 HW HL HD'
    S = stage_mod
    hyps = (f' changed_signal ev = {clk0}%nat -> new_value ev = 1 -> read_signal pre {clk0}%nat = 0 ->'
            f' read_signal pre {rst0}%nat = {E.RST_IDLE} -> {edge_mod}.NetWords pre -> CombLFP P seed pre ->'
            f' CombLFP P(write_signal pre(changed_signal ev)(new_value ev))(phase_driven_state P ev pre) ->')
    L = [f'Notation P := {prog.split(".")[-1]} (only parsing).',
         f'Lemma comb_unw_{bank} : comb_root_unwrittenb P {bank}%nat = true. Proof. vm_compute; reflexivity. Qed.',
         f'Lemma writers_{bank} : filter (writes_rootb {bank}%nat) (processes P) = [process_{wp}]. Proof. vm_compute; reflexivity. Qed.',
         f'Lemma ram_shape : exists y, {S}.tree_of process_{wp} = TIf (EVar 1 {we}%nat) y (TLeaf []).',
         f'Proof. unfold {S}.tree_of, {S}.conv_of. vm_compute. eexists. reflexivity. Qed.',
         f'Theorem ram_hold ev pre seed :{hyps}',
         f' norm 1(read_signal(phase_driven_state P ev pre){we}%nat)=0 -> read_signal(PhaseSemantics P ev pre){bank}%nat=read_signal pre {bank}%nat.',
         f'Proof. intros {args} Hz. destruct ram_shape as [y Hy].',
         f' refine(seq_tree_hold P ev pre {bank}%nat process_{wp} ({S}.inner_of process_{wp}) ({S}.tree_of process_{wp}) ({S}.need_of process_{wp}) comb_unw_{bank}'
         f' (fun H => let Hn : {clk0}%nat = {bank}%nat := eq_trans (eq_sym Hc) H in ltac:(discriminate Hn)) {S}.body_{wp} {S}.rel_{wp} {S}.depth_{wp} _ _).',
         f' - rewrite writers_{bank}. cbn[filter]. rewrite({edge_mod}.sel_rise_match_{wp} ev pre seed {args}). reflexivity.',
         f' - rewrite Hy. cbn[tleaf]. cbn[eval_expr]. rewrite Hz. reflexivity.',
         'Qed.']
    body = (f'(** {design}: RAM hold at the rising edge when the write enable is 0, generated by tools/cpu_tmpl_stage.py --ram.\n'
            f'    proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + hdr + f'Module {module}.\n' + '\n'.join(L) +
            f'\nEnd {module}.\nPrint Assumptions {module}.ram_hold.\n')
    return body, [f'{module}.ram_hold'], dict(bank=bank, enable=we)


# ---------------------------------------------------------------------------------------------------------------------------
# Reset variants (options --reset-stage / --reset-frame / --reset-ram, additive; see cpu_tmpl_edge.SCEN):
# the register steps, frames and RAM hold for events on the primary reset and for clock events with reset 0.
RESET_STEP_SCEN = ('rise0', 'rassert0', 'rassert1')
RESET_FRAME_SCEN = ('rise0', 'fall0', 'rassert0', 'rrelease0', 'bootassert')


def _reset_hdr(pr, edge_mod, edger_mod, stage_mod=None):
    mods = pr['ast']['module'] + ' Lang.ExtendedSVSeqTree Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice ' + edge_mod.rsplit('.', 1)[0] + ' ' + edger_mod.rsplit('.', 1)[0]
    if stage_mod:
        mods += ' ' + stage_mod.rsplit('.', 1)[0]
    pmod = pr['ast']['program'].split('.')[0]
    return E.HDR.replace('@AST@', mods).replace('@OPEN@', pmod + ' ExtendedSVSeqTree ExtendedSVRootProjection ExtendedSVProcessSlice')


def reset_stage_text(design, module, edge_mod, edger_mod, stage_mod):
    ast, pr, tr = roles.load_all(design)
    clk0, rst0, net, chain, procs = E.nets(ast, pr)
    prog = pr['ast']['program']
    hdr = _reset_hdr(pr, edge_mod, edger_mod, stage_mod)
    L = [f'Notation P := {prog.split(".")[-1]} (only parsing).', f'Module E := {edge_mod}.', f'Module ER := {edger_mod}.', f'Module S := {stage_mod}.']
    names = []
    for scen in RESET_STEP_SCEN:
        sc = E.SCEN[scen]
        fire = E.expected_scen(procs, clk0, rst0, sc)
        hyps = E.scen_hyps(sc, clk0, rst0, 'E', 'ER.NetsZero')
        args = E.scen_args(sc)
        changed = clk0 if sc['kind'] == 'clk' else rst0
        for i in fire:
            for R, w in sorted(full_width_regs(ast, i, None).items()):
                if w is None:
                    continue
                L += [f'Theorem {scen}_{R} ev pre seed :{hyps}',
                      f' norm {w}(read_signal(PhaseSemantics P ev pre){R}%nat)=norm {w}(eval_expr(phase_driven_state P ev pre)(texpr {w}%nat {R}%nat (S.tree_of process_{i}))).',
                      f'Proof. intros {args}.',
                      f' refine(seq_tree_value P ev pre {R}%nat process_{i} (S.inner_of process_{i}) (S.tree_of process_{i}) (S.need_of process_{i}) {w}%nat S.comb_unw_{R}'
                      f' (fun H => let Hn : {changed}%nat = {R}%nat := eq_trans (eq_sym Hc) H in ltac:(discriminate Hn)) S.body_{i} S.rel_{i} S.depth_{i} _ S.wf_{R}).',
                      f' rewrite S.writers_{R}. cbn[filter]. rewrite(ER.{scen}_match_{i} ev pre seed {args}). reflexivity. Qed.']
                names.append(f'{scen}_{R}')
    body = (f'(** {design}: stage-register steps for clock events with reset 0 and for events on the primary reset, generated by tools/cpu_tmpl_stage.py --reset-stage.\n'
            f'    proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + hdr + f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\n')
    body += ''.join(f'Print Assumptions {module}.{n}.\n' for n in names)
    return body, [f'{module}.{n}' for n in names], dict(registers=len(names))


def reset_frame_text(design, module, edge_mod, edger_mod):
    ast, pr, tr = roles.load_all(design)
    clk0, rst0, net, chain, procs = E.nets(ast, pr)
    prog = pr['ast']['program']
    hdr = _reset_hdr(pr, edge_mod, edger_mod)
    L = [f'Notation P := {prog.split(".")[-1]} (only parsing).', f'Module E := {edge_mod}.', f'Module ER := {edger_mod}.']
    seqs = {i for i, _ in procs}
    written = {i: E.assigned_roots(ast.procs[i]['body']) for i in seqs}
    names, done = [], set()
    for scen in RESET_FRAME_SCEN:
        sc = E.SCEN[scen]
        fire = E.expected_scen(procs, clk0, rst0, sc)
        hyps = E.scen_hyps(sc, clk0, rst0, 'E', 'ER.NetsZero')
        args = E.scen_args(sc)
        zero = sc.get('zero_pre')
        changed = clk0 if sc['kind'] == 'clk' else rst0
        roots = sorted({r for i in seqs if i not in fire for r in written[i]})
        for R in roots:
            ws = sorted(i for i in seqs if R in written[i])
            if any(i in fire for i in ws):
                continue
            rw = ', '.join(f'ER.{scen}_match_{i} ev pre{"" if zero else " seed"} {args}' for i in ws)
            if ('c', R) not in done:
                L.append(f'Lemma comb_unw_{R} : comb_root_unwrittenb P {R}%nat = true. Proof. vm_compute; reflexivity. Qed.')
                L.append(f'Lemma writers_{R} : filter (writes_rootb {R}%nat) (processes P) = [' + ';'.join(f'process_{i}' for i in ws) + ']. Proof. vm_compute; reflexivity. Qed.')
                done.add(('c', R))
            L += [f'Theorem {scen}_frame_{R} ev pre{"" if zero else " seed"} :{hyps}',
                  f' read_signal(PhaseSemantics P ev pre){R}%nat=read_signal pre {R}%nat.',
                  f'Proof. intros {args}. refine(seq_frame P ev pre {R}%nat comb_unw_{R} (fun H => let Hn : {changed}%nat = {R}%nat := eq_trans (eq_sym Hc) H in ltac:(discriminate Hn)) _).',
                  f' rewrite writers_{R}. cbn[filter]. rewrite ({rw}). reflexivity. Qed.']
            names.append(f'{scen}_frame_{R}')
    body = (f'(** {design}: frame lemmas of non-firing sequential processes for the reset scenarios, generated by tools/cpu_tmpl_stage.py --reset-frame.\n'
            f'    proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + hdr + f'Module {module}.\n' + '\n'.join(L) +
            f'\nEnd {module}.\n' + ''.join(f'Print Assumptions {module}.{n}.\n' for n in names))
    return body, [f'{module}.{n}' for n in names], dict(frames=len(names))


def reset_ram_text(design, module, edge_mod, edger_mod, stage_mod):
    """RAM hold at a clock rise with reset 0 when the write enable is 0."""
    ast, pr, tr = roles.load_all(design)
    clk0, rst0, net, chain, procs = E.nets(ast, pr)
    ram = pr['ram']
    bank, we = ram['bank']['id'], ram['write_enable']['id']
    wp = int(ram['write_process'].split('_')[1])
    sc = E.SCEN['rise0']
    assert wp in E.expected_scen(procs, clk0, rst0, sc)
    prog = pr['ast']['program']
    hdr = _reset_hdr(pr, edge_mod, edger_mod, stage_mod)
    hyps = E.scen_hyps(sc, clk0, rst0, 'E', 'ER.NetsZero')
    args = E.scen_args(sc)
    L = [f'Notation P := {prog.split(".")[-1]} (only parsing).', f'Module E := {edge_mod}.', f'Module ER := {edger_mod}.', f'Module S := {stage_mod}.',
         f'Lemma comb_unw_{bank} : comb_root_unwrittenb P {bank}%nat = true. Proof. vm_compute; reflexivity. Qed.',
         f'Lemma writers_{bank} : filter (writes_rootb {bank}%nat) (processes P) = [process_{wp}]. Proof. vm_compute; reflexivity. Qed.',
         f'Lemma ram_shape : exists y, S.tree_of process_{wp} = TIf (EVar 1 {we}%nat) y (TLeaf []).',
         f'Proof. unfold S.tree_of, S.conv_of. vm_compute. eexists. reflexivity. Qed.',
         f'Theorem ram_hold0 ev pre seed :{hyps}',
         f' norm 1(read_signal(phase_driven_state P ev pre){we}%nat)=0 -> read_signal(PhaseSemantics P ev pre){bank}%nat=read_signal pre {bank}%nat.',
         f'Proof. intros {args} Hz. destruct ram_shape as [y Hy].',
         f' refine(seq_tree_hold P ev pre {bank}%nat process_{wp} (S.inner_of process_{wp}) (S.tree_of process_{wp}) (S.need_of process_{wp}) comb_unw_{bank}'
         f' (fun H => let Hn : {clk0}%nat = {bank}%nat := eq_trans (eq_sym Hc) H in ltac:(discriminate Hn)) S.body_{wp} S.rel_{wp} S.depth_{wp} _ _).',
         f' - rewrite writers_{bank}. cbn[filter]. rewrite(ER.rise0_match_{wp} ev pre seed {args}). reflexivity.',
         f' - rewrite Hy. cbn[tleaf]. cbn[eval_expr]. rewrite Hz. reflexivity.',
         'Qed.']
    body = (f'(** {design}: RAM hold at a clock rise with reset 0 when the write enable is 0, generated by tools/cpu_tmpl_stage.py --reset-ram.\n'
            f'    proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + hdr + f'Module {module}.\n' + '\n'.join(L) +
            f'\nEnd {module}.\nPrint Assumptions {module}.ram_hold0.\n')
    return body, [f'{module}.ram_hold0'], dict(bank=bank, enable=we)


if __name__ == '__main__':
    import argparse
    import cpu_tmpl_accept as acc
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', default='bzeeno')
    ap.add_argument('--module', default='BzTmplStage')
    ap.add_argument('--namespace')
    ap.add_argument('--edge', default='TmplBzEdge.BzTmplEdge.BzTmplEdge')
    ap.add_argument('--out', required=True)
    ap.add_argument('--provider', action='append', default=[])
    ap.add_argument('--accept', action='store_true')
    ap.add_argument('--frame', action='store_true')
    ap.add_argument('--ram', action='store_true')
    ap.add_argument('--stage', default='TmplBzStage.BzTmplStage.BzTmplStage')
    ap.add_argument('--edger', help='reset-layer edge module (fully qualified); required by --reset-stage/--reset-frame/--reset-ram')
    ap.add_argument('--reset-stage', action='store_true')
    ap.add_argument('--reset-frame', action='store_true')
    ap.add_argument('--reset-ram', action='store_true')
    ap.add_argument('--rise-procs', help='comma list of sequential process indices the decision-tree converter handles (manifest route field); default: all firing on the rise')
    a = ap.parse_args()
    if a.reset_stage:
        body, exports, info = reset_stage_text(a.design, a.module, a.edge, a.edger, a.stage)
    elif a.reset_frame:
        body, exports, info = reset_frame_text(a.design, a.module, a.edge, a.edger)
    elif a.reset_ram:
        body, exports, info = reset_ram_text(a.design, a.module, a.edge, a.edger, a.stage)
    else:
        body, exports, info = ram_text(a.design, a.module, a.edge, a.stage) if a.ram else (frame_text if a.frame else (lambda d, m, e: build(d, m, e, rise_procs=[int(x) for x in a.rise_procs.split(',')] if a.rise_procs else None)))(a.design, a.module, a.edge)
    if not a.accept:
        Path(a.out).write_text(body)
        print(a.out, len(body.splitlines()), 'lines', info)
        sys.exit(0)
    prof = json.loads(Path(f'framework/auto-contract-profiles/{a.design}.json').read_text())
    lp = [(prof['pipeline_roles']['ast']['file'].rsplit('/', 1)[0], prof['pipeline_roles']['ast']['module'].split('.')[0])]
    prov = [dict(namespace=x.split('=')[0], directory=str(Path(x.split('=')[1]).resolve())) for x in a.provider]
    r = acc.accept(a.out, a.namespace, a.module, body, exports, lp, providers=prov,
                   extra=dict(generator='tools/cpu_tmpl_stage.py', design=a.design, info=info,
                              libraries=['src/Lang/ExtendedSVSeqTree.v']))
    print(json.dumps(r, indent=1))
    sys.exit(0 if r['accepted'] else 1)

