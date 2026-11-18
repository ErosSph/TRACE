#!/usr/bin/env python3
"""Edge layer for designs whose sequential processes are clocked through derived clock/reset wires.

Option `--design bzeeno` (generic: any AST whose sequential processes have event specs (Posedge clk[, Negedge resetn])
and whose clk/resetn signals are copy or inversion chains of one primary clock input and one primary reset input).
For every such net signal the generator emits (all checked by Coq)
  * the wire equations along the chain (checked_assignment_binding),
  * net_<s>: at a combinational fixed point the signal is the primary clock/reset, possibly inverted,
  * sel_rise / sel_fall: for a clock event on the primary input (reset high), `selected_on_transition P pre driven` is exactly the
    list of sequential processes whose (edge, signal) fires; the list is computed from the AST by simulating the polarities.
These close the `process_matches_states ...` hypotheses of the RF/stage step lemmas (r-tmpl-bzeeno-rf-20261103-a1).
Hypotheses (no correctness assumption on the design): pre is a comb fixed point and a word state on the nets, the driven state is
a fixed point (supplied by the design's low-level phase fact), the primary values before the event.
Untrusted generator; Coq checks everything. proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
"""
import json
import os
import sys
FAST_FILTER = False   # additive option --fast-filter: computed process-index filter instead of `cbn [filter]` (same statements)
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles

RST_IDLE = int(os.environ.get('TMPL_RST_IDLE', '1'))   # level of the primary reset input assumed by the edge lemmas (1: idle level of an active-low reset; Steel has an active-high reset: TMPL_RST_IDLE=0)


def nets(ast, pr):
    """{signal: (primary, inverted)} for every signal in a sequential process event list."""
    clk0, rst0 = pr['events']['clock']['id'], pr['events']['reset']['id']
    out, chain = {}, {}

    def trace(s):
        inv, path = 0, []
        while s not in (clk0, rst0):
            c = ast.comb.get(s)
            if c is None:
                raise ValueError(f'signal {s} is not a copy/not chain from a primary input')
            r = c['rhs']
            path.append(s)
            if r[0] == 'EVar':
                s = r[2]
            elif r[0] == 'EUnary' and r[2] == 'UNot' and r[3][0] == 'EVar':
                inv ^= 1
                s = r[3][2]
            else:
                raise ValueError(f'signal {s}: unsupported net expression {r}')
        return s, inv, path
    procs = []
    for i, p in enumerate(ast.procs):
        if p['kind'] != 'Sequential':
            continue
        specs = []
        for edge, sig in p['events']:
            prim, inv, path = trace(sig)
            out[sig] = (prim, inv)
            chain[sig] = path
            specs.append((edge, sig, prim, inv))
        procs.append((i, specs))
    return clk0, rst0, out, chain, procs


def fires(edge, old, new):
    return (old == 0 and new != 0) if edge == 'Posedge' else (old != 0 and new == 0)


def expected(procs, clk0, rst0, old_clk, new_clk, rst):
    sel = []
    for i, specs in procs:
        hit = False
        for edge, sig, prim, inv in specs:
            if prim == clk0:
                o, n = old_clk ^ inv, new_clk ^ inv
            else:
                o, n = rst ^ inv, rst ^ inv
            hit |= fires(edge, o, n)
        if hit:
            sel.append(i)
    return sel


# Narrow LLM-generated change: Codex (2026-11-09), event certificate emission.
# None uses certificates everywhere; a set of (scenario, process index) supports
# the measured one-process pilot without changing any theorem statement.
MATCH_CERTIFICATES = None


def match_certificate(name, i, specs, clk0, sc, rewrites, finish):
    if MATCH_CERTIFICATES is not None and (name, i) not in MATCH_CERTIFICATES:
        return (f' unfold process_matches_states, process_{i}; cbn[process_kind process_events existsb event_spec_matches_states event_signal event_edge edge_fires];'
                f' {("rewrite " + rewrites + "; ") if rewrites else ""}{finish} Qed.')
    values = []
    for edge, sig, prim, inv in specs:
        old, new = sc['c'] if prim == clk0 else sc['r']
        old, new = old ^ inv, new ^ inv
        if sc.get('zero_pre') and sig not in sc['primary_signals']:
            old = 0
        values.append(f'({old},{new})')
    table = '[' + ';'.join(values) + ']'
    rewrites = ', '.join('?' + x for x in rewrites.split(', ')) if rewrites else ''
    obs = (' apply Forall2_cons; [split; cbn [event_signal fst snd]; ' +
           (("rewrite " + rewrites + "; ") if rewrites else "") + finish.rstrip('.') + '|].') * len(specs)
    return (f' eapply (process_check_sound pre d process_{i} {table}); [reflexivity| |vm_compute; reflexivity].\n'
            f' unfold observations_hold; cbn [process_{i} process_events].' + obs + ' apply Forall2_nil. Qed.')


def text(design, module):
    ast, pr, tr = roles.load_all(design)
    clk0, rst0, net, chain, procs = nets(ast, pr)
    allw = sorted({s for p in chain.values() for s in p})
    order = []

    def visit(s):
        if s in (clk0, rst0) or s in order:
            return
        c = ast.comb[s]['rhs']
        visit(c[2] if c[0] == 'EVar' else c[3][2])
        order.append(s)
    for s in allw:
        visit(s)
    par = {s: (ast.comb[s]['rhs'][2] if ast.comb[s]['rhs'][0] == 'EVar' else ast.comb[s]['rhs'][3][2]) for s in order}
    neg = {s: ast.comb[s]['rhs'][0] != 'EVar' for s in order}
    pinfo = {clk0: (clk0, 0), rst0: (rst0, 0)}
    for s in order:
        pinfo[s] = (pinfo[par[s]][0], pinfo[par[s]][1] ^ int(neg[s]))
    allsig = [clk0, rst0] + order
    wn = lambda x: f'W{x}'
    L = ['Lemma filter_refine {A : Type} (f g : A -> bool) (l : list A) : (forall x, f x = true -> g x = true) ->',
         ' filter f l = filter f (filter g l).',
         'Proof. intro H. induction l as [|a l IH]; cbn [filter]; [reflexivity|]. destruct (g a) eqn:Ga; cbn [filter].',
         ' - destruct (f a) eqn:Fa; [f_equal|]; exact IH.',
         ' - destruct (f a) eqn:Fa; [rewrite (H a Fa) in Ga; discriminate|]. exact IH. Qed.',
         'Definition is_seqb (p : Process) : bool := match process_kind p with Sequential => true | _ => false end.',
         'Lemma matches_seq pre d p : process_matches_states pre d p = true -> is_seqb p = true.',
         'Proof. unfold process_matches_states, is_seqb. destruct (process_kind p); [discriminate|discriminate|intros; reflexivity]. Qed.']
    if FAST_FILTER:
        L += ['Lemma filter_by {A : Type} (f : A -> bool) (l : list A) (bs : list bool) : map f l = bs -> filter f l = map fst (filter snd (combine l bs)).',
              'Proof. revert bs. induction l as [|a l IH]; intros [|b bs] H; cbn [map] in H; try discriminate; [reflexivity|].',
              ' injection H as Hb Hr. cbn [filter combine]. rewrite <- Hb. destruct (f a); cbn [snd fst filter map]; [f_equal|]; apply IH; exact Hr. Qed.']
    for s in order:
        c = ast.comb[s]
        assert c['width'] == 1
        L += [f'Definition orig_w{s}:Expr:={T.coq(c["rhs"])}.',
              f'Theorem eq_w{s} seed fixed:CombLFP P seed fixed->norm 1(read_signal fixed {s}%nat)=norm 1(eval_expr fixed orig_w{s}).',
              f'Proof. intro HL. refine(checked_assignment_binding P _ {c["k"]}%nat {c["name"]} false orig_w{s} 1%nat {s}%nat seed fixed eq_refl _ _ _ _ HL).',
              ' all: first[vm_compute;reflexivity|(vm_compute;lia)]. Qed.']
        t_ = par[s]
        if not neg[s]:
            L += [f'Theorem netn_{s} seed d : CombLFP P seed d -> norm 1(read_signal d {s}%nat)=norm 1(read_signal d {t_}%nat).',
                  f'Proof. intro HL. rewrite(eq_w{s} seed d HL). unfold orig_w{s}. cbn[eval_expr]. rewrite norm_idempotent. reflexivity. Qed.']
        else:
            L += [f'Theorem netn_{s} seed d : CombLFP P seed d -> norm 1(read_signal d {s}%nat)=1-norm 1(read_signal d {t_}%nat).',
                  f'Proof. intro HL. rewrite(eq_w{s} seed d HL). unfold orig_w{s}.',
                  f' destruct(one_bit_cases d {t_}%nat)as[H|H]; cbn[eval_expr]; rewrite H; reflexivity. Qed.']
    L.append('Definition NetWords(s:State):Prop:=' + ' /\\ '.join(f'Word 1(read_signal s {x}%nat)' for x in allsig) + '.')
    pat = '(' + ' & '.join(wn(x) for x in allsig) + ')'
    # raw step and raw-to-primary lemmas
    for s in order:
        t_ = par[s]
        rhs = f'1-read_signal d {t_}%nat' if neg[s] else f'read_signal d {t_}%nat'
        L += [f'Lemma raw_{s} seed d : CombLFP P seed d -> NetWords d -> read_signal d {s}%nat={rhs}.',
              f'Proof. intros HL HW. pose proof(netn_{s} seed d HL) as E. unfold NetWords,Word in HW.',
              f' destruct HW as {pat}. rewrite <-W{s}, <-W{t_} in E. exact E. Qed.']
        prim, inv = pinfo[s]
        goal = f'1-read_signal d {prim}%nat' if inv else f'read_signal d {prim}%nat'
        pf = f'pose proof(raw_{s} seed d HL HW) as A.' + (f' pose proof(rawp_{t_} seed d HL HW) as B. lia.' if t_ not in (clk0, rst0) else ' lia.')
        L += [f'Lemma rawp_{s} seed d : CombLFP P seed d -> NetWords d -> read_signal d {s}%nat={goal}.',
              f'Proof. intros HL HW. {pf} Qed.']
    L += ['Lemma pds_eq ev pre : phase_driven_state P ev pre = lfp_candidate P (write_signal pre (changed_signal ev) (new_value ev)).',
          'Proof. Transparent phase_driven_state. reflexivity. Qed.',
          f'Lemma prim_driven ev pre : changed_signal ev = {clk0}%nat -> read_signal(phase_driven_state P ev pre){clk0}%nat=new_value ev /\\ '
          f'read_signal(phase_driven_state P ev pre){rst0}%nat=read_signal pre {rst0}%nat.',
          'Proof. intro Hc. split.',
          f' - rewrite(sampled_input P {clk0}%nat ev pre ltac:(vm_compute;reflexivity)). rewrite Hc. apply read_signal_write_same.',
          f' - rewrite(sampled_input P {rst0}%nat ev pre ltac:(vm_compute;reflexivity)). rewrite read_signal_write_other by (rewrite Hc; discriminate). reflexivity. Qed.',
          f'Lemma words_driven ev pre : changed_signal ev = {clk0}%nat -> Word 1(new_value ev) -> NetWords pre -> NetWords(phase_driven_state P ev pre).',
          'Proof. intros Hc Hn HW. destruct(prim_driven ev pre Hc)as[D0 D1]. unfold NetWords in *.',
          f' destruct HW as {pat}.',
          f' split; [rewrite D0; exact Hn|]. split; [rewrite D1; exact W{rst0}|].']
    for k, s in enumerate(order):
        body = (f'rewrite pds_eq; apply lfp_word; [vm_compute; reflexivity|]; unfold WordRoot; '
                f'rewrite read_signal_write_other by (rewrite Hc; discriminate); exact W{s}')
        L.append(f' {body}.' if k == len(order) - 1 else f' split; [{body}|].')
    L.append('Qed.')

    def sel_lemma(name, old, new):
        exp = expected(procs, clk0, rst0, old, new, RST_IDLE)
        lst = '[' + ';'.join(f'process_{i}' for i in exp) + ']'
        hyps = (f' changed_signal ev = {clk0}%nat -> new_value ev = {new} -> read_signal pre {clk0}%nat = {old} ->'
                f' read_signal pre {rst0}%nat = {RST_IDLE} -> NetWords pre -> CombLFP P seed pre ->'
                f' CombLFP P(write_signal pre(changed_signal ev)(new_value ev))(phase_driven_state P ev pre) ->')
        out = []
        for i, specs in procs:
            hit = i in exp
            rw = ', '.join(f'(rawp_{sig} seed pre HL HW), (rawp_{sig} _ d HD Wd)' for edge, sig, prim, inv in specs if sig not in (clk0, rst0))
            out += [f'Theorem {name}_match_{i} ev pre seed :{hyps}',
                    f' process_matches_states pre(phase_driven_state P ev pre)process_{i}={"true" if hit else "false"}.',
                    'Proof. intros Hc Hv H0 H1 HW HL HD. set(d:=phase_driven_state P ev pre).',
                    ' assert(Wd:NetWords d) by (apply words_driven; [exact Hc|rewrite Hv; vm_compute; reflexivity|exact HW]).',
                    ' destruct(prim_driven ev pre Hc)as[D0 D1]. rewrite Hv in D0. rewrite H1 in D1. fold d in D0, D1.',
                    match_certificate(name, i, specs, clk0, dict(c=(old,new), r=(RST_IDLE,RST_IDLE)), rw,
                                      'rewrite ?H0, ?D0, ?H1, ?D1; reflexivity.')]
        out += [f'Theorem {name} ev pre seed :{hyps}',
                f' selected_on_transition P pre(phase_driven_state P ev pre)={lst}.',
                'Proof. intros Hc Hv H0 H1 HW HL HD.',
                ' unfold selected_on_transition. rewrite(filter_refine(process_matches_states pre(phase_driven_state P ev pre)) is_seqb(processes P) (matches_seq pre(phase_driven_state P ev pre))).',
                ' assert(Hseq:filter is_seqb(processes P)=[' + ';'.join(f'process_{i}' for i, _ in procs) + ']) by (vm_compute; reflexivity).',
                ' rewrite Hseq. cbn[filter].']
        if FAST_FILTER:
            bs = ';'.join('true' if i in exp else 'false' for i, _ in procs)
            rws = ' '.join(f'refine(f_equal2 cons({name}_match_{i} ev pre seed Hc Hv H0 H1 HW HL HD) _);' for i, _ in procs) + ' reflexivity'
            out = out[:-1] + [' rewrite Hseq. rewrite(filter_by(process_matches_states pre(phase_driven_state P ev pre))[' + ';'.join(f'process_{i}' for i, _ in procs) + '] [' + bs + '] ltac:(cbn[map]; ' + rws + ')).',
                              ' cbv[map fst snd filter combine]. reflexivity. Qed.']
            return out
        for i, specs in procs:
            out.append(f' rewrite({name}_match_{i} ev pre seed Hc Hv H0 H1 HW HL HD).')
        out.append(' reflexivity. Qed.')
        return out
    L += sel_lemma('sel_rise', 0, 1) + sel_lemma('sel_fall', 1, 0)
    exp_r = expected(procs, clk0, rst0, 0, 1, RST_IDLE)
    exp_f = expected(procs, clk0, rst0, 1, 0, RST_IDLE)
    return L, ['sel_rise', 'sel_fall'], dict(rise=exp_r, fall=exp_f, nets=order)


HDR = r"""(** Narrow LLM provenance: event-certificate consumption added by Codex, 2026-11-09.
    Concrete net observations remain design-specific certificate data. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVCheckedAssignmentBinding Lang.ExtendedSVWordInvariant Lang.ExtendedSVStallFlush
 Lang.ExtendedSVBankAlignment Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVEventMatchCertificate @AST@.
Import ListNotations ExtendedSV ExtendedSVCheckedAssignmentBinding ExtendedSVWordInvariant ExtendedSVStallFlush ExtendedSVBankAlignment
 ExtendedSVEmptyPipeline ExtendedSVEventMatchCertificate @OPEN@.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics phase_driven_state.
"""


def build(design, module):
    ast, pr, tr = roles.load_all(design)
    L, ex, info = text(design, module)
    prog = pr['ast']['program']
    pmod = prog.split('.')[0]
    hdr = HDR.replace('@AST@', pr['ast']['module']).replace('@OPEN@', pmod)
    body = (f'(** {design}: edge layer (derived clock/reset nets, selected sequential processes), generated by tools/cpu_tmpl_edge.py.\n'
            f'    proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + hdr +
            f'Module {module}.\nNotation P := {prog.split(".")[-1]} (only parsing).\n' + '\n'.join(L) + f'\nEnd {module}.\n')
    body += ''.join(f'Print Assumptions {module}.{e}.\n' for e in ex)
    return body, [f'{module}.{e}' for e in ex], info


def glue_text(design, module, edge_mod, rf_mod, variant):
    """RF step lemmas at the primary falling edge with the selection hypothesis discharged by sel_fall."""
    import cpu_tmpl_rf as rfg
    ast, pr, tr = roles.load_all(design)
    c = rfg.cfg(design, variant)
    sh, bank, reg = c['sh'], c['bank'], c['sh']['reg']
    cc, g, e = T.coq(sh['c']), T.coq(sh['g']), T.coq(sh['e'])
    clk0, rst0, net, chain, procs = nets(ast, pr)
    rfp = int(pr['rf_write']['process'].split('_')[1])
    assert rfp in expected(procs, clk0, rst0, 1, 0, RST_IDLE), 'the RF process does not fire on the falling edge of the primary clock'
    prog = pr['ast']['program']
    pmod = prog.split('.')[0]
    hdr = HDR.replace('@AST@', pr['ast']['module'] + ' ' + edge_mod.rsplit('.', 1)[0] + ' ' + rf_mod.rsplit('.', 1)[0]).replace('@OPEN@', pmod)
    en, rn = edge_mod, rf_mod
    D = '(phase_driven_state P ev pre)'
    pre_hyps = (f'changed_signal ev = {clk0}%nat -> new_value ev = 0 -> read_signal pre {clk0}%nat = 1 -> read_signal pre {rst0}%nat = {RST_IDLE} ->'
                f' {en}.NetWords pre -> CombLFP P seed pre -> CombLFP P(write_signal pre(changed_signal ev)(new_value ev)){D} ->')
    args = 'Hc Hv H0 H1 HW HL HD'
    side = f'(rf_bank_not_event ev Hc) (rf_matches_fall ev pre seed {args})'
    new_bank = f'(read_signal (PhaseSemantics P ev pre) {bank}%nat)'
    L = [f'Notation P := {prog.split(".")[-1]} (only parsing).',
         f'Theorem rf_matches_fall ev pre seed : {pre_hyps}',
         f' process_matches_states pre{D}process_{rfp}=true.',
         f'Proof. intros {args}. exact({en}.sel_fall_match_{rfp} ev pre seed {args}). Qed.',
         f'Theorem rf_bank_not_event ev : changed_signal ev = {clk0}%nat -> changed_signal ev <> {bank}%nat. Proof. intro H; rewrite H; discriminate. Qed.',
         f'Theorem rf_rel_step_fall ev pre seed view : {pre_hyps}',
         f' eval_expr {D} {cc} <> 0 -> eval_expr {D} {g} <> 0 -> RFRel (read_signal pre {bank}%nat) view ->',
         f' RFRel {new_bank} (fun i => if Z.eqb i (norm 5 (read_signal {D} {reg}%nat)) then norm 32 (eval_expr {D} {e}) else view i).',
         f'Proof. intros {args} Hc1 Hg HR. exact({rn}.rf_rel_step ev pre view {side} Hc1 Hg HR). Qed.',
         f'Theorem rf_rel_off_fall ev pre seed view : {pre_hyps}',
         f' eval_expr {D} {cc} <> 0 -> eval_expr {D} {g} = 0 -> RFRel (read_signal pre {bank}%nat) view -> RFRel {new_bank} view.',
         f'Proof. intros {args} Hc1 Hg HR. exact({rn}.rf_rel_off ev pre view {side} Hc1 Hg HR). Qed.',
         f'Theorem rf_rel_reset_fall ev pre seed : {pre_hyps}',
         f' eval_expr {D} {cc} = 0 -> RFRel {new_bank} (fun _ => 0).',
         f'Proof. intros {args} Hc1. exact({rn}.rf_rel_reset ev pre {side} Hc1). Qed.']
    ex = ['rf_matches_fall', 'rf_bank_not_event', 'rf_rel_step_fall', 'rf_rel_off_fall', 'rf_rel_reset_fall']
    body = (f'(** {design}: RF write step at the primary falling edge, generated by tools/cpu_tmpl_edge.py --glue.\n'
            f'    proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + hdr +
            'Require Import Lang.ExtendedSVBankOperand.\nImport ExtendedSVBankOperand.\n' + f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\n')
    body += ''.join(f'Print Assumptions {module}.{x}.\n' for x in ex)
    return body, [f'{module}.{x}' for x in ex]


def assigned_roots(s):
    if s[0] == 'SAssign':
        lv = s[3]
        while lv[0] == 'LSel':
            lv = lv[2]
        return {lv[2]}
    if s[0] == 'SSeq':
        return set().union(*[assigned_roots(c) for c in s[1]]) if s[1] else set()
    if s[0] == 'SIf':
        return assigned_roots(s[2]) | assigned_roots(s[3])
    if s[0] == 'SCase':
        return set().union(*[assigned_roots(a[1]) for a in s[2]]) if s[2] else set()
    return set()


def discover_pipelined(design):
    """Template roles of a clocked-through-nets pipeline (additive manifest section `template_roles` of bzeeno.json)."""
    ast, pr, _ = roles.load_all(design)
    clk0, rst0, net, chain, procs = nets(ast, pr)

    def row(i):
        r = ast.sig[i]
        return {'id': i, 'width': r['width'], 'path': r['path']}
    seq = []
    for i, specs in procs:
        written = sorted(assigned_roots(ast.procs[i]['body']))
        seq.append({'process': f'process_{i}', 'events': [{'edge': e, 'signal': row(s), 'primary': row(pr_), 'inverted': bool(iv)}
                                                         for e, s, pr_, iv in specs],
                    'writes': [row(w) for w in written]})
    return {
        'kind': 'pipelined_derived_clock',
        'primary_clock': row(clk0), 'primary_reset': row(rst0),
        'sequential_processes': seq,
        'fires_on_rise': [f'process_{i}' for i in expected(procs, clk0, rst0, 0, 1, RST_IDLE)],
        'fires_on_fall': [f'process_{i}' for i in expected(procs, clk0, rst0, 1, 0, RST_IDLE)],
        'rf_write_edge': 'fall' if int(pr['rf_write']['process'].split('_')[1]) in expected(procs, clk0, rst0, 1, 0, RST_IDLE) else 'rise',
        'provenance': {'source': 'discovered', 'rule': 'sequential process event specs (Posedge clk, Negedge resetn); clock/reset nets traced '
                       'through copy/not comb wires to the primary inputs (tools/cpu_tmpl_edge.py nets); fire lists computed by simulating the polarities'}}


def write_roles(design):
    path = roles.PROFILE / (design + '.json')
    prof = json.loads(path.read_text())
    prof['template_roles'] = discover_pipelined(design)
    path.write_text(json.dumps(prof, indent=1) + '\n')
    return path


# ---------------------------------------------------------------------------------------------------------------------------
# Reset layer (option --reset-events, additive): events on the primary reset, and clock events with reset = 0.
# Scenario = (what changes, clock old/new, reset old/new).  The selection lists are computed by simulating the polarities.
# 'boot' is the first boot event applied to the raw seed state: it is not a comb fixed point, every derived net reads 0 before
# the event, so the old value of a net is 0 instead of the polarity of its primary.
SCEN = {
    'rise0': dict(kind='clk', c=(0, 1), r=(0, 0)),
    'fall0': dict(kind='clk', c=(1, 0), r=(0, 0)),
    'rassert0': dict(kind='rst', c=(0, 0), r=(1, 0)),
    'rassert1': dict(kind='rst', c=(1, 1), r=(1, 0)),
    'rrelease0': dict(kind='rst', c=(0, 0), r=(0, 1)),
    'rrelease1': dict(kind='rst', c=(1, 1), r=(0, 1)),
    'bootassert': dict(kind='rst', c=(0, 0), r=(1, 0), zero_pre=True),
}


def expected_scen(procs, clk0, rst0, sc):
    sel = []
    (c0, c1), (r0, r1) = sc['c'], sc['r']
    for i, specs in procs:
        hit = False
        for edge, sig, prim, inv in specs:
            if prim == clk0:
                o, n = (c0 ^ inv, c1 ^ inv)
            else:
                o, n = (r0 ^ inv, r1 ^ inv)
            if sc.get('zero_pre') and sig not in (clk0, rst0):
                o = 0
            hit |= fires(edge, o, n)
        if hit:
            sel.append(i)
    return sel


def net_order(ast, pr):
    """the derived nets in dependency order (same order as the edge layer)"""
    clk0, rst0, net, chain, procs = nets(ast, pr)
    allw = sorted({s for p in chain.values() for s in p})
    order = []

    def visit(s):
        if s in (clk0, rst0) or s in order:
            return
        c = ast.comb[s]['rhs']
        visit(c[2] if c[0] == 'EVar' else c[3][2])
        order.append(s)
    for s in allw:
        visit(s)
    return order


def scen_hyps(sc, clk0, rst0, E, nz='NetsZero'):
    changed = clk0 if sc['kind'] == 'clk' else rst0
    newv = sc['c'][1] if sc['kind'] == 'clk' else sc['r'][1]
    h = (f' changed_signal ev = {changed}%nat -> new_value ev = {newv} -> read_signal pre {clk0}%nat = {sc["c"][0]} ->'
         f' read_signal pre {rst0}%nat = {sc["r"][0]} ->')
    if sc.get('zero_pre'):
        h += f' {nz} pre -> {E}.NetWords pre ->'
    else:
        h += f' {E}.NetWords pre -> CombLFP P seed pre ->'
    h += ' CombLFP P(write_signal pre(changed_signal ev)(new_value ev))(phase_driven_state P ev pre) ->'
    return h


def scen_args(sc):
    return 'Hc Hv H0 H1 HZ HW HD' if sc.get('zero_pre') else 'Hc Hv H0 H1 HW HL HD'


def reset_text(design, module, edge_mod):
    ast, pr, tr = roles.load_all(design)
    clk0, rst0, net, chain, procs = nets(ast, pr)
    order = net_order(ast, pr)
    allsig = [clk0, rst0] + order
    E = 'E'
    prog = pr['ast']['program']
    pmod = prog.split('.')[0]
    hdr = HDR.replace('@AST@', pr['ast']['module'] + ' ' + edge_mod.rsplit('.', 1)[0]).replace('@OPEN@', pmod)
    pat = '(' + ' & '.join(f'W{x}' for x in allsig) + ')'
    L = [f'Notation P := {prog.split(".")[-1]} (only parsing).', f'Module E := {edge_mod}.',
         f'Definition NetsZero (s:State):Prop:=' + ' /\\ '.join(f'read_signal s {x}%nat=0' for x in order) + '.',
         f'Lemma prim_driven_rst ev pre : changed_signal ev = {rst0}%nat -> read_signal(phase_driven_state P ev pre){rst0}%nat=new_value ev /\\ '
         f'read_signal(phase_driven_state P ev pre){clk0}%nat=read_signal pre {clk0}%nat.',
         'Proof. intro Hc. split.',
         f' - rewrite(sampled_input P {rst0}%nat ev pre ltac:(vm_compute;reflexivity)). rewrite Hc. apply read_signal_write_same.',
         f' - rewrite(sampled_input P {clk0}%nat ev pre ltac:(vm_compute;reflexivity)). rewrite read_signal_write_other by (rewrite Hc; discriminate). reflexivity. Qed.',
         f'Lemma words_driven_rst ev pre : changed_signal ev = {rst0}%nat -> Word 1(new_value ev) -> E.NetWords pre -> E.NetWords(phase_driven_state P ev pre).',
         'Proof. intros Hc Hn HW. destruct(prim_driven_rst ev pre Hc)as[D1 D0]. unfold E.NetWords in *.',
         f' destruct HW as {pat}.',
         f' split; [rewrite D0; exact W{clk0}|]. split; [rewrite D1; exact Hn|].']
    for k, s in enumerate(order):
        body = (f'rewrite E.pds_eq; apply lfp_word; [vm_compute; reflexivity|]; unfold WordRoot; '
                f'rewrite read_signal_write_other by (rewrite Hc; discriminate); exact W{s}')
        L.append(f' {body}.' if k == len(order) - 1 else f' split; [{body}|].')
    L.append('Qed.')
    info = {}
    exports = []
    for name, sc in SCEN.items():
        exp = expected_scen(procs, clk0, rst0, sc)
        info[name] = exp
        lst = '[' + ';'.join(f'process_{i}' for i in exp) + ']'
        hyps = scen_hyps(sc, clk0, rst0, E)
        args = scen_args(sc)
        zero = sc.get('zero_pre')
        driven_words = ('words_driven_rst ev pre Hc ltac:(rewrite Hv; vm_compute; reflexivity) HW' if sc['kind'] == 'rst'
                        else f'E.words_driven ev pre Hc ltac:(rewrite Hv; vm_compute; reflexivity) HW')
        prim = 'prim_driven_rst' if sc['kind'] == 'rst' else 'E.prim_driven'
        for i, specs in procs:
            hit = i in exp
            ns = [sig for edge, sig, pm, inv in specs if sig not in (clk0, rst0)]
            if zero:
                rw = ', '.join(f'(Z{sig}), (E.rawp_{sig} _ d HD Wd)' for sig in ns)
                pre_destruct = (f' rename HZ into Z{order[0]}.' if len(order) == 1 else
                                ' destruct HZ as ' + '(' + ' & '.join(f'Z{x}' for x in order) + ').')   # additive: one derived net (NERV)
            else:
                rw = ', '.join(f'(E.rawp_{sig} seed pre HL HW), (E.rawp_{sig} _ d HD Wd)' for sig in ns)
                pre_destruct = ''
            if sc['kind'] == 'rst':
                dd = ' destruct(prim_driven_rst ev pre Hc)as[D1 D0]. rewrite Hv in D1. rewrite H0 in D0. fold d in D0, D1.'
                rwend = 'rewrite ?H0, ?H1, ?D0, ?D1; reflexivity.'
            else:
                dd = ' destruct(E.prim_driven ev pre Hc)as[D0 D1]. rewrite Hv in D0. rewrite H1 in D1. fold d in D0, D1.'
                rwend = 'rewrite ?H0, ?D0, ?H1, ?D1; reflexivity.'
            L += [f'Theorem {name}_match_{i} ev pre{"" if zero else " seed"} :{hyps}',
                  f' process_matches_states pre(phase_driven_state P ev pre)process_{i}={"true" if hit else "false"}.',
                  f'Proof. intros {args}. set(d:=phase_driven_state P ev pre).',
                  f' assert(Wd:E.NetWords d) by (apply {driven_words.split(" ",1)[0]}; [exact Hc|rewrite Hv; vm_compute; reflexivity|exact HW]).',
                  dd + pre_destruct,
                  match_certificate(name, i, specs, clk0, dict(sc, primary_signals=(clk0,rst0)), rw, rwend)]
            exports.append(f'{name}_match_{i}')
        sig_seed = '' if zero else ' seed'
        L += [f'Theorem sel_{name} ev pre{sig_seed} :{hyps}',
              f' selected_on_transition P pre(phase_driven_state P ev pre)={lst}.',
              f'Proof. intros {args}.',
              ' unfold selected_on_transition. rewrite(E.filter_refine(process_matches_states pre(phase_driven_state P ev pre)) E.is_seqb(processes P) (E.matches_seq pre(phase_driven_state P ev pre))).',
              ' assert(Hseq:filter E.is_seqb(processes P)=[' + ';'.join(f'process_{i}' for i, _ in procs) + ']) by (vm_compute; reflexivity).',
              ' rewrite Hseq. cbn[filter].']
        for i, specs in procs:
            L.append(f' rewrite({name}_match_{i} ev pre{sig_seed} {args}).')
        L.append(' reflexivity. Qed.')
        exports.append(f'sel_{name}')
    body = (f'(** {design}: reset layer of the edge generator (events on the primary reset, clock events with reset 0), generated by tools/cpu_tmpl_edge.py --reset-events.\n'
            f'    proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + hdr +
            f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\n')
    body += ''.join(f'Print Assumptions {module}.sel_{n}.\n' for n in SCEN)
    return body, [f'{module}.sel_{n}' for n in SCEN], dict(selected={k: v for k, v in info.items()}, lemmas=len(exports))


if __name__ == '__main__':
    import argparse
    import cpu_tmpl_accept as acc
    ap = argparse.ArgumentParser()
    ap.add_argument('--fast-filter', action='store_true')
    ap.add_argument('--design', default='bzeeno')
    ap.add_argument('--module', default='BzTmplEdge')
    ap.add_argument('--namespace')
    ap.add_argument('--out', required=True)
    ap.add_argument('--accept', action='store_true')
    ap.add_argument('--provider', action='append', default=[])
    ap.add_argument('--glue', nargs=2, metavar=('EDGE_MODULE', 'RF_MODULE'), help='emit the RF-at-falling-edge glue module (fully qualified provider module names)')
    ap.add_argument('--variant', default='bzeeno-configured')
    ap.add_argument('--reset-events', metavar='EDGE_MODULE', help='emit the reset layer (events on the primary reset, clock events with reset 0); argument = fully qualified edge module')
    ap.add_argument('--write-roles', action='store_true', help='write template_roles into the design manifest (no Coq output)')
    a = ap.parse_args()
    FAST_FILTER = a.fast_filter
    if a.write_roles:
        print(write_roles(a.design)); sys.exit(0)
    if a.reset_events:
        body, exports, info = reset_text(a.design, a.module, a.reset_events)
    elif a.glue:
        body, exports = glue_text(a.design, a.module, a.glue[0], a.glue[1], a.variant)
        info = dict(glue=a.glue)
    else:
        body, exports, info = build(a.design, a.module)
    if not a.accept:
        Path(a.out).write_text(body)
        print(a.out, len(body.splitlines()), 'lines', info)
        sys.exit(0)
    prof = json.loads(Path(f'framework/auto-contract-profiles/{a.design}.json').read_text())
    lp = [(prof['pipeline_roles']['ast']['file'].rsplit('/', 1)[0], prof['pipeline_roles']['ast']['module'].split('.')[0])]
    prov = [dict(namespace=x.split('=')[0], directory=str(Path(x.split('=')[1]).resolve())) for x in a.provider]
    r = acc.accept(a.out, a.namespace, a.module, body, exports, lp, providers=prov,
                   extra=dict(generator='tools/cpu_tmpl_edge.py', design=a.design, info=info))
    print(json.dumps(r, indent=1))
    sys.exit(0 if r['accepted'] else 1)
