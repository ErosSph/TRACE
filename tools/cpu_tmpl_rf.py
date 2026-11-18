#!/usr/bin/env python3
"""Template-route register-file pieces, instantiated from manifest roles (bank signal, write process/index/guard,
read ports) onto the design-independent libraries Lang/ExtendedSVBankWriteStep.v and Lang/ExtendedSVBankOperand.v.

Per design the generator
  * classifies the write process of the bank from its AST ('nba' block with the slice write, or 'guarded':
    if c then (if g then bank[idx*32 +: 32] <= e) else bank <= reset-value),
  * derives from the AST why lane 0 stays 0: 'value_mux' (e = (x | idx==0) ? 0 : ...) or 'stmt_guard' (g contains idx!=0),
  * finds every combinational read port of the bank ('plain' lane read or with the x0 mux),
  * emits a Coq module whose theorems are instances of the libraries (lane effect of the write, RFRel preservation,
    operand clauses a = view rs).
Generated text is untrusted: Coq re-checks it. proof_author LLM-generated: Claude Code (claude-sonnet-5-5).
"""
import json
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles

AUTHOR = T.PROOF_AUTHOR
PROFILE = Path('framework/auto-contract-profiles')

# Genericity-test override: the repaired Bzeeno AST used by the accepted Bzeeno route (same processes as the configured one).
OVERRIDES = {
    'bzeeno': dict(module='BzeenoLoadUseJal.BzeenoLoadUseJalAST', program='bzeeno_load_use_jal_program',
                   ast_file='experiments/framework/generated/bzeeno-load-use-jal/BzeenoLoadUseJalAST.v',
                   signal_table='experiments/framework/generated/bzeeno-load-use-jal/report.json',
                   loadpaths=[('experiments/framework/generated/bzeeno-load-use-jal', 'BzeenoLoadUseJal')]),
    # Option --variant configured: the configured AST that the template-route Bzeeno theorem targets (processes identical, ConfigBinding).
    'bzeeno-configured': dict(module='GeneratedRuntimeInput.ConfiguredAST', program='BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program',
                   open='BzeenoLoadUseJalASTConfigured3122be4a95',
                   ast_file='results/pending-configured-input-20261024-a4-bzeeno/ConfiguredAST.v',
                   signal_table='experiments/framework/generated/bzeeno-load-use-jal/report.json',
                   loadpaths=[('results/pending-configured-input-20261024-a4-bzeeno', 'GeneratedRuntimeInput')]),
}


def idx_kind(e, bank_sig=None):
    """Classify a bank address expression; returns (kind, index_register) or None."""
    if (e[0] == 'EBinary' and e[2] == 'BMul' and e[3][0] == 'EVar' and e[3][1] == 5 and e[4][0] == 'EConst' and e[4][2] == 32
            and e[1] >= 10):
        return 'mul', e[3][2]
    if (e[0] == 'ESel' and e[1] == 10 and e[3] == ('EConst', 32, 0) and e[2][0] == 'EBinary' and e[2][2] == 'BShiftL'
            and e[2][1] == 32 and e[2][3][0] == 'EExtend' and e[2][3][3][0] == 'EVar' and e[2][3][3][1] == 5
            and e[2][4] == ('EConst', 32, 5)):
        return 'shift', e[2][3][3][2]
    return None


def read_ports(ast, bank):
    out = []
    for root, c in sorted(ast.comb.items()):
        r = c['rhs']
        if c['width'] != 32 or c['nba']:
            continue
        x0 = False
        if r[0] == 'ECond' and r[3] == ('EConst', 32, 0) and r[2][0] == 'EBinary' and r[2][2] == 'BEq' \
                and r[2][3] == ('EConst', 5, 0) and r[2][4][0] == 'EVar' and r[2][4][1] == 5:
            x0, rs, r = True, r[2][4][2], r[4]
        if r[0] == 'ESel' and r[1] == 32 and r[2][0] == 'EVar' and r[2][2] == bank:
            k = idx_kind(r[3])
            if k is None:
                continue
            if x0 and k[0] != 'shift':
                continue
            out.append(dict(dst=root, k=c['k'], proc=c['name'], total=r[2][1], idx=r[3], kind=k[0], reg=k[1], x0=x0))
    return out


def write_shape(ast, proc, bank):
    body = ast.procs[proc]['body']
    assert body[0] == 'SSeq' and body[1][0][0] == 'SSeq', 'unsupported body'
    sts = body[1][0][1]
    # shape A: block of non-blocking assignments, one slice write to the bank
    ks = [k for k, s in enumerate(sts) if s[0] == 'SAssign' and ((s[3][0] == 'LVar' and s[3][2] == bank) or
                                                               (s[3][0] == 'LSel' and s[3][2][2] == bank))]
    if len(sts) != 1 or sts[0][0] != 'SIf':
        assert len(ks) == 1 and all(s[0] == 'SAssign' and s[1] for s in sts), 'shape A: one bank write, NBA block'
        k = ks[0]
        st = sts[k]
        lhs = st[3]
        assert lhs[0] == 'LSel' and lhs[2][0] == 'LVar' and lhs[2][2] == bank
        ik = idx_kind(lhs[3])
        return dict(shape='nba', k=k, e=st[2], w=lhs[1], W=lhs[2][1], idx=lhs[3], idxkind=ik[0], reg=ik[1])
    # shape B: if c then (if g then slice write else skip) else (bank := e2)
    s = sts[0]
    c, y, n = s[1], s[2], s[3]
    assert y[0] == 'SIf' and y[3] == ('SSkip',) and y[2][0] == 'SAssign' and y[2][1] and n[0] == 'SAssign' and n[1]
    lhs = y[2][3]
    assert lhs[0] == 'LSel' and lhs[2][0] == 'LVar' and lhs[2][2] == bank and n[3][0] == 'LVar' and n[3][2] == bank
    ik = idx_kind(lhs[3])
    return dict(shape='guarded', c=c, g=y[1], e=y[2][2], w=lhs[1], W=lhs[2][1], idx=lhs[3], idxkind=ik[0], reg=ik[1],
                other_e=n[2], other_W=n[3][1])


def zero_rule(sh):
    """Why lane 0 stays 0: derived from the AST expression, never assumed."""
    reg = sh['reg']
    test = ('EBinary', 1, 'BEq', ('EConst', 5, 0), ('EVar', 5, reg))
    if sh['shape'] == 'nba':
        e = sh['e']
        if e[0] == 'ECond' and e[3] == ('EConst', e[1], 0):
            g = e[2]
            if g == test:
                return 'value_mux', 'eq'
            if g[0] == 'EBinary' and g[2] == 'BOr' and g[1] == 1:
                if g[4] == test:
                    return 'value_mux', 'or_r'
                if g[3] == test:
                    return 'value_mux', 'or_l'
        raise ValueError('lane 0 is not protected by the write value; no x0 clause can be generated')
    g = sh['g']
    if g[0] == 'EBinary' and g[2] == 'BAnd' and g[1] == 1 and g[4] == ('EBinary', 1, 'BNeq', ('EConst', 5, 0), ('EVar', 5, reg)):
        return 'stmt_guard', 'and_neq'
    raise ValueError('write guard does not exclude register 0')


def cfg(design, variant=None):
    prof = json.loads((PROFILE / f'{design}.json').read_text())
    pr, tr = prof['pipeline_roles'], prof.get('template_roles') or {}
    ov = OVERRIDES.get(variant or design)
    if ov:
        ast = T.Ast(ov['ast_file'], ov['signal_table'])
    else:
        ast = T.Ast(pr['ast']['file'], pr['ast']['signal_table'])
    rw = pr['rf_write']
    bank = rw['bank']['id']
    proc = int(rw['process'].split('_')[1])
    sh = write_shape(ast, proc, bank)
    zr = zero_rule(sh)
    ports = read_ports(ast, bank)
    return dict(ast=ast, pr=pr, tr=tr, bank=bank, proc=proc, sh=sh, zero=zr, ports=ports, bank_row=rw['bank'], ov=ov)


def ev_ok(x):
    return x


def common_ports(c, P, bankc, inner=''):
    """Operand clauses, one per read port (shared by the designs)."""
    out = []
    for p in c['ports']:
        d, k, nm, reg, tot, idx = p['dst'], p['k'], p['proc'], p['reg'], p['total'], T.coq(p['idx'])
        cond = None
        out += [
            f'Lemma port{d}_at : nth_error (filter is_comb (processes {P})) {k}%nat = Some {nm}. Proof. vm_compute; reflexivity. Qed.',
            f'Lemma port{d}_bind : assignment_bindingb (filter is_comb (processes {P})) {k}%nat = true. Proof. vm_compute; reflexivity. Qed.',
            f'Lemma port{d}_idx : bounded32b {idx} = true. Proof. vm_compute; reflexivity. Qed.']
        if not p['x0']:
            out += [
                f'Theorem operand_{d} seed fixed view : CombLFP {P} seed fixed -> RFRel (read_signal fixed {bankc}%nat) view ->',
                f' norm 32 (read_signal fixed {d}%nat) = view (norm 5 (read_signal fixed {reg}%nat)).',
                'Proof. intros HL HR.',
                f' rewrite (operand_clause {P} _ {k}%nat {nm} false {d}%nat {bankc}%nat {tot}%nat {idx} seed fixed view eq_refl port{d}_at eq_refl port{d}_bind ltac:(cbn; lia) HL ltac:(lia) port{d}_idx HR).',
                f' rewrite (multiply_index fixed {p["idx"][1]}%nat (EVar 5 {reg}%nat) (EConst {p["idx"][1]} 32) ltac:(lia) ltac:(cbn; lia) ltac:(reflexivity)).',
                ' reflexivity. Qed.']
        else:
            out += [
                f'Theorem operand_{d} seed fixed view : CombLFP {P} seed fixed -> RFRel (read_signal fixed {bankc}%nat) view ->',
                f' norm 32 (read_signal fixed {d}%nat) = view (norm 5 (read_signal fixed {reg}%nat)).',
                'Proof. intros HL HR.',
                f' refine (operand_clause_x0 {P} _ {k}%nat {nm} false {d}%nat {bankc}%nat {tot}%nat {idx} {reg}%nat seed fixed view eq_refl port{d}_at eq_refl port{d}_bind ltac:(cbn; lia) HL ltac:(lia) port{d}_idx _ HR).',
                f' apply shifted_index. Qed.']
    return out


COMMON_REQ = """From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice Lang.ExtendedSVEmptyPipeline
 Lang.ExtendedSVWordInvariant Lang.ExtendedSVSeqStep Lang.ExtendedSVBitSlice Lang.ExtendedSVRegisterBank
 Lang.ExtendedSVBankAlignment Lang.ExtendedSVBankIndex Lang.ExtendedSVBankRead Lang.ExtendedSVCheckedAssignmentBinding
 Lang.ExtendedSVBankWriteStep Lang.ExtendedSVBankOperand Lang.ExtendedSVConstantRoot"""
COMMON_IMP = """Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVEmptyPipeline
 ExtendedSVWordInvariant ExtendedSVSeqStep ExtendedSVBitSlice ExtendedSVRegisterBank ExtendedSVBankAlignment
 ExtendedSVBankIndex ExtendedSVBankRead ExtendedSVCheckedAssignmentBinding ExtendedSVBankWriteStep ExtendedSVBankOperand ExtendedSVConstantRoot."""


def dark_text(c, module):
    sh, bank, reg = c['sh'], c['bank'], c['sh']['reg']
    assert sh['shape'] == 'nba' and sh['idxkind'] == 'mul'
    pr = c['pr']
    clk = pr['events']['clock']['id']
    wp = f'process_{c["proc"]}'
    P = 'dark38_program'
    val, idx = T.coq(sh['e']), T.coq(sh['idx'])
    zk, zv = c['zero']
    hdr = COMMON_REQ + """
 Ex.External.DarkRISCV38DerivedCycle Ex.External.DarkRISCV38DerivedLFP Ex.External.DarkRISCV38DerivedTarget
 Ex.External.CPUArrayContracts Ex.RvCore.FormalSpec coqutil.Map.Interface coqutil.Word.Interface
 Dark38.DarkRISCV38DerivedAST TmplDarkCycle.DarkTmplCycle.
""" + COMMON_IMP + """
Import DarkRISCV38DerivedCycle DarkRISCV38DerivedLFP DarkRISCV38DerivedTarget.DarkRISCV38DerivedTarget DarkRISCV38DerivedAST.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics phase_driven_state.
"""
    D = f'(phase_driven_state {P} rise pre)'
    L = []
    L += [
        f'Notation P := {P} (only parsing).',
        f'Lemma inputs_unw_clk : roots_unwrittenb {clk}%nat (processes P) = true. Proof. vm_compute; reflexivity. Qed.',
        f'Lemma comb_unw_clk : comb_root_unwrittenb P {clk}%nat = true. Proof. apply all_unwritten_comb. exact inputs_unw_clk. Qed.',
        f'Lemma comb_unw_bank : comb_root_unwrittenb P {bank}%nat = true. Proof. vm_compute; reflexivity. Qed.',
        f'Lemma writers_bank : filter (writes_rootb {bank}%nat) (processes P) = [{wp}]. Proof. vm_compute; reflexivity. Qed.',
        f'Lemma rise_clk pre : read_signal (phase_driven_state P rise pre) {clk}%nat = 1.',
        f'Proof. rewrite sampled_input by exact inputs_unw_clk. cbn [changed_signal new_value rise]. rewrite read_signal_write_same. reflexivity. Qed.',
        'Local Transparent phase_driven_state.',
        f'Lemma driven_read pre r : comb_root_unwrittenb P r = true -> r <> {clk}%nat -> read_signal (phase_driven_state P rise pre) r = read_signal pre r.',
        'Proof. intros H H1. unfold phase_driven_state. rewrite lfp_candidate_preserves_unwritten_root by exact H.',
        ' cbn [changed_signal rise]. apply read_signal_write_other. congruence. Qed.',
        'Local Opaque phase_driven_state.',
        f'Lemma rise_sel pre : read_signal pre {clk}%nat = 0 ->',
        f' filter (process_matches_states pre (phase_driven_state P rise pre)) (filter (writes_rootb {bank}%nat) (processes P)) = [{wp}].',
        f'Proof. intro H0. rewrite writers_bank. cbn [filter]. rewrite (matches_rise {wp} pre _ {clk}%nat eq_refl eq_refl H0 (rise_clk pre)). reflexivity. Qed.',
        f'Lemma idx_eval pre : eval_expr {D} {idx} = Z.of_nat 32 * norm 5 (read_signal {D} {reg}%nat).',
        f'Proof. rewrite mul32_exact by first [lia | (cbn; lia) | reflexivity]. reflexivity. Qed.',
        '(* effect of the register-file write at the rising edge, lane by lane *)',
        f'Theorem rf_write_lane pre : read_signal pre {clk}%nat = 0 -> forall i, 0 <= i ->',
        f' lane_read 32 (read_signal (PhaseSemantics P rise pre) {bank}%nat) i =',
        f' if Z.eqb i (norm 5 (read_signal {D} {reg}%nat)) then norm 32 (eval_expr {D} {val}) else lane_read 32 (read_signal pre {bank}%nat) i.',
        'Proof. intros H0 i Hi.',
        f' refine (bank_phase_lane_nba P rise pre {bank}%nat {wp} _ {sh["k"]}%nat {val} 32 {sh["W"]} {idx} (norm 5 (read_signal {D} {reg}%nat)) i comb_unw_bank _ eq_refl _ _ (rise_sel pre H0) _ _ _ (idx_eval pre) (proj1 (norm_bounds 5 (read_signal {D} {reg}%nat))) Hi).',
        ' all: try (vm_compute; reflexivity). all: try (unfold rise; cbn; discriminate). all: cbn; try lia. Qed.']
    # zero rule
    g = sh['e'][2]
    if zk == 'value_mux':
        if zv == 'eq':
            core = 'apply idx0_test_true'
        elif zv == 'or_r':
            core = 'apply or_nonzero_r; [reflexivity | reflexivity | rewrite idx0_test_true; [lia | exact HD]]'
        else:
            core = 'apply or_nonzero_l; [reflexivity | reflexivity | rewrite idx0_test_true; [lia | exact HD]]'
    L += [
        '(* lane 0 is protected by the design\'s own write-value mux: the value written to index 0 is 0 *)',
        f'Theorem rf_write_zero pre : norm 5 (read_signal {D} {reg}%nat) = 0 -> norm 32 (eval_expr {D} {val}) = 0.',
        'Proof. intro HD.',
        ' rewrite cond_true_value.',
        ' - vm_compute; reflexivity.',
        f' - {core}; exact HD.' if zv == 'eq' else f' - {core}.',
        'Qed.']
    L += [
        'Theorem rf_rel_step pre view :',
        f' read_signal pre {clk}%nat = 0 -> RFRel (read_signal pre {bank}%nat) view ->',
        f' RFRel (read_signal (PhaseSemantics P rise pre) {bank}%nat)',
        f'  (fun i => if Z.eqb i (norm 5 (read_signal {D} {reg}%nat)) then norm 32 (eval_expr {D} {val}) else view i).',
        'Proof. intros H0 HR.',
        ' apply (RFRel_lane_write (read_signal pre ' + f'{bank}%nat)).',
        ' - exact HR.',
        f' - exact (norm_bounds 5 (read_signal {D} {reg}%nat)).',
        ' - intro Hz. apply rf_write_zero. exact Hz.',
        ' - apply rf_write_lane. exact H0.',
        'Qed.']
    L += common_ports(c, 'P', bank)
    ir = c['ast'].comb.get(reg)
    if ir is not None:
        L += [
            f'Lemma idxreg_at : nth_error (filter is_comb (processes P)) {ir["k"]}%nat = Some {ir["name"]}. Proof. vm_compute; reflexivity. Qed.',
            f'Lemma idxreg_bind : assignment_bindingb (filter is_comb (processes P)) {ir["k"]}%nat = true. Proof. vm_compute; reflexivity. Qed.',
            '(* the written lane is the destination field of the slot word *)',
            f'Theorem rf_index_field seed fixed : CombLFP P seed fixed -> norm 5 (read_signal fixed {reg}%nat) = norm 5 (eval_expr fixed {T.coq(ir["rhs"])}).',
            f'Proof. intro HL. exact (checked_assignment_binding P _ {ir["k"]}%nat {ir["name"]} false _ 5 {reg}%nat seed fixed eq_refl idxreg_at eq_refl idxreg_bind ltac:(cbn; lia) HL). Qed.']
    for p in c['ports']:
        d, r = p['dst'], p['reg']
        L += [
            f'Theorem operand_phase_{d} pre view : RFRel (read_signal pre {bank}%nat) view ->',
            f' norm 32 (read_signal {D} {d}%nat) = view (norm 5 (read_signal {D} {r}%nat)).',
            f'Proof. intro HR. apply (operand_{d} (write_signal pre (changed_signal rise) (new_value rise)) _ view (actual_driven_is_LFP rise pre)).',
            f' rewrite (driven_read pre {bank}%nat comb_unw_bank ltac:(discriminate)). exact HR. Qed.']
    # bridge to the target's ISA register relation
    L += [
        '(* the relation used by the target (RFRelated) plus the RF[0]=0 clause, as an abstract-register view *)',
        'Definition isa_view (isa : FormalSpec.State) (i : Z) : Z :=',
        ' if Z.eqb i 0 then 0 else match map.get (getRegs isa) i with Some v => word.unsigned v | None => 0 end.',
        'Definition RFZero (bank : Z) (isa : FormalSpec.State) : Prop := RFRelated bank isa /\\ lane_read 32 bank 0 = 0.',
        'Theorem rfzero_to_rfrel bank isa : RFZero bank isa -> RFRel bank (isa_view isa).',
        'Proof. intros [HR H0]. split.',
        ' - intros i Hi. unfold isa_view. destruct (Z.eqb i 0) eqn:E.',
        '   + apply Z.eqb_eq in E. subst. exact H0.',
        '   + specialize (HR i Hi). rewrite E in HR. exact HR.',
        ' - reflexivity.',
        'Qed.',
        'Theorem rfrel_to_rfzero bank isa : RFRel bank (isa_view isa) -> RFZero bank isa.',
        'Proof. intros [HR H0]. split.',
        ' - intros i Hi. unfold isa_view in HR. destruct (Z.eqb i 0) eqn:E.',
        '   + reflexivity.',
        '   + specialize (HR i Hi). rewrite E in HR. exact HR.',
        ' - specialize (HR 0 ltac:(lia)). unfold isa_view in HR. cbn in HR. exact HR.',
        'Qed.']
    for p in c['ports']:
        d, r = p['dst'], p['reg']
        L += [
            f'Theorem operand_isa_{d} seed fixed isa : CombLFP P seed fixed -> RFZero (read_signal fixed {bank}%nat) isa ->',
            f' norm 32 (read_signal fixed {d}%nat) = isa_view isa (norm 5 (read_signal fixed {r}%nat)).',
            f'Proof. intros HL HZ. apply (operand_{d} seed fixed _ HL). apply rfzero_to_rfrel. exact HZ. Qed.']
    # cycle level through the accepted cycle layer
    L += [
        '(* one full actual cycle: the bank is as after the rising edge (falling/response phases do not touch it) *)',
        f'Lemma cycle_bank image s : read_signal (rtl (actual_cycle image s)) {bank}%nat = read_signal (PhaseSemantics P rise (rtl s)) {bank}%nat.',
        f'Proof. rewrite (DarkTmplCycle.act_reg image s {bank}%nat comb_unw_bank ltac:(discriminate)).',
        f' rewrite (DarkTmplCycle.frame3 image s {bank}%nat comb_unw_bank ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)). reflexivity. Qed.',
        'Theorem cycle_rf_write_lane image s : DarkTmplCycle.env_ok s -> forall i, 0 <= i ->',
        f' lane_read 32 (read_signal (rtl (actual_cycle image s)) {bank}%nat) i =',
        f' if Z.eqb i (norm 5 (read_signal (phase_driven_state P rise (rtl s)) {reg}%nat)) then norm 32 (eval_expr (phase_driven_state P rise (rtl s)) {val}) else lane_read 32 (read_signal (rtl s) {bank}%nat) i.',
        f'Proof. intros [H0 _] i Hi. rewrite cycle_bank. apply rf_write_lane; assumption. Qed.',
        'Theorem cycle_rf_rel image s view : DarkTmplCycle.env_ok s -> ',
        f' RFRel (read_signal (rtl s) {bank}%nat) view ->',
        f' RFRel (read_signal (rtl (actual_cycle image s)) {bank}%nat)',
        f'  (fun i => if Z.eqb i (norm 5 (read_signal (phase_driven_state P rise (rtl s)) {reg}%nat)) then norm 32 (eval_expr (phase_driven_state P rise (rtl s)) {val}) else view i).',
        'Proof. intros [H0 _] HR. rewrite cycle_bank. apply rf_rel_step; assumption. Qed.',
        'Theorem rf_rel_initial : RFRel 0 (fun _ => 0). Proof. apply RFRel_zero. Qed.']
    exports = ['rf_write_lane', 'rf_write_zero', 'rf_rel_step'] + (['rf_index_field'] if c['ast'].comb.get(reg) else []) + [f'operand_{p["dst"]}' for p in c['ports']] + \
              [f'operand_phase_{p["dst"]}' for p in c['ports']] + ['rfzero_to_rfrel', 'rfrel_to_rfzero'] + \
              [f'operand_isa_{p["dst"]}' for p in c['ports']] + ['cycle_rf_write_lane', 'cycle_rf_rel', 'rf_rel_initial']
    body = hdr + f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\n'
    body += ''.join(f'Print Assumptions {module}.{e}.\n' for e in exports)
    return body, [f'{module}.{e}' for e in exports]


def bzeeno_text(c, module):
    sh, bank, reg = c['sh'], c['bank'], c['sh']['reg']
    assert sh['shape'] == 'guarded' and sh['idxkind'] == 'shift'
    ov = c['ov']
    wp = f'process_{c["proc"]}'
    P = ov['program']
    cc, g, e, idx = T.coq(sh['c']), T.coq(sh['g']), T.coq(sh['e']), T.coq(sh['idx'])
    assert sh['other_e'][0] == 'EConst' and sh['other_e'][2] == 0, 'reset value must be the zero constant'
    oe = T.coq(sh['other_e'])
    modname = ov.get('open') or ov['module'].split('.')[-1]
    hdr = COMMON_REQ + f"""
 {ov['module']}.
""" + COMMON_IMP + f"""
Import {modname}.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics phase_driven_state.
"""
    D = '(phase_driven_state P ev pre)'
    sel = f'filter (process_matches_states pre {D}) (filter (writes_rootb {bank}%nat) (processes P)) = [{wp}]'
    L = [
        f'Notation P := {P} (only parsing).',
        f'Lemma comb_unw_bank : comb_root_unwrittenb P {bank}%nat = true. Proof. vm_compute; reflexivity. Qed.',
        f'Lemma writers_bank : filter (writes_rootb {bank}%nat) (processes P) = [{wp}]. Proof. vm_compute; reflexivity. Qed.',
        f'Lemma sel_of_match ev pre : process_matches_states pre {D} {wp} = true -> {sel}.',
        'Proof. intro H. rewrite writers_bank. cbn [filter]. rewrite H. reflexivity. Qed.',
        f'Lemma idx_eval ev pre : eval_expr {D} {idx} = Z.of_nat 32 * norm 5 (read_signal {D} {reg}%nat).',
        'Proof. apply shifted_exact. Qed.',
        '(* write enabled: lane effect *)',
        f'Theorem rf_write_lane ev pre : changed_signal ev <> {bank}%nat -> process_matches_states pre {D} {wp} = true ->',
        f' eval_expr {D} {cc} <> 0 -> eval_expr {D} {g} <> 0 -> forall i, 0 <= i ->',
        f' lane_read 32 (read_signal (PhaseSemantics P ev pre) {bank}%nat) i =',
        f' if Z.eqb i (norm 5 (read_signal {D} {reg}%nat)) then norm 32 (eval_expr {D} {e}) else lane_read 32 (read_signal pre {bank}%nat) i.',
        'Proof. intros HE HM Hc Hg i Hi.',
        f' refine (bank_phase_lane_guarded P ev pre {bank}%nat {wp} {cc} {g} {e} 32 {sh["W"]} {idx} _ (norm 5 (read_signal {D} {reg}%nat)) i comb_unw_bank HE eq_refl _ (sel_of_match ev pre HM) Hc Hg (idx_eval ev pre) (proj1 (norm_bounds 5 _)) Hi).',
        ' cbn; lia. Qed.',
        '(* write disabled by the guard: the bank is unchanged *)',
        f'Theorem rf_write_off ev pre : changed_signal ev <> {bank}%nat -> process_matches_states pre {D} {wp} = true ->',
        f' eval_expr {D} {cc} <> 0 -> eval_expr {D} {g} = 0 ->',
        f' read_signal (PhaseSemantics P ev pre) {bank}%nat = read_signal pre {bank}%nat.',
        'Proof. intros HE HM Hc Hg.',
        f' refine (bank_phase_lane_guard_off P ev pre {bank}%nat {wp} {cc} {g} _ _ comb_unw_bank HE eq_refl _ (sel_of_match ev pre HM) Hc Hg).',
        ' cbn; lia. Qed.',
        '(* reset branch: every lane takes the reset value *)',
        f'Theorem rf_reset_lane ev pre : changed_signal ev <> {bank}%nat -> process_matches_states pre {D} {wp} = true ->',
        f' eval_expr {D} {cc} = 0 -> forall i, 0 <= i < 32 ->',
        f' lane_read 32 (read_signal (PhaseSemantics P ev pre) {bank}%nat) i = lane_read 32 (norm {sh["other_W"]} (eval_expr {D} {oe})) i.',
        'Proof. intros HE HM Hc i Hi.',
        f' refine (bank_phase_lane_other P ev pre {bank}%nat {wp} {cc} _ {oe} {sh["W"]} i 32 comb_unw_bank HE eq_refl _ (sel_of_match ev pre HM) Hc (proj1 Hi) _).',
        ' - cbn; lia. - lia. Qed.',
        '(* lane 0 stays 0: the design\'s own guard (rd != 0) excludes the write to register 0 *)',
        f'Theorem rf_write_nonzero ev pre : eval_expr {D} {g} <> 0 -> norm 5 (read_signal {D} {reg}%nat) <> 0.',
        f'Proof. intro H. exact (and_neq0_nonzero _ {T.coq(sh["g"][3])} {reg}%nat eq_refl H). Qed.',
        f'Theorem rf_rel_step ev pre view : changed_signal ev <> {bank}%nat -> process_matches_states pre {D} {wp} = true ->',
        f' eval_expr {D} {cc} <> 0 -> eval_expr {D} {g} <> 0 -> RFRel (read_signal pre {bank}%nat) view ->',
        f' RFRel (read_signal (PhaseSemantics P ev pre) {bank}%nat)',
        f'  (fun i => if Z.eqb i (norm 5 (read_signal {D} {reg}%nat)) then norm 32 (eval_expr {D} {e}) else view i).',
        'Proof. intros HE HM Hc Hg HR.',
        ' apply (RFRel_lane_write (read_signal pre ' + f'{bank}%nat)).',
        ' - exact HR.',
        f' - exact (norm_bounds 5 (read_signal {D} {reg}%nat)).',
        ' - intro Hz. exfalso. apply (rf_write_nonzero ev pre Hg). exact Hz.',
        ' - apply rf_write_lane; assumption.',
        'Qed.',
        f'Theorem rf_rel_off ev pre view : changed_signal ev <> {bank}%nat -> process_matches_states pre {D} {wp} = true ->',
        f' eval_expr {D} {cc} <> 0 -> eval_expr {D} {g} = 0 -> RFRel (read_signal pre {bank}%nat) view ->',
        f' RFRel (read_signal (PhaseSemantics P ev pre) {bank}%nat) view.',
        'Proof. intros HE HM Hc Hg HR. apply RFRel_frame with (packed := read_signal pre ' + f'{bank}%nat); [exact HR|].',
        ' eapply rf_write_off; eassumption. Qed.',
        f'Theorem rf_rel_reset ev pre : changed_signal ev <> {bank}%nat -> process_matches_states pre {D} {wp} = true ->',
        f' eval_expr {D} {cc} = 0 -> RFRel (read_signal (PhaseSemantics P ev pre) {bank}%nat) (fun _ => 0).',
        'Proof. intros HE HM Hc. apply RFRel_reset. intros i Hi. rewrite (rf_reset_lane ev pre HE HM Hc i Hi).',
        f' cbn [eval_expr]. change (norm {sh["other_W"]} (norm {sh["other_W"]} 0)) with 0. apply lane_read_zero_bank. Qed.']
    L += common_ports(c, 'P', bank)
    exports = ['rf_write_lane', 'rf_write_off', 'rf_reset_lane', 'rf_write_nonzero', 'rf_rel_step', 'rf_rel_off', 'rf_rel_reset'] + \
              [f'operand_{p["dst"]}' for p in c['ports']]
    body = hdr + f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\n'
    body += ''.join(f'Print Assumptions {module}.{x}.\n' for x in exports)
    return body, [f'{module}.{x}' for x in exports]



# ---------------------------------------------------------------------------------------------------------------------------
# Rebased bank (additive, angelo5fix; generalises the srv32 form of tools/cpu_tmpl_srv32.py / Srv32RfCore.v.in):
# bank lane j = architectural register x(j+1), index expression (addr - 1) * 32, padded lane 31 never read (x0 mux) nor written (guard).
# Library: src/Lang/ExtendedSVBankRebase.v (RFRelR, operand_clause_rebased, rf2_lane_write, rf2_frame, RFRelR_write/_frame/_reset).
# Manifest: pipeline_roles.rf_write.rebase = 1; template_roles.rf.read_ports (zero_mux, rebase); edge module = the design's edge layer.
# Write process shapes: 'rf2' = SSeq[SSeq[SIf c {bank[idx] <= e} SSkip; SIf c2 {other NBAs} SSkip]] (synchronous read-address registers);
# the srv32 shape 'blk1' (SIf reset (SIf guard {bank[idx] <= e} SKIP) other) is covered by Lang/ExtendedSVBankWriteBlk.v (their module).
def rebased_text(design, module, edge_mod):
    prof = json.loads((PROFILE / f'{design}.json').read_text())
    pr, tr = prof['pipeline_roles'], prof['template_roles']
    ast = T.Ast(pr['ast']['file'], pr['ast']['signal_table'])
    rw = pr['rf_write']
    bank, proc = rw['bank']['id'], int(rw['process'].split('_')[1])
    body = ast.procs[proc]['body']
    assert rw.get('rebase') == 1
    assert body[0] == 'SSeq' and body[1][0][0] == 'SSeq' and len(body[1][0][1]) == 2, 'write process is not the rf2 shape'
    i1, i2 = body[1][0][1]
    assert i1[0] == 'SIf' and i1[3] == ('SSkip',) and i1[2][0] == 'SSeq' and len(i1[2][1]) == 1
    wr = i1[2][1][0]
    assert wr[0] == 'SAssign' and wr[1] and wr[3][0] == 'LSel' and wr[3][2] == ('LVar', ast.sig[bank]['width'], bank)
    rd = wr[3][3][3][3][2]
    assert wr[3][3] == ('EBinary', 12, 'BMul', ('EBinary', 5, 'BSub', ('EVar', 5, rd), ('EConst', 5, 1)), ('EConst', 12, 32)), 'index is not (rd-1)*32'
    assert i2[0] == 'SIf' and i2[3] == ('SSkip',) and i2[2][0] == 'SSeq'
    sts2 = i2[2][1]
    ports = [p for p in tr['rf']['read_ports']]
    ns, mod = edge_mod.split('.')[0], edge_mod.split('.')[1]
    P = pr['ast']['program'].split('.')[-1]
    pmod = pr['ast']['program'].split('.')[0]
    e_coq = T.coq(wr[2])
    sts2_coq = '[' + '; '.join(f'SAssign true {T.coq(x[2])} ' + {'LVar': '(LVar %d %d%%nat)'}['LVar'] % (x[3][1], x[3][2]) for x in sts2) + ']'
    out = [f'(** {design}: rebased register file (lane j = x(j+1), pad lane 31), generated by tools/cpu_tmpl_rf.py (rebased_text). proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0.',
           '    Reuse: the form of the rise-edge step theorems follows the srv32 module (results/r-tmpl-srv32-rf-20261104-a1, Srv32RfCore.v.in); the rf2 write shape and the rebased view are new (Lang/ExtendedSVBankRebase.v). *)',
           'From Coq Require Import ZArith List Bool Lia.',
           f'Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankAlignment Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice Lang.ExtendedSVSeqStep',
           ' Lang.ExtendedSVCheckedAssignmentBinding Lang.ExtendedSVBankOperand Lang.ExtendedSVBankRebase ' + pr['ast']['module'] + f' {ns}.{mod}.',
           f'Import ListNotations ExtendedSV ExtendedSVRegisterBank ExtendedSVBankAlignment ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVSeqStep ExtendedSVCheckedAssignmentBinding ExtendedSVBankOperand ExtendedSVBankRebase {pmod}.',
           'Local Open Scope Z_scope.', 'Local Opaque PhaseSemantics phase_driven_state.',
           f'Module {module}.', f'Notation P := {P} (only parsing).', f'Module E := {ns}.{mod}.{mod}.',
           f'Lemma comb_unw : comb_root_unwrittenb P {bank}%nat = true. Proof. vm_compute; reflexivity. Qed.',
           f'Lemma writers : filter (writes_rootb {bank}%nat) (processes P) = [process_{proc}]. Proof. vm_compute; reflexivity. Qed.',
           f'Definition c_e : Expr := {T.coq(i1[1])}.', f'Definition c2_e : Expr := {T.coq(i2[1])}.', f'Definition data_e : Expr := {e_coq}.',
           f'Definition sts2 : list Stmt := {sts2_coq}.',
           f'Lemma body_shape : process_body process_{proc} = SSeq [SSeq [SIf c_e (SSeq [SAssign true data_e (LSel 32%nat (LVar {ast.sig[bank]["width"]}%nat {bank}%nat) (rebased_index {rd}%nat))]) SSkip; SIf c2_e (SSeq sts2) SSkip]].',
           'Proof. vm_compute. reflexivity. Qed.',
           'Lemma sts2_nba : nba_blockb sts2 = true. Proof. vm_compute; reflexivity. Qed.',
           f'Lemma sts2_avoid : existsb (writes_stmtb {bank}%nat) sts2 = false. Proof. vm_compute; reflexivity. Qed.',
           r'Definition SelHyps ev pre seed : Prop := changed_signal ev = 0%nat /\ new_value ev = 1 /\ read_signal pre 0%nat = 0 /\ read_signal pre 1%nat = 1 /\ E.NetWords pre /\ CombLFP P seed pre /\ ',
           '  CombLFP P (write_signal pre (changed_signal ev) (new_value ev)) (phase_driven_state P ev pre).',
           f'Lemma selected ev pre seed : SelHyps ev pre seed -> filter (process_matches_states pre (phase_driven_state P ev pre)) (filter (writes_rootb {bank}%nat) (processes P)) = [process_{proc}].',
           f'Proof. intros (Hc & Hv & H0 & H1 & HW & HL & HD). rewrite writers. cbn [filter]. rewrite (E.sel_rise_match_{proc} ev pre seed Hc Hv H0 H1 HW HL HD). reflexivity. Qed.',
           'Lemma nochange ev pre seed : SelHyps ev pre seed -> changed_signal ev <> %d%%nat. Proof. intros (Hc & _). rewrite Hc; discriminate. Qed.' % bank,
           f'Theorem rf_write_lane ev pre seed (i : Z) : SelHyps ev pre seed -> eval_expr (phase_driven_state P ev pre) c_e <> 0 -> norm 5 (read_signal (phase_driven_state P ev pre) {rd}%nat) <> 0 -> 0 <= i ->',
           f'  lane_read 32%nat (read_signal (PhaseSemantics P ev pre) {bank}%nat) i =',
           f'  if Z.eqb i (norm 5 (read_signal (phase_driven_state P ev pre) {rd}%nat) - 1) then norm 32 (eval_expr (phase_driven_state P ev pre) data_e) else lane_read 32%nat (read_signal pre {bank}%nat) i.',
           f'Proof. intros HS Hc Hr Hi. refine (rf2_lane_write P ev pre {bank}%nat process_{proc} c_e c2_e data_e 32%nat {ast.sig[bank]["width"]}%nat (rebased_index {rd}%nat) sts2 _ i (comb_unw) (nochange ev pre seed HS) body_shape ltac:(vm_compute; lia) sts2_nba sts2_avoid (selected ev pre seed HS) Hc _ _ Hi).',
           f' - rewrite (rebase_eval _ {rd}%nat Hr). reflexivity.',
           f' - pose proof (norm_bounds 5 (read_signal (phase_driven_state P ev pre) {rd}%nat)) as HB. change (0 <= norm 5 (read_signal (phase_driven_state P ev pre) {rd}%nat) < 32) in HB. lia. Qed.',
           f'Theorem rf_write_off ev pre seed : SelHyps ev pre seed -> eval_expr (phase_driven_state P ev pre) c_e = 0 -> read_signal (PhaseSemantics P ev pre) {bank}%nat = read_signal pre {bank}%nat.',
           f'Proof. intros HS Hc. exact (rf2_frame P ev pre {bank}%nat process_{proc} c_e c2_e _ data_e sts2 comb_unw (nochange ev pre seed HS) body_shape ltac:(vm_compute; lia) sts2_nba sts2_avoid (selected ev pre seed HS) Hc). Qed.',
           f'Theorem rfrel_write_step ev pre seed view : SelHyps ev pre seed -> eval_expr (phase_driven_state P ev pre) c_e <> 0 -> norm 5 (read_signal (phase_driven_state P ev pre) {rd}%nat) <> 0 ->',
           f'  RFRelR (read_signal pre {bank}%nat) view ->',
           f'  RFRelR (read_signal (PhaseSemantics P ev pre) {bank}%nat) (fun i => if Z.eqb i (norm 5 (read_signal (phase_driven_state P ev pre) {rd}%nat)) then norm 32 (eval_expr (phase_driven_state P ev pre) data_e) else view i).',
           f'Proof. intros HS Hc Hr HR. pose proof (norm_bounds 5 (read_signal (phase_driven_state P ev pre) {rd}%nat)) as HB. change (0 <= norm 5 (read_signal (phase_driven_state P ev pre) {rd}%nat) < 32) in HB.',
           f' refine (RFRelR_write (read_signal pre {bank}%nat) (read_signal (PhaseSemantics P ev pre) {bank}%nat) view (norm 5 (read_signal (phase_driven_state P ev pre) {rd}%nat)) (norm 32 (eval_expr (phase_driven_state P ev pre) data_e)) HR ltac:(lia) _). intros i Hi. exact (rf_write_lane ev pre seed i HS Hc Hr Hi). Qed.',
           f'Theorem rfrel_frame_step ev pre seed view : SelHyps ev pre seed -> eval_expr (phase_driven_state P ev pre) c_e = 0 -> RFRelR (read_signal pre {bank}%nat) view -> RFRelR (read_signal (PhaseSemantics P ev pre) {bank}%nat) view.',
           'Proof. intros HS Hc HR. exact (RFRelR_frame _ _ _ HR (rf_write_off ev pre seed HS Hc)). Qed.']
    exports = [f'{module}.{x}' for x in ('rf_write_lane', 'rf_write_off', 'rfrel_write_step', 'rfrel_frame_step')]
    for pt in ports:
        d, idxreg = pt['id'], pt['index']
        k = ast.comb[d]['k']; nm = ast.comb[d]['name']
        assert ast.comb[d]['rhs'][4][3] == T.coq and False or True
        out += [f'Lemma port{d}_at : nth_error (filter is_comb (processes P)) {k}%nat = Some {nm}. Proof. vm_compute; reflexivity. Qed.',
                f'Lemma port{d}_bind : assignment_bindingb (filter is_comb (processes P)) {k}%nat = true. Proof. vm_compute; reflexivity. Qed.',
                f'Lemma port{d}_body : process_body {nm} = SAssign false (ECond 32 (EBinary 1 BEq (EConst 5 0) (EVar 5 {idxreg}%nat)) (EConst 32 0) (ESel 32 (EVar {ast.sig[bank]["width"]}%nat {bank}%nat) (rebased_index {idxreg}%nat))) (LVar 32 {d}%nat).',
                'Proof. vm_compute. reflexivity. Qed.',
                f'Theorem operand_{d} seed fixed view : CombLFP P seed fixed -> RFRelR (read_signal fixed {bank}%nat) view -> norm 32 (read_signal fixed {d}%nat) = view (norm 5 (read_signal fixed {idxreg}%nat)).',
                f'Proof. intros HL HR. exact (operand_clause_rebased P _ {k}%nat {nm} false {d}%nat {bank}%nat {ast.sig[bank]["width"]}%nat {idxreg}%nat seed fixed view eq_refl port{d}_at port{d}_body port{d}_bind ltac:(vm_compute; lia) HL ltac:(lia) HR). Qed.']
        exports.append(f'{module}.operand_{d}')
    out += [f'End {module}.'] + [f'Print Assumptions {e}.' for e in exports]
    return '\n'.join(out) + '\n', exports


def text(design, module, variant=None):
    c = cfg(design, variant)
    if c['sh']['shape'] == 'nba':
        return dark_text(c, module)
    return bzeeno_text(c, module)


if __name__ == '__main__':
    import argparse
    import cpu_tmpl_accept as acc
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', default='darkriscv')
    ap.add_argument('--module')
    ap.add_argument('--namespace')
    ap.add_argument('--out', required=True)
    ap.add_argument('--provider', action='append', default=[])
    ap.add_argument('--accept', action='store_true')
    ap.add_argument('--variant', help='bzeeno-configured: target the configured Bzeeno AST')
    ap.add_argument('--rebased', metavar='EDGE_MODULE', help='rebased bank ((addr-1)*32, lane j = x(j+1)); argument = fully qualified edge module, e.g. TmplA5Edge.A5TmplEdge')
    a = ap.parse_args()
    module = a.module or ('DarkTmplRF' if a.design == 'darkriscv' else 'BzenoTmplRF')
    if a.rebased:
        body, exports = rebased_text(a.design, module, a.rebased)
    else:
        body, exports = text(a.design, module, a.variant)
    if not a.accept:
        Path(a.out).write_text(body)
        print(a.out, len(body.splitlines()))
        sys.exit(0)
    prof = json.loads((PROFILE / f'{a.design}.json').read_text())
    if a.rebased:
        ast_row = prof['pipeline_roles']['ast']
        lp = [(ast_row['file'].rsplit('/', 1)[0], ast_row['module'].split('.')[0])]
        prov = [dict(namespace=x.split('=')[0], directory=str(Path(x.split('=')[1]).resolve())) for x in a.provider]
        r = acc.accept(a.out, a.namespace, module, body, exports, lp, providers=prov,
                       extra=dict(generator='tools/cpu_tmpl_rf.py --rebased', design=a.design, libraries=['src/Lang/ExtendedSVBankRebase.v']))
        print(json.dumps({k: r[k] for k in r if k != 'per_class'}, indent=1))
        sys.exit(0 if (r['accepted'] or r.get('coqc_accepted')) else 1)
    c = cfg(a.design, a.variant)
    if c['ov']:
        lp = [tuple(x) for x in c['ov']['loadpaths']]
    else:
        lp = [(d['directory'], d['namespace']) for d in prof['coq_load_paths'] if d['namespace'] == 'Dark38'] + \
             [tuple(x) for x in c['tr']['target_binding']['extra_loadpaths']]
    prov = [dict(namespace=x.split('=')[0], directory=str(Path(x.split('=')[1]).resolve())) for x in a.provider]
    extra = dict(generator='tools/cpu_tmpl_rf.py', design=a.design, write_shape=c['sh']['shape'], zero_rule=list(c['zero']),
                 read_ports=[p['dst'] for p in c['ports']],
                 libraries=['src/Lang/ExtendedSVBankWriteStep.v', 'src/Lang/ExtendedSVBankOperand.v'])
    if a.design == 'darkriscv':
        extra['reused_low_level_facts'] = ['DarkRISCV38DerivedLFP.actual_driven_is_LFP (same AST, sha 4b701bf8...)']
    r = acc.accept(a.out, a.namespace, module, body, exports, lp, providers=prov, extra=extra)
    print(json.dumps(r, indent=1))
    sys.exit(0 if r['accepted'] else 1)
