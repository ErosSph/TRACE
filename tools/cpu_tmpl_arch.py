#!/usr/bin/env python3
"""goal_arch glue (RF part), generated per class from the ISA class table.

For every class C a lemma `rfarch_C`: in a committing cycle (FLUSH=0, XRES=0, HLT=0) whose slot word decodes to class C
(fields from CPUClassTableInverse.inv_C), the register bank after the actual cycle equals the ISA register view after the
ISA step: RFZero (bank') post, for any ISA post state whose register file has the family shape
(dataop_post / jump_post / branch_post). It composes inv_prem_C (R -> premise), C_controls (premise -> RTL write),
operand_isa_* and cycle_rf_rel (RF agent), bridge_C (class formula -> result_word), isa_simm_G (immediates),
rfrel_after_write/keep (ISA register-write effect). Design-independent parts live in src/Ex/External/CPUISARegView.v.
"""
import json
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles
import cpu_tmpl_params as PR
import cpu_tmpl_controls as ctl
import cpu_tmpl_inv as inv
import cpu_isa_classes as isa
import cpu_class_table as ct

HDR = r"""From Coq Require Import ZArith List Bool Lia.
Require Import coqutil.Z.BitOps Lang.ExtendedSV Lang.ExtendedSVCheckedAssignmentBinding Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVBankOperand Lang.ExtendedSVExprAgreement Lang.ExtendedSVRootProjection Lang.ExtendedSVBankAlignment
 Ex.External.CPUISARegView Ex.External.CPUClassValueBridge Ex.External.CPUClassTableInverse Ex.External.CPUImmediateShapes
 Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PDataOpExecution Ex.RvCore.FormalSpec riscv.Utility.Utility
 Ex.External.DarkRISCV38DerivedTarget Ex.External.DarkRISCV38DerivedCycle Ex.External.DarkRISCV38DerivedLFP Dark38.DarkRISCV38DerivedAST
 TmplDarkControls.DarkTmplControls TmplDarkInv.DarkTmplInv TmplDarkCycle.DarkTmplCycle TmplDarkRF.DarkTmplRF TmplDarkImm.DarkTmplImm
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVBankOperand ExtendedSVCheckedAssignmentBinding ExtendedSVExprAgreement ExtendedSVRootProjection CPUISARegView CPUImmediateShapes DarkRISCV38DerivedCycle DarkRISCV38DerivedLFP
 DarkRISCV38DerivedTarget.DarkRISCV38DerivedTarget DarkRISCV38DerivedAST.
Local Open Scope Z_scope.
Module CT := TmplDarkControls.DarkTmplControls.DarkTmplControls.
Module IV := TmplDarkInv.DarkTmplInv.DarkTmplInv.
Module CY := TmplDarkCycle.DarkTmplCycle.DarkTmplCycle.
Module RF := TmplDarkRF.DarkTmplRF.DarkTmplRF.
Module IM := TmplDarkImm.DarkTmplImm.DarkTmplImm.
Module BR := CPUClassValueBridge.CPUClassValueBridge.
Module INVC := CPUClassTableInverse.CPUClassTableInverse.
Notation P := dark38_program (only parsing).
"""

GROUP_KIND = {'OPIMM': 'I', 'JALR': 'I', 'BRANCH': 'B', 'JAL': 'J', 'LUI': 'U', 'AUIPC': 'U'}


def split_args(a):
    toks, depth, cur = [], 0, ''
    for ch in a:
        if ch == '(':
            depth += 1
        if ch == ')':
            depth -= 1
        if ch == ' ' and depth == 0:
            toks.append(cur)
            cur = ''
        else:
            cur += ch
    toks.append(cur)
    return toks


def core(g):
    """Class independent lemmas: wires, field extraction, coherent transfer, immediates."""
    out = []
    ids = g.pr['controller']
    word = g.pr['fetch_slot']['word']['id']
    for r in (ids['rd']['id'], ids['rs1']['id'], ids['rs2']['id'], ids['imm_signed']['id']):
        g.wire_eq(r)
    out += g.head
    fields, inword = inv.captured_fields(g.ast, g.pr)
    reg_ids = [R for R, _, _ in fields]
    lsb = {ids[k]['id']: g.ast.comb[ids[k]['id']]['rhs'][3][2] for k in ('rd', 'rs1', 'rs2')}
    for name, k in (('rd', 'rd'), ('rs1', 'rs1'), ('rs2', 'rs2')):
        x = ids[k]['id']
        lo = lsb[x]
        out += [f'Lemma field_{x} seed d w : CombLFP P seed d -> norm 32 (read_signal d {word}%nat) = w -> norm 5 (read_signal d {x}%nat) = bitSlice w {lo} {lo + 5}.',
                f'Proof. intros HL Hw. rewrite (eq_w{x} seed d HL). unfold orig_w{x}. cbn [eval_expr]. change (norm 5 {lo}) with {lo}. rewrite Hw.',
                f' rewrite (bs_norm w {lo} {lo + 5}) by lia. replace (Z.to_nat ({lo + 5} - {lo})) with 5%nat by reflexivity. rewrite norm_idempotent. reflexivity. Qed.']
    lst0 = ';'.join(str(r) for r in reg_ids)
    out += [f'Lemma comb_unw_regs R : In R [{lst0}]%nat -> comb_root_unwrittenb P R = true /\\ R <> @id:CLK@%nat.',
            'Proof. intro HR. cbn in HR. repeat (destruct HR as [<-|HR]; [split; [vm_compute; reflexivity|discriminate]|]). contradiction. Qed.']
    out += ['Lemma ram_keep image s : norm 1 (read_signal (phase_driven_state P rise (rtl s)) @id:DBUS_REQ@%nat) = 0 -> ram (actual_cycle image s) = ram s.',
            'Proof. intro H. pose proof (target_samples_actual_memory_ports image s) as E. change (ram (actual_cycle image s) = sampled_ram_next (ram s) (phase_driven_state P rise (rtl s))) in E. rewrite E. unfold sampled_ram_next. rewrite H. reflexivity. Qed.']
    out += ['Lemma isa_view_eq r x : RF.isa_view r x = isa_view r x. Proof. reflexivity. Qed.']
    # coherent transfer
    out += ['Lemma coh_clause w R g f1 f2 : read_signal f1 R = read_signal f2 R ->',
            ' (forall wi r, In (wi, r) (expr_inputs g) -> read_signal f1 r = read_signal f2 r) ->',
            ' norm w (read_signal f1 R) = norm w (eval_expr f1 g) -> norm w (read_signal f2 R) = norm w (eval_expr f2 g).',
            'Proof. intros H1 H2 H3. rewrite <- H1, <- (eval_expr_agree g f1 f2 (fun wi r Hin => f_equal (norm wi) (H2 wi r Hin))). exact H3. Qed.']
    lst = ';'.join(str(r) for r in reg_ids)
    out += [f'Lemma coh_transfer f1 f2 : (forall R, In R [{lst}]%nat -> read_signal f1 R = read_signal f2 R) -> IV.CoherentFields f1 -> IV.CoherentFields f2.',
            'Proof. intros H C. unfold IV.CoherentFields in *.']
    pat = f'C{reg_ids[-1]}'
    for R in reversed(reg_ids[:-1]):
        pat = f'[C{R} {pat}]'
    out += [f' destruct C as {pat}.',
            ' repeat split; (eapply coh_clause; [apply H; cbn; tauto | intros wi r Hin; cbn [expr_inputs] in Hin; repeat (destruct Hin as [Hin|Hin]); try contradiction; ' +
            'try (inversion Hin; subst; apply H; cbn; tauto) | assumption]). Qed.']
    # coherent clause for the immediate register
    simm = ids['imm_signed']['id']
    reg = g.ast.comb[simm]['rhs'][2]
    pat41 = '_'
    names = [f'C{R}' if R == reg else '_' for R in reg_ids]
    p = names[-1]
    for n in reversed(names[:-1]):
        p = f'[{n} {p}]'
    out += [f'Lemma coh_imm f : IV.CoherentFields f -> norm 32 (read_signal f {reg}%nat) = norm 32 (eval_expr f IM.simm_expr).',
            f'Proof. unfold IV.CoherentFields. intro C. destruct C as {p}. exact C{reg}. Qed.']
    for G, k in GROUP_KIND.items():
        opc = [c['opcode'] for c in isa.classes() if c['group'] == G][0]
        out += [f'Lemma simm_{G} seed d w : CombLFP P seed d -> IV.CoherentFields d -> norm 32 (read_signal d {word}%nat) = w -> norm 7 w = {opc} ->',
                f' norm 32 (read_signal d {simm}%nat) = norm 32 (isa_imm_{k} w).',
                f'Proof. intros HL C Hw Hop. rewrite (eq_w{simm} seed d HL). unfold orig_w{simm}. cbn [eval_expr]. rewrite norm_idempotent.',
                f' rewrite (coh_imm d C). rewrite (IM.isa_simm_{G} d ltac:(rewrite Hw; exact Hop)). rewrite Hw. reflexivity. Qed.']
    return out


def nested(names):
    p = names[-1]
    for n in reversed(names[:-1]):
        p = f'[{n} {p}]'
    return p


def class_text(g, c):
    n, grp, kind = c['name'], c['group'], c['kind']
    ids = g.id
    word = g.pr['fetch_slot']['word']['id']
    toks = split_args(ct.args(c))
    k = len(toks)
    vs = [f'a{i}' for i in range(k)]
    hy = ct.hyps(c)
    eqs = ' /\\ '.join(f'{v} = {e}' for v, e in zip(vs, toks))
    hyp_s = ' /\\ '.join(hy)
    ins = f'(Decode.{n} {" ".join(vs)})'
    shift_imm = n in ('Slli', 'Srli', 'Srai')
    if kind == 'branch':
        shape, v = 'getRegs post = getRegs r', None
    else:
        v = ('word.add (getPc r) (word.of_Z 4)' if kind in ('jal', 'jalr') else f'CV32E40PDataOpExecution.result_word r {ins}')
        shape = f'getRegs post = (if Z.eq_dec a0 0 then getRegs r else map.put (getRegs r) a0 ({v}))'
    extra = ''
    xn = ''
    if n == 'Auipc':
        extra, xn = f'norm 32 (read_signal (rtl s) {ids["pc"]}%nat) = word.unsigned (getPc r) -> ', ' Hpc'
    if kind in ('jal', 'jalr'):
        extra, xn = f'norm 32 (read_signal (rtl s) {ids["link"]}%nat) = norm 32 (word.unsigned (getPc r) + 4) -> ', ' Hlink'
    hn = [f'Hh{i}' for i in range(len(hy))]
    eqn = [f'Eq{i}' for i in range(k)]
    L = [f'Lemma rfarch_{n} image s r post w {" ".join(vs)} :',
         ' CY.env_ok s -> RF.RFZero (read_signal (rtl s) @id:BANK@%nat) r -> IV.CoherentFields (rtl s) ->',
         f' norm 1 (read_signal (rtl s) {ids["xres"]}%nat) = 0 -> norm 2 (read_signal (rtl s) {ids["flush"]}%nat) = 0 ->',
         f' norm 32 (read_signal (rtl s) {word}%nat) = w ->',
         f' (({eqs}) /\\ {hyp_s}) -> {extra}{shape} ->',
         ' RF.RFZero (read_signal (rtl (actual_cycle image s)) @id:BANK@%nat) post /\\ ram (actual_cycle image s) = ram s.',
         f'Proof. intros HE HZ HC HX HF Hw Hinv{xn} Hregs.',
         f' destruct Hinv as [{nested(eqn)} {nested(hn)}].',
         ' pose proof (actual_driven_is_LFP rise (rtl s)) as HL. set (d := phase_driven_state P rise (rtl s)) in *.',
         ' set (seed := write_signal (rtl s) (changed_signal rise) (new_value rise)) in *.',
         ' assert (Hdr : forall R, comb_root_unwrittenb P R = true -> R <> @id:CLK@%nat -> read_signal d R = read_signal (rtl s) R) by (intros R H1 H2; exact (CY.driven_read (rtl s) R H1 H2)).',
         ' assert (Hbank : read_signal d @id:BANK@%nat = read_signal (rtl s) @id:BANK@%nat) by (apply Hdr; [vm_compute; reflexivity|discriminate]).',
         ' assert (HZd : RF.RFZero (read_signal d @id:BANK@%nat) r) by (rewrite Hbank; exact HZ).',
         f' assert (Hw1 : norm 32 (read_signal d {word}%nat) = w) by (rewrite (Hdr {word}%nat ltac:(vm_compute; reflexivity) ltac:(discriminate)); exact Hw).',
         f' assert (Hx1 : norm 1 (read_signal d {ids["xres"]}%nat) = 0) by (rewrite (Hdr {ids["xres"]}%nat CY.comb_unw_{ids["xres"]} ltac:(discriminate)); exact HX).',
         f' assert (Hf1 : norm 2 (read_signal d {ids["flush"]}%nat) = 0) by (rewrite (Hdr {ids["flush"]}%nat CY.comb_unw_{ids["flush"]} ltac:(discriminate)); exact HF).',
         f' assert (Hhl : norm 1 (read_signal d {ids["halt"]}%nat) = 0) by exact (CY.driven_halt s HE).',
         ' assert (Cd : IV.CoherentFields d) by (apply (coh_transfer (rtl s) d); [intros R HR; symmetry; destruct (comb_unw_regs R HR) as [Hu Hn]; exact (Hdr R Hu Hn)|exact HC]).',
         f' assert (Hop : norm 7 (norm 32 (read_signal d {word}%nat)) = {c["opcode"]}).',
         f' {{ rewrite Hw1. pose proof {hn[0]} as Hb. rewrite (bs_norm w 0 7) in Hb by lia. replace (Z.to_nat (7 - 0)) with 7%nat in Hb by reflexivity. rewrite Z.shiftr_0_r in Hb. exact Hb. }}']
    pcall = f'IV.inv_prem_{n} seed d HL (conj Hx1 (conj Hhl Hf1)) Cd Hop'
    if c['funct3'] is not None:
        L += [f' assert (H3 : norm 3 (Z.shiftr (norm 32 (read_signal d {word}%nat)) 12) = {c["funct3"]}).',
              f' {{ rewrite Hw1. pose proof {hn[1]} as Hb. rewrite (bs_norm w 12 15) in Hb by lia. replace (Z.to_nat (15 - 12)) with 3%nat in Hb by reflexivity. exact Hb. }}']
        pcall += ' H3'
    if c['funct7'] is not None:
        if grp == 'OP':
            L += [f' assert (H7 : norm 7 (Z.shiftr (norm 32 (read_signal d {word}%nat)) 25) = {c["funct7"]}).',
                  f' {{ rewrite Hw1. pose proof {hn[-1]} as Hb. rewrite (bs_norm w 25 32) in Hb by lia. replace (Z.to_nat (32 - 25)) with 7%nat in Hb by reflexivity. exact Hb. }}']
        else:
            L += [f' assert (H7 : norm 7 (Z.shiftr (norm 32 (read_signal d {word}%nat)) 25) = {c["funct7"]}).',
                  f' {{ rewrite Hw1. rewrite (bs7_shift w {hn[-1]}), {hn[-2]}. reflexivity. }}']
        pcall += ' H7'
    L += [f' pose proof ({pcall}) as Hprem.',
          f' pose proof (CT.{n}_controls seed d HL Hprem) as {nested(["Hrf"] + ["_"] * (3 + {"dataop": 0, "jal": 1, "jalr": 1, "branch": 2}[kind]) + ["Hd8", "Hd13", "Hd14"])}.']
    dp = ids['rd']
    if kind != 'branch':
        L += [f' assert (Dp : norm 5 (read_signal d {dp}%nat) = a0) by (rewrite (field_{dp} seed d w HL Hw1), Eq0; reflexivity).']

    def op(idn, fld, argn):
        return [f' assert (O{idn} : norm 32 (read_signal d {idn}%nat) = word.unsigned (CV32E40PReq40StateRel.CV32E40PReq40StateRel.formal_register_word r {argn})).',
                f' {{ rewrite (RF.operand_isa_{idn} seed d r HL HZd), (field_{fld} seed d w HL Hw1), <- Eq{vs.index(argn)}. exact (eq_sym (view_formal r {argn})). }}']
    RS1, RS2 = g.pr['controller']['rs1']['id'], g.pr['controller']['rs2']['id']
    ra, rb, ni = ids['a'], ids['b'], ids['imm']
    if kind == 'dataop' and grp == 'OP':
        L += op(ra, RS1, 'a1') + op(rb, RS2, 'a2')
    elif kind == 'dataop' and grp == 'OPIMM':
        L += op(ra, RS1, 'a1')
    if grp in ('OPIMM', 'LUI', 'AUIPC'):
        if shift_imm:
            L += [f' assert (Oimm : norm 32 (read_signal d {ni}%nat) = norm 32 (isa_imm_I w)) by exact (simm_OPIMM seed d w HL Cd Hw1 ltac:(rewrite <- Hw1; exact Hop)).',
                  f' assert (Hsh2 : norm 5 (norm 32 (read_signal d {ni}%nat)) = a2) by (rewrite Oimm, Eq2; unfold Utility.machineIntToShamt; exact (shamt_imm w {hn[-1]})).',
                  ' assert (Hsh1 : 0 <= a2 < 32) by (rewrite <- Hsh2; pose proof (ExtendedSVBankAlignment.norm_bounds 5 (norm 32 (read_signal d ' + str(ni) + '%nat))) as [B0 B1]; change (2 ^ Z.of_nat 5) with 32 in B1; lia).']
        else:
            L += [f' assert (Oimm : norm 32 (read_signal d {ni}%nat) = norm 32 a{k - 1}).',
                  f' {{ rewrite (simm_{grp} seed d w HL Cd Hw1 ltac:(rewrite <- Hw1; exact Hop)), Eq{k - 1}. reflexivity. }}']
    if kind == 'dataop':
        pass
    # value of the RTL write
    L += [f' pose proof (RF.cycle_rf_rel image s (RF.isa_view r) HE (RF.rfzero_to_rfrel _ _ HZ)) as Hrel.',
          ' refine (conj _ (ram_keep image s Hd8)). apply RF.rfrel_to_rfzero.']
    if kind == 'branch':
        L += [f' assert (Hv : norm 32 (eval_expr d CT.orig_t_rf_value) = isa_view r (norm 5 (read_signal d {dp}%nat))).',
              f' {{ rewrite Hrf. destruct (Z.eqb 0 (norm 5 (read_signal d {dp}%nat))) eqn:E0.',
              '   - apply Z.eqb_eq in E0. rewrite <- E0. reflexivity.',
              f'   - rewrite (RF.operand_isa_68 seed d r HL HZd), isa_view_eq. reflexivity. }}',
              f' eapply (rfrel_after_keep _ r post (norm 5 (read_signal d {dp}%nat))); [exact Hrel|exact Hv|exact Hregs].',
              'Qed.']
        return L
    L += [f' assert (Hv : norm 32 (eval_expr d CT.orig_t_rf_value) = (if Z.eqb 0 (norm 5 (read_signal d {dp}%nat)) then 0 else word.unsigned ({v}))).',
          ' { rewrite Hrf. rewrite Dp. destruct (Z.eqb 0 a0); [reflexivity|].']
    if grp == 'OP':
        L += [f'   rewrite O{ra}, O{rb}. exact (BR.bridge_{n} r a0 a1 a2). }}']
    elif grp == 'OPIMM' and not shift_imm:
        L += [f'   rewrite O{ra}, Oimm. exact (BR.bridge_{n} r a0 a1 a2). }}']
    elif shift_imm:
        L += [f'   rewrite O{ra}. exact (BR.bridge_{n} r a0 a1 a2 (norm 32 (read_signal d {ni}%nat)) Hsh1 Hsh2). }}']
    elif n == 'Lui':
        L += ['   rewrite Oimm. exact (BR.bridge_Lui r a0 a1). }']
    elif n == 'Auipc':
        L += [f'   rewrite (Hdr {ids["pc"]}%nat ltac:(vm_compute; reflexivity) ltac:(discriminate)), Hpc, Oimm. exact (BR.bridge_Auipc r a0 a1). }}']
    else:
        L += [f'   rewrite (Hdr {ids["link"]}%nat ltac:(vm_compute; reflexivity) ltac:(discriminate)), norm_idempotent, Hlink, uw_link. reflexivity. }}']
    L += [f' exact (rfrel_after_write _ r post a0 ({v}) (norm 5 (read_signal d {dp}%nat)) (norm 32 (eval_expr d CT.orig_t_rf_value)) Hrel Dp Hv Hregs).',
          'Qed.']
    return L


def text(classes=None, module='DarkTmplArchRF', design='darkriscv'):
    g = ctl.Gen(design, module)
    body = core(g)
    names = []
    for c in isa.classes():
        if classes and c['name'] not in classes:
            continue
        body += class_text(g, c)
        names.append(f'rfarch_{c["name"]}')
    out = HDR + f'Module {module}.\n' + '\n'.join(body) + f'\nEnd {module}.\n' + ''.join(f'Print Assumptions {module}.{n}.\n' for n in names)
    return PR.Params(design).render(out), [f'{module}.{n}' for n in names]


if __name__ == '__main__':
    import argparse
    import cpu_tmpl_accept as acc
    ap = argparse.ArgumentParser()
    ap.add_argument('--module', default='DarkTmplArchRF')
    ap.add_argument('--namespace')
    ap.add_argument('--out', required=True)
    ap.add_argument('--classes')
    ap.add_argument('--provider', action='append', default=[])
    ap.add_argument('--accept', action='store_true')
    a = ap.parse_args()
    body, exports = text(a.classes.split(',') if a.classes else None, a.module)
    if not a.accept:
        Path(a.out).write_text(body)
        print(a.out)
        sys.exit(0)
    prov = [dict(namespace=x.split('=')[0], directory=str(Path(x.split('=')[1]).resolve())) for x in a.provider]
    lp = [(d['directory'], d['namespace']) for d in json.loads(Path('framework/auto-contract-profiles/darkriscv.json').read_text())['coq_load_paths']
          if d['namespace'] == 'Dark38']
    r = acc.accept(a.out, a.namespace, a.module, body, exports, lp, providers=prov, extra=dict(generator='tools/cpu_tmpl_arch.py', design='darkriscv'))
    print(json.dumps(r, indent=1))
    sys.exit(0 if r['accepted'] else 1)
