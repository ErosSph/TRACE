#!/usr/bin/env python3
"""Per-design ISA lift builders for tools/cpu_tmpl_lift.py (role parametric; roles in framework/lift-roles/<design>.json).
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import json, re
from pathlib import Path
import cpu_isa_classes as isa

ROOT = Path(__file__).resolve().parent.parent
AND = ' /\\ '
AUTHOR = 'LLM-generated: Claude Code (claude-sonnet-5-5)'

PRE = '''From Coq Require Import ZArith List Bool Lia.
Require Import coqutil.Z.BitOps Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVWordInvariant Ex.External.CPUImmediateShapes Ex.External.CPUDatapathFacts Ex.External.CPUISARegView Lang.ExtendedSVBankAlignment Ex.External.CPUJumpFamilyProgramDomain
 Ex.External.CV32E40PReq41Instruction Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PDataOpExecution Ex.External.CV32E40PISAWordInterpretation Ex.External.CPUClassValueBridge
 Ex.External.CV32E40PBranchISACondition Ex.RvCore.FormalSpec Ex.RvCore.Machine coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility riscv.Utility.MkMachineWidth
 @AST@ @PROVIDERS@.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVWordInvariant CPUImmediateShapes CPUDatapathFacts CV32E40PReq40StateRel CV32E40PDataOpExecution CV32E40PISAWordInterpretation CV32E40PBranchISACondition.
Local Open Scope Z_scope.
Definition P:=@PROG@.
Module Pv := @PROV@.
Module LI := @ISAMOD@.
Module BR := CPUClassValueBridge.CPUClassValueBridge.
Module V := Ex.External.CPUISARegView.CPUISARegView.
'''


def split_top(s, sep):
    out, depth, cur, i = [], 0, '', 0
    while i < len(s):
        ch = s[i]
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            out.append(cur); cur = ''; i += len(sep); continue
        cur += ch; i += 1
    out.append(cur)
    return out


def binders(c):
    n, g = c['name'], c['group']
    if g == 'OP':
        return ['rd', 'rs1', 'rs2'], 'rd rs1 rs2'
    if g == 'OPIMM':
        if n in ('Slli', 'Srli', 'Srai'):
            return ['rd', 'rs', 'sh'], 'rd rs sh'
        return ['rd', 'rs', 'imm'], 'rd rs imm'
    if g in ('LUI', 'AUIPC', 'JAL'):
        return ['rd', 'imm'], 'rd imm'
    if g == 'JALR':
        return ['rd', 'rs', 'imm'], 'rd rs imm'
    return ['rs1', 'rs2', 'imm'], 'rs1 rs2 imm'


USES = lambda c: dict(
    a=c['group'] in ('OP', 'OPIMM', 'JALR', 'BRANCH'),
    b=c['group'] in ('OP', 'BRANCH'),
    imm=c['group'] != 'OP',
    pc=True, w=True)


HELP2 = r'''Require Import coqutil.Z.bitblast coqutil.Z.prove_Zeq_bitwise.
Lemma m4_m2 x : x mod 4 = 0 -> x mod 2 = 0.
Proof. intro H. apply Z.mod_divide in H; [|lia]. destruct H as [k ->]. apply Z.mod_divide; [lia|]. exists (2 * k). lia. Qed.
Lemma bit1_m4 y : y mod 4 = 0 -> norm 1 (Z.shiftr y 1) = 0.
Proof. intro H. apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. rewrite Hk. rewrite Z.shiftr_div_pow2 by lia.
 change (2 ^ 1) with 2. assert (E : k * 4 / 2 = k * 2) by (symmetry; apply Z.div_unique_exact; lia). rewrite E.
 rewrite ExtendedSVBankAlignment.norm_mod. change (2 ^ Z.of_nat 1) with 2. apply Z.mod_divide; [lia|]. exists k. lia. Qed.
Lemma bit1_land y : norm 1 (Z.shiftr y 1) = norm 1 (Z.shiftr (Z.land y (2 ^ 32 - 2)) 1).
Proof. rewrite !norm_ones. change (Z.of_nat 1) with 1. apply Z.bits_inj'. intros i Hi.
 rewrite !Z.land_spec, !Z.shiftr_spec by lia. rewrite Z.land_spec.
 destruct (Z.eq_dec i 0) as [->|N].
 - cbn [Z.add]. assert (H : Z.testbit (2 ^ 32 - 2) 1 = true) by (vm_compute; reflexivity). rewrite H. destruct (Z.testbit y 1), (Z.testbit (Z.ones 1) 0); reflexivity.
 - assert (Hz : Z.testbit (Z.ones 1) i = false) by (rewrite Z.testbit_ones_nonneg by lia; apply Z.ltb_ge; lia).
   rewrite Hz. now rewrite !andb_false_r.
Qed.
'''


def ctl_lift(design, module, use_mis=False):
    R = json.loads((ROOT / 'framework' / 'lift-roles' / f'{design}.json').read_text())
    prov = R['provider']
    src = (ROOT / prov['dir'] / prov['file']).read_text()
    W = R['wires']
    vw = R['var_wire']
    MISSRC = (ROOT / R['mis']['dir'] / R['mis']['file']).read_text() if use_mis else ''
    misreq = (' ' + R['mis']['namespace'] + '.' + R['mis']['module'].split('.')[1]) if use_mis else ''
    pre = (PRE.replace('@AST@', R['ast_require']).replace('@PROVIDERS@', prov['namespace'] + '.' + prov['module'].split('.')[1] + ' TmplLiftIsa.TmplLiftIsa' + misreq)
           .replace('@PROG@', R['program']).replace('@PROV@', prov['module']).replace('@ISAMOD@', 'TmplLiftIsa.TmplLiftIsa.TmplLiftIsa'))
    if use_mis:
        pre += 'Module Pm := ' + R['mis']['module'] + '.\n'
    L, ex = [], []
    rd = lambda r: f'(read_signal d {r}%nat)'
    L.append('Section ISA.\nContext {word : Interface.word 32} {BW : Bitwidth 32}.\nContext {Registers : map.map Decode.Register word} {Mem : map.map word byte}.\n'
             'Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.\nLocal Notation uw := word.unsigned.\n'
             'Local Notation reg := formal_register_word.')
    for c in isa.classes():
        n, g, k = c['name'], c['group'], c['kind']
        m = re.search(r'^Theorem ' + prov['thm'].format(C=n) + r' seed d \(w a b imm pc:Z\) : (.*)\.$', src, re.M)
        assert m, n
        parts = split_top(m.group(1), ' -> ')
        concl = parts[-1]
        hyps = parts[1:-1]          # after CombLFP
        assert parts[0].startswith('CombLFP')
        # data hyps = last 5 (w a b imm pc)
        dh = hyps[-5:]
        ch = hyps[:-5]
        mis_here = use_mis and c['kind'] in ('jal', 'jalr', 'branch')
        i238 = None
        if mis_here:
            Wm = R['mis']
            i238 = [i for i, h in enumerate(ch) if f"read_signal d {Wm['wire']}%nat" in h][0]
            mm_ = re.search(r'^Theorem ' + Wm['thm'].format(C=n) + r' seed d \(w a b imm pc:Z\) : (.*)\.$', MISSRC, re.M)
            mparts = split_top(mm_.group(1), ' -> ')
            assert mparts[1:-1][:-5] == ch[:i238] + ch[i238 + 1:], n
            mis_concl = split_top(mparts[-1], ' /\\ ')
            ch_full = ch
            ch = ch[:i238] + ch[i238 + 1:]
        HORD = ['w', 'a', 'b', 'pc', 'imm']
        for h, v in zip(dh, HORD):
            assert h.endswith(f'= {v}') and f'read_signal d {vw[v]}%nat' in h, (n, h)
        conj = split_top(concl, ' /\\ ')
        byw = {}
        for i, q in enumerate(conj):
            mm = re.search(r'read_signal d (\d+)%nat', q)
            byw[int(mm.group(1)) if mm else -1] = i
        names, bstr = binders(c)
        shift = n in ('Slli', 'Srli', 'Srai')
        use = USES(c)
        ins = f'(Decode.{n} {bstr})'
        regw = lambda r: f'(uw (reg s {r}))'
        A = regw('rs1' if g in ('OP', 'BRANCH') else 'rs')
        B = regw('rs2')
        IMM = 'b5' if shift else 'imm'
        IMMV = 'b5' if shift else '(norm 32 imm)'
        PC = '(uw (getPc s))'
        val = dict(w='w', a=A, b=B, imm=IMMV, pc=PC)
        # statement
        ctl_names = [f'h{i}' for i in range(len(ch))]
        hs = []
        if shift:
            hs += ['0 <= sh < 32', 'norm 5 b5 = sh']
        if k != 'branch':
            hs.append(f'rd = bitSlice w 7 12')
        for v in HORD:
            if use[v]:
                hs.append(f'norm 32 {rd(vw[v])} = {val[v]}')
        if k in ('jal', 'jalr', 'branch'):
            hs.append(f'LI.ipc s {ins} mod {4 if use_mis else 2} = 0')
        if k == 'jalr':
            hs.append('rs = 0')
        extra_names = []
        nm = iter(f'e{i}' for i in range(30))
        en = {}
        if shift:
            en['sh1'] = next(nm); en['sh2'] = next(nm)
        if k != 'branch':
            en['rd'] = next(nm)
        for v in HORD:
            if use[v]:
                en[v] = next(nm)
        if k in ('jal', 'jalr', 'branch'):
            en['al'] = next(nm)
        if k == 'jalr':
            en['x0'] = next(nm)
        bind = ' '.join(names) + (' b5' if shift else '') + ' w' + ('' if k != 'branch' else '')
        if k == 'branch':
            pass
        decl = f'Theorem {n}_lift seed d (s : FormalSpec.State) {bind} : CombLFP P seed d -> ' + ' -> '.join(ch + hs) + ' -> '
        ipc = f'(LI.ipc s {ins})'
        out = [conj[0].replace('ctl_' + n, 'Pv.ctl_' + n)]
        if k != 'branch':
            out.append(f'norm 5 {rd(W["rd"])} = rd')
        out.append(f'norm 32 {rd(W["next_pc"])} = {ipc}')
        if k in ('dataop',):
            out.append(f'norm 32 {rd(W["result"])} = uw (result_word s {ins})')
        elif k in ('jal', 'jalr'):
            out.append(f'norm 32 {rd(W["result"])} = uw (word.add (getPc s) (word.of_Z 4 : word))')
        out.append(f'norm 32 {rd(W["fetch_pc"])} = {ipc}')
        out.append(f'norm 7 {rd(W["fetch_word"])} = norm 7 (Z.shiftr {ipc} 2)')
        out.append(f'norm 1 {rd(W["fetch_invalid"])} = boolz (negb (Z.ltb {ipc} 512))')
        decl += ' /\\ '.join(f'({o})' if ' /\\ ' in o else o for o in out) + '.'
        L.append(decl)
        # proof
        call_args = []
        for v in R['vars']:
            call_args.append(val[v] if use[v] else f'(norm 32 {rd(vw[v])})')
        hcall = ['HL'] + (ctl_names[:i238] + ['H238'] + ctl_names[i238:] if mis_here else ctl_names)
        for v in HORD:
            hcall.append(en[v] if use[v] else 'eq_refl')
        intro = ['HL'] + ctl_names + ([en['sh1'], en['sh2']] if shift else []) + ([en['rd']] if k != 'branch' else []) + [en[v] for v in HORD if use[v]] + ([en['al']] if 'al' in en else []) + ([en['x0']] if 'x0' in en else [])
        P = [f'Proof. intros {" ".join(intro)}.']
        names_c = ['Hdec', 'Hrd', 'H243', 'Hres', 'H23', 'H18', 'H17']
        pat = []
        conj_names = {}
        for i, q in enumerate(conj):
            conj_names[i] = f'K{i}'
        if mis_here:
            datapart = [en[v] if use[v] else 'eq_refl' for v in HORD]
            P.append(f' destruct (Pm.{R["mis"]["thm"].format(C=n)} seed d {" ".join(call_args)} HL {" ".join(ctl_names)} {" ".join(datapart)}) as [_ K238].')
            if k == 'jal':
                P.append(f' assert (H238 : norm 1 {rd(R["mis"]["wire"])} = 0). {{ rewrite K238. rewrite norm_add_r. exact (bit1_m4 _ {en["al"]}). }}')
            elif k == 'jalr':
                P.append(f' assert (H238 : norm 1 {rd(R["mis"]["wire"])} = 0). {{ rewrite K238, {en["x0"]}, V.view_formal, V.view_zero, Z.add_0_l, norm_self. rewrite bit1_land. exact (bit1_m4 _ {en["al"]}). }}')
            else:
                cond0 = re.sub(r'\b(a|b)\b', lambda mm: A if mm.group(1) == 'a' else B, c['cond'])
                guard0 = f'(isa_branch_guard {ins} (reg s rs1) (reg s rs2))'
                P.append(f' assert (Ec0 : {cond0} = {guard0}) by exact (LI.boolz_bool _ _ (BR.bridge_{n} (reg s rs1) (reg s rs2) rs1 rs2 imm)).')
                P.append(f' assert (H238 : norm 1 {rd(R["mis"]["wire"])} = 0). {{ rewrite K238, Ec0. revert {en["al"]}. unfold LI.ipc. destruct {guard0}; intro Hal0; cbn in Hal0; [rewrite norm_add_r; exact (bit1_m4 _ Hal0) | reflexivity]. }}')
        P.append(f' pose proof (Pv.{prov["thm"].format(C=n)} seed d {" ".join(call_args)} {" ".join(hcall)}) as Kall.')
        pat_s = '[' + ' ['.join(conj_names[i] for i in range(len(conj) - 1)) + ' ' + conj_names[len(conj) - 1] + ']' * (len(conj) - 1)
        pat_s = '[K0 ' + ''.join(f'[K{i} ' for i in range(1, len(conj) - 1)) + f'K{len(conj) - 1}' + ']' * (len(conj) - 1)
        P.append(f' destruct Kall as {pat_s}.')
        iN, iR, iP, iS = byw[W['next_pc']], byw.get(W['rd']), byw[W['next_pc']], byw.get(W['result'])
        i23, i18, i17 = byw[W['fetch_pc']], byw[W['fetch_word']], byw[W['fetch_invalid']]
        sv = lambda t: re.sub(r'\b(w|a|b|imm|pc)\b', lambda mm: val[mm.group(1)], t)
        # Eipc : the RTL value norm 32 F equals ipc
        qF = conj[iN]
        F = sv(qF.split(' = ', 1)[1])            # 'norm 32 (...)'
        if k == 'dataop':
            P.append(f' assert (Eipc : {F} = {ipc}) by reflexivity.')
        elif k == 'jal':
            P.append(f' assert (Eipc : {F} = {ipc}).')
            P.append(f' {{ unfold LI.ipc. rewrite norm_add_r. apply clear0_even. apply LI.tb0_norm. exact ' + (f'(m4_m2 _ {en["al"]})' if use_mis else en["al"]) + '. }'.replace('LI.ipc. ', 'LI.ipc. ').replace('unfold LI.ipc', 'unfold LI.ipc'))
        elif k == 'jalr':
            P.append(f' assert (Eipc : {F} = {ipc}).')
            P.append(f' {{ unfold LI.ipc. rewrite {en["x0"]}, V.view_formal, V.view_zero. rewrite Z.add_0_l, norm_self. exact (LI.clear0_jalr imm). }}')
        else:
            cond = c['cond']
            cond = re.sub(r'\b(a|b)\b', lambda mm: A if mm.group(1) == 'a' else B, cond)
            guard = f'(isa_branch_guard {ins} (reg s rs1) (reg s rs2))'
            P.append(f' assert (Ec : {cond} = {guard}) by exact (LI.boolz_bool _ _ (BR.bridge_{n} (reg s rs1) (reg s rs2) rs1 rs2 imm)).')
            P.append(f' rewrite Ec in K{iN}, K{i23}, K{i18}, K{i17}.')
            P.append(f' assert (Eipc : {F.replace(cond, guard) if cond in F else "?"} = {ipc}).')
            P.append(f' {{ revert {en["al"]}. unfold LI.ipc. destruct {guard}; intro Hal; cbn in Hal; [rewrite norm_add_r; apply clear0_even; apply LI.tb0_norm; exact ' + ('(m4_m2 _ Hal)' if use_mis else 'Hal') + ' | reflexivity]. }')
        # build final conjunction
        fin = []
        for i, q in enumerate(conj):
            if i == 0:
                fin.append('K0')
            elif i == iR and k == 'branch':
                continue
            elif i == iR:
                fin.append(f'(eq_trans K{i} (eq_trans (f_equal (norm 5) {en["rd"]}) (eq_trans (f_equal (norm 5) (eq_refl _)) (eq_refl _))))' if False else 'RDPROOF')
            elif i == iN or i == i23:
                fin.append(f'(eq_trans K{i} Eipc)')
            elif i == iS:
                fin.append('RESPROOF')
            elif i == i18:
                fin.append(f'(eq_trans K{i} (f_equal (fun x => norm 7 (Z.shiftr x 2)) Eipc))')
            elif i == i17:
                fin.append(f'(eq_trans K{i} (f_equal (fun x => boolz (negb (Z.ltb x 512))) Eipc))')
        # rd proof
        if k != 'branch':
            rdp = f'(eq_trans K{iR} (eq_trans (f_equal (norm 5) (eq_sym (f_equal (fun z => Z.shiftr z 7) eq_refl))) (RDLEMMA)))'
            rdp = f'(RDF _ _ _ K{iR} {en["rd"]})'
        if iS is not None:
            if k == 'dataop':
                if shift:
                    br = f'(BR.bridge_{n} s {" ".join(names)} b5 {en["sh1"]} {en["sh2"]})'
                else:
                    br = f'(BR.bridge_{n} s {bstr})'
                resp = f'(eq_trans K{iS} {br})'
            else:
                resp = f'(eq_trans K{iS} (eq_sym (V.uw_link (getPc s))))'
        out_fin = []
        for f in fin:
            if f == 'RDPROOF':
                out_fin.append(rdp)
            elif f == 'RESPROOF':
                out_fin.append(resp)
            else:
                out_fin.append(f)
        P.append(' ' + 'refine (conj ' + ' (conj '.join(out_fin[:-1]) + ' ' + out_fin[-1] + ')' * (len(out_fin) - 1) + '.')
        P.append(' Qed.')
        # rd helper inline: replace RDF
        txt = '\n'.join(P)
        txt = txt.replace('RDF', 'LiftRd')
        L.append(txt)
        ex.append(f'{module}.{n}_lift')
    L.append('End ISA.')
    helpers = ('Lemma LiftRd w rd z : z = norm 5 (Z.shiftr w 7) -> rd = bitSlice w 7 12 -> z = rd.\n'
               'Proof. intros H1 H2. rewrite H1, H2. rewrite (V.bs_norm w 7 12) by lia. reflexivity. Qed.\n')
    if use_mis:
        helpers += HELP2
    text = (f'(** {design}: ISA lift of the provider facts per class (tools/cpu_tmpl_lift.py --kinds lift, roles framework/lift-roles/{design}.json). '
            f'proof_author: {AUTHOR}; external_llm_api_calls=0. *)\n' + pre + helpers + f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\n'
            + 'Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.\n' + ''.join(f'Print Assumptions {e}.\n' for e in ex))
    return text, ex


def build(design, kinds, module):
    R = json.loads((ROOT / 'framework' / 'lift-roles' / f'{design}.json').read_text())
    if kinds == 'lift' and R['kind'] == 'ctl_provider':
        return ctl_lift(design, module)
    if kinds == 'lift2' and R['kind'] == 'ctl_provider':
        return ctl_lift(design, module, use_mis=True)
    if kinds == 'lift' and R['kind'] == 'ex_provider':
        return ex_lift(design, module)
    if kinds == 'lift' and R['kind'] == 'wire_provider':
        return wire_lift(design, module)
    raise SystemExit(f'unsupported: {design} {kinds}')


# ---------------------------------------------------------------- ex_provider (srv32 style: result / next-pc / branch scenarios / operand ports)
PEND = r'''Definition pend (we rd v : Z) (f : Z -> Z) : Z -> Z := fun i => if (we =? 1) && (i =? rd) && negb (rd =? 0) then v else f i.
Definition fwd_we (f wa : Z) : Z := if (f =? 0) && (wa =? 1) then 1 else 0.
Definition RFV (bank : Z) (view : Z -> Z) : Prop := view 0 = 0 /\ forall r, 1 <= r < 32 -> view r = norm 32 (Z.shiftr bank (32 * norm 5 (r - 1))).
Lemma pend_sel view bank we wd v s X : RFV bank view -> 0 <= s < 32 ->
 (s = 0 -> X = 0) -> (s <> 0 -> we = 1 -> wd = s -> X = v) ->
 (s <> 0 -> ~ (we = 1 /\ wd = s) -> X = norm 32 (Z.shiftr bank (32 * norm 5 (s - 1)))) -> X = pend we wd v view s.
Proof. intros [Hv0 Hv] Hr H0 H1 H2. unfold pend.
 destruct (Z.eq_dec s 0) as [Hs|Hs].
 - rewrite (H0 Hs). subst s. rewrite Hv0.
   destruct (Z.eq_dec wd 0) as [->|Hwd].
   + cbn. rewrite andb_false_r. reflexivity.
   + assert (E : (0 =? wd) = false) by (apply Z.eqb_neq; lia). rewrite E. cbn. rewrite andb_false_r. reflexivity.
 - destruct ((we =? 1) && (s =? wd) && negb (wd =? 0)) eqn:E.
   + rewrite !andb_true_iff in E. destruct E as [[E1 E2] E3]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
     exact (H1 Hs E1 (eq_sym E2)).
   + rewrite (Hv s ltac:(lia)). apply H2; [exact Hs|]. intros [A B]. subst wd. rewrite A in E.
     assert (H : s =? s = true) by apply Z.eqb_refl. assert (H3 : s =? 0 = false) by (apply Z.eqb_neq; lia).
     rewrite H, H3 in E. discriminate.
Qed.
'''


def get_thm(src, name):
    m = re.search(r'^Theorem ' + re.escape(name) + r' seed d (.*?) ?: (CombLFP .*)\.$', src, re.M)
    assert m, name
    binders = re.findall(r'\((\w+):Z\)', m.group(1))
    parts = split_top(m.group(2), ' -> ')
    return binders, parts[1:-1], parts[-1]


def ex_lift(design, module):
    R = json.loads((ROOT / 'framework' / 'lift-roles' / f'{design}.json').read_text())
    prov = R['provider']
    src = (ROOT / prov['dir'] / prov['file']).read_text()
    W = R['wires']
    T = R['thm']
    pre = (PRE.replace('@AST@', R['ast_require']).replace('@PROVIDERS@', prov['namespace'] + '.' + prov['module'].split('.')[1] + ' TmplLiftIsa.TmplLiftIsa')
           .replace('@PROG@', R['program']).replace('@PROV@', prov['module']).replace('@ISAMOD@', 'TmplLiftIsa.TmplLiftIsa.TmplLiftIsa'))
    rd = lambda r: f'(read_signal d {r}%nat)'
    L, ex = [], []
    L.append('Section ISA.\nContext {word : Interface.word 32} {BW : Bitwidth 32}.\nContext {Registers : map.map Decode.Register word} {Mem : map.map word byte}.\n'
             'Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.\nLocal Notation uw := word.unsigned.\n'
             'Local Notation reg := formal_register_word.')
    # ---- operand ports -> pending-write view
    for port in R['operand_ports']:
        nm = port['name']
        bz, hz, cz = get_thm(src, port['zero'])
        bf, hf, cf = get_thm(src, port['fwd'])
        bb, hb, cb = get_thm(src, port['bank'])
        pre8 = hz[:8]          # selection / forwarding / bank register facts (same text in the three scenario theorems)
        assert hf[:8] == pre8 and hb[:8] == pre8
        names = ['s', 'f', 'wa', 'wd', 'wm', 'wr', 'wres', 'bank']
        assert bz == names, bz
        hn = [f'h{i}' for i in range(8)]
        out = rd(port['out'])
        L.append(f'Theorem {nm}_pend seed d (view : Z -> Z) (s f wa wd wm wr wres bank : Z) : CombLFP P seed d -> {" -> ".join(pre8)} -> RFV bank view -> 0 <= s < 32 ->\n'
                 f' norm 32 {out} = pend (fwd_we f wa) wd (norm 32 (if wm =? 0 then wres else wr)) view s.')
        L.append(f'Proof. intros HL {" ".join(hn)} HV HR. apply (pend_sel view bank (fwd_we f wa) wd _ s _ HV HR).\n'
                 f' - intro Hs. exact (Pv.{port["zero"]} seed d s f wa wd wm wr wres bank HL {" ".join(hn)} Hs).\n'
                 f' - intros Hs Hw Hd. unfold fwd_we in Hw. destruct (f =? 0) eqn:E1; destruct (wa =? 1) eqn:E2; cbn in Hw; try discriminate. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.\n'
                 f'   exact (Pv.{port["fwd"]} seed d s f wa wd wm wr wres bank HL {" ".join(hn)} Hs E1 E2 Hd).\n'
                 f' - intros Hs Hn. exact (Pv.{port["bank"]} seed d s f wa wd wm wr wres bank HL {" ".join(hn)} Hs ltac:(intros [A [B C]]; apply Hn; split; [unfold fwd_we; rewrite A, B; reflexivity | exact C])).\nQed.')
        ex.append(f'{module}.{nm}_pend')
    # ---- per class
    for c in isa.classes():
        n, g, k = c['name'], c['group'], c['kind']
        names, bstr = binders(c)
        shift = n in ('Slli', 'Srli', 'Srai')
        ins = f'(Decode.{n} {bstr})'
        regw = lambda r: f'(uw (reg s {r}))'
        A = regw('rs1' if g in ('OP', 'BRANCH') else 'rs')
        IMMV = 'b5' if shift else '(norm 32 imm)'
        B = regw('rs2') if g in ('OP', 'BRANCH') else IMMV
        PC = '(uw (getPc s))'
        base = dict(a=A, b=B, pc=PC, imm=IMMV, fe='fe')
        ipc = f'(LI.ipc s {ins})'
        shpre = ['0 <= sh < 32', 'norm 5 b5 = sh'] if shift else []
        bind = '(' + ' '.join(names) + (' b5' if shift else '') + ' : Z)'

        def split_hyps(hyps, bnd):
            dh = [h for h in hyps if any(re.search(r'= ' + v + r'$', h) for v in bnd)]
            return [h for h in hyps if h not in dh], dh

        def var_of(h, bnd):
            return [v for v in bnd if re.search(r'= ' + v + r'$', h)][0]

        # ---- result
        if k != 'branch':
            bnd, hyps, concl = get_thm(src, T['result'].format(C=n))
            ch, dh = split_hyps(hyps, bnd)
            val = {v: base[v] for v in bnd}
            dh2 = [re.sub(r'= (\w+)$', lambda m: '= ' + val[m.group(1)], h) for h in dh]
            ens = [f'e{i}' for i in range(len(dh))]
            cn = [f'h{i}' for i in range(len(ch))]
            res = f'uw (result_word s {ins})' if k == 'dataop' else 'uw (word.add (getPc s) (word.of_Z 4 : word))'
            L.append(f'Theorem {n}_lift_result seed d (s : FormalSpec.State) {bind} : CombLFP P seed d -> {" -> ".join(ch + shpre + dh2)} -> norm 32 {rd(W["result"])} = {res}.')
            order = {h: e for h, e in zip(dh, ens)}
            call = ' '.join(val[v] for v in bnd)
            # arguments of the provider in its hypothesis order
            hargs = []
            ci = iter(cn); di = iter(ens)
            for h in hyps:
                hargs.append(next(di) if h in dh else next(ci))
            if k == 'dataop':
                br = f'BR.bridge_{n} s {bstr}' + (' b5 e_sh1 e_sh2' if shift else '')
                fin = f'exact ({br})'
            else:
                fin = 'exact (eq_sym (V.uw_link (getPc s)))'
            intro = ['HL'] + cn + (['e_sh1', 'e_sh2'] if shift else []) + ens
            L.append(f'Proof. intros {" ".join(intro)}. rewrite (Pv.{T["result"].format(C=n)} seed d {call} HL {" ".join(hargs)}). {fin}. Qed.')
            ex.append(f'{module}.{n}_lift_result')
        # ---- next pc / taken
        if k in ('jal', 'jalr'):
            bnd, hyps, concl = get_thm(src, T['next'].format(C=n))
            ch, dh = split_hyps(hyps, bnd)
            val = {v: base[v] for v in bnd}
            dh2 = [re.sub(r'= (\w+)$', lambda m: '= ' + val[m.group(1)], h) for h in dh]
            ens = [f'e{i}' for i in range(len(dh))]
            cn = [f'h{i}' for i in range(len(ch))]
            conj = split_top(concl, ' /\\ ')
            extra = ['LI.ipc s ' + ins + ' mod 2 = 0'] + (['rs = 0'] if k == 'jalr' else [])
            outs = [f'norm 32 {rd(W["next_pc"])} = {ipc}'] + conj[1:]
            L.append(f'Theorem {n}_lift_next seed d (s : FormalSpec.State) {bind} : CombLFP P seed d -> {" -> ".join(ch + dh2 + extra)} -> {AND.join(outs)}.')
            call = ' '.join(val[v] for v in bnd)
            hargs = []
            ci = iter(cn); di = iter(ens)
            for h in hyps:
                hargs.append(next(di) if h in dh else next(ci))
            intro = ['HL'] + cn + ens + ['eal'] + (['ex0'] if k == 'jalr' else [])
            if k == 'jal':
                eq = ('unfold LI.ipc. rewrite norm_add_r. apply clear0_even. apply LI.tb0_norm. exact eal.')
                F = split_top(conj[0], ' = ')[1] if False else conj[0].split(' = ', 1)[1]
                F = re.sub(r'\b(pc|imm|a)\b', lambda m: val[m.group(1)], F)
            else:
                eq = 'unfold LI.ipc. rewrite ex0, V.view_formal, V.view_zero. rewrite Z.add_0_l, norm_self. exact (LI.clear0_jalr imm).'
                F = re.sub(r'\b(pc|imm|a)\b', lambda m: val[m.group(1)], conj[0].split(' = ', 1)[1])
            L.append(f'Proof. intros {" ".join(intro)}. destruct (Pv.{T["next"].format(C=n)} seed d {call} HL {" ".join(hargs)}) as [K0 K1].\n'
                     f' assert (Eipc : {F} = {ipc}). {{ {eq} }}\n refine (conj (eq_trans K0 Eipc) K1). Qed.')
            ex.append(f'{module}.{n}_lift_next')
        if k == 'branch':
            bt, ht, ct_ = get_thm(src, T['branch_t'].format(C=n))
            bn, hn_, cn_ = get_thm(src, T['branch_n'].format(C=n))
            assert bt == bn and ht[:-1] == hn_[:-1], n
            bnd = bt
            ch, dh = split_hyps(ht[:-1], bnd)
            val = {v: base[v] for v in bnd}
            dh2 = [re.sub(r'= (\w+)$', lambda m: '= ' + val[m.group(1)], h) for h in dh]
            ens = [f'e{i}' for i in range(len(dh))]
            cn = [f'h{i}' for i in range(len(ch))]
            condt = ht[-1][:-len(' = true')]
            assert ht[-1].endswith(' = true') and hn_[-1] == condt + ' = false'
            cond = re.sub(r'\b(a|b)\b', lambda m: val[m.group(1)], condt)
            guard = f'(isa_branch_guard {ins} (reg s rs1) (reg s rs2))'
            ft = [x for x in bnd]
            call = ' '.join(val[v] for v in bnd)
            hargs = []
            ci = iter(cn); di = iter(ens)
            for h in ht[:-1]:
                hargs.append(next(di) if h in dh else next(ci))
            fe = [v for v in bnd if v == 'fe']
            Ft = re.sub(r'\b(pc|imm)\b', lambda m: val[m.group(1)], split_top(ct_, ' /\\ ')[0].split(' = ', 1)[1])
            Fn = split_top(cn_, ' /\\ ')[0].split(' = ', 1)[1]
            L.append(f'Theorem {n}_lift_next seed d (s : FormalSpec.State) {bind} (fe : Z) : CombLFP P seed d -> {" -> ".join(ch + dh2)} ->\n'
                     f' norm 1 {rd(W["taken"])} = boolz {guard} /\\ ({guard} = true -> norm 32 {rd(W["next_pc"])} = {ipc}) /\\ ({guard} = false -> norm 32 {rd(W["next_pc"])} = {Fn}).')
            L.append(f'Proof. intros HL {" ".join(cn + ens)}.\n'
                     f' assert (Ec : {cond} = {guard}) by exact (LI.boolz_bool _ _ (BR.bridge_{n} (reg s rs1) (reg s rs2) rs1 rs2 imm)).\n'
                     f' destruct {guard} eqn:Eg.\n'
                     f' - destruct (Pv.{T["branch_t"].format(C=n)} seed d {call} HL {" ".join(hargs)} Ec) as [K0 K1].\n'
                     f'   split; [exact K1 | split; [intros _; unfold LI.ipc; rewrite Eg; rewrite K0; apply norm_add_r | intro H; discriminate H]].\n'
                     f' - destruct (Pv.{T["branch_n"].format(C=n)} seed d {call} HL {" ".join(hargs)} Ec) as [K0 K1].\n'
                     f'   split; [exact K1 | split; [intro H; discriminate H | intros _; exact K0]].\nQed.')
            ex.append(f'{module}.{n}_lift_next')
    # ---- trap / misaligned = 0 from the checked program
    bnd, hyps, concl = get_thm(src, T['trap'])
    pc_ = f'PD.AtProgram words (Z.to_nat (t / 4)) s'
    hn = [f'h{i}' for i in range(len(hyps))]
    npi = [i for i, h in enumerate(hyps) if h.startswith('norm 32 ' + rd(W['next_pc']))]
    assert len(npi) == 1
    hy2 = list(hyps)
    ci = npi[0]
    hy2[ci] = f'norm 32 {rd(W["next_pc"])} = uw (getPc y)'
    # drop the premise norm 2 np = 0 (derived from the program domain)
    j2 = [i for i, h in enumerate(hyps) if h == 'norm 2 np = 0']
    assert len(j2) == 1
    keep = [h for i, h in enumerate(hy2) if i != j2[0]]
    args = ' '.join(['(uw (getPc y))' if v == 'np' else v for v in bnd])
    hargs = ' '.join('Hnp2' if i == j2[0] else hn[i] for i in range(len(hyps)))
    keepn = ' '.join(hn[i] for i in range(len(hyps)) if i != j2[0])
    L.append(f'Theorem trap_lift seed d (s y : FormalSpec.State) words t {" ".join(v for v in bnd if v != "np")} : CombLFP P seed d -> {" -> ".join(keep)} ->\n'
             f' PD.check_program words = true -> PD.AtProgram words (Z.to_nat (t / 4)) s -> LI.J.checked_pc_effect t s = Some y -> {concl}.')
    L.append(f'Proof. intros HL {keepn} HC HAt HE. destruct (LI.isa_pc_ok words HC t s y HAt HE) as [H4 _].\n'
             f' assert (Hnp2 : norm 2 (uw (getPc y)) = 0). {{ rewrite ExtendedSVBankAlignment.norm_mod. change (2 ^ Z.of_nat 2) with 4. exact H4. }}\n'
             f' exact (Pv.{T["trap"]} seed d {args} HL {hargs}). Qed.'.replace('HL ' + hargs, 'HL ' + hargs))
    ex.append(f'{module}.trap_lift')
    L.append('End ISA.')
    text = (f'(** {design}: ISA lift of the provider facts (tools/cpu_tmpl_lift.py --kinds lift, roles framework/lift-roles/{design}.json). '
            f'proof_author: {AUTHOR}; external_llm_api_calls=0. *)\n' + pre + 'Module PD := Ex.External.CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.\n'
            + f'Module {module}.\n' + PEND + '\n'.join(L) + f'\nEnd {module}.\n'
            + 'Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.\n' + ''.join(f'Print Assumptions {e}.\n' for e in ex))
    return text, ex


# ---------------------------------------------------------------- wire_provider (Bzeeno style: provider `<C>_ex d` states the result wire in terms of operand WIRES)
def wire_lift(design, module):
    """Regression of the Bzeeno `<C>_ex_isa` statements: operands are wire reads; the lift substitutes the ISA values.
    The ExPrem_C / <C>_ex of the accepted provider are consumed; the generated statements must equal the accepted ones."""
    R = json.loads((ROOT / 'framework' / 'lift-roles' / f'{design}.json').read_text())
    W = R['wires']
    rd = lambda r: f'(read_signal d {r}%nat)'
    out = []
    ex = []
    for c in isa.classes():
        n, g, k = c['name'], c['group'], c['kind']
        if k == 'branch':
            continue
        sl = n in ('Slt', 'Sltu', 'Slti', 'Sltiu')
        sh = n in ('Slli', 'Srli', 'Srai')
        reg = lambda r: f'(uw (reg s {r}))'
        if k in ('jal', 'jalr'):
            stmt = (f'Theorem {n}_ex_isa seed d s : CombLFP P seed d -> ExPrem_{n} d -> norm 32 {rd(W["link"])} = uw (word.add (getPc s) (word.of_Z 4 : word)) -> norm 32 {rd(W["result"])} = uw (word.add (getPc s) (word.of_Z 4 : word)).')
            prf = f'Proof. intros HL HP hl. rewrite ({n}_ex seed d HL HP). rewrite hl. apply CPUClassValueBridge.norm_uw. Qed.'
            out += [stmt, prf]; ex.append(f'{module}.{n}_ex_isa'); continue
        if g == 'OP':
            binders, hy, names, rw = 'rd rs1 rs2', f'norm 32 {rd(W["a"])} = uw (reg s rs1) -> norm 32 {rd(W["b_rs2"])} = uw (reg s rs2)', 'ha hb', 'rewrite ha, hb.'
        elif n == 'Lui':
            binders, hy, names, rw = 'rd imm', f'norm 32 {rd(W["b_imm"])} = norm 32 imm', 'hb', 'rewrite hb.'
        elif n == 'Auipc':
            binders, hy, names, rw = 'rd imm', f'norm 32 {rd(W["pc"])} = uw (getPc s) -> norm 32 {rd(W["b_imm"])} = norm 32 imm', 'ha hb', 'rewrite ha, hb.'
        elif sh:
            binders, hy, names, rw = 'rd rs sh b', f'norm 32 {rd(W["a"])} = uw (reg s rs) -> norm 32 {rd(W["b_imm"])} = b -> 0 <= sh < 32 -> norm 5 b = sh', 'ha hb h1 h2', 'rewrite ha, hb.'
        else:
            binders, hy, names, rw = 'rd rs imm', f'norm 32 {rd(W["a"])} = uw (reg s rs) -> norm 32 {rd(W["b_imm"])} = norm 32 imm', 'ha hb', 'rewrite ha, hb.'
        args = {'rd rs1 rs2': 'rd rs1 rs2', 'rd imm': 'rd imm', 'rd rs sh b': 'rd rs sh', 'rd rs imm': 'rd rs imm'}[binders]
        if sl:
            reg1 = '(uw (reg s rs1))' if g == 'OP' else '(uw (reg s rs))'
            b2 = '(uw (reg s rs2))' if g == 'OP' else '(norm 32 imm)'
            val = re.sub(r'\b(a|b)\b', lambda m: reg1 if m.group(1) == 'a' else b2, c['value'])
            hy = f'norm 1 {rd(W["slt_bit"])} = {val}'; names, rw = 'hl', 'rewrite hl.'
        out.append(f'Theorem {n}_ex_isa seed d s {binders} : CombLFP P seed d -> ExPrem_{n} d -> {hy} -> norm 32 {rd(W["result"])} = uw (result_word s (Decode.{n} {args})).')
        br = f'CPUClassValueBridge.bridge_{n} s {args}' + (' b h1 h2' if sh else '')
        out.append(f'Proof. intros HL HP {names}. rewrite ({n}_ex seed d HL HP). {rw} exact ({br}). Qed.')
        ex.append(f'{module}.{n}_ex_isa')
    return '\n'.join(out), ex


def regress_bzeeno():
    R = json.loads((ROOT / 'framework' / 'lift-roles' / 'bzeeno.json').read_text())
    t, ex = wire_lift('bzeeno', 'X')
    prov = R['provider']
    acc = (ROOT / prov['dir'] / prov['file']).read_text().splitlines()
    accd = {}
    for i, l in enumerate(acc):
        m = re.match(r'Theorem (\w+_ex_isa) ', l)
        if m:
            accd[m.group(1)] = (l, acc[i + 1])
    gen = t.splitlines()
    bad = []
    for i in range(0, len(gen), 2):
        name = re.match(r'Theorem (\w+_ex_isa)', gen[i]).group(1)
        if accd.get(name) != (gen[i], gen[i + 1]):
            bad.append(name)
    print(f'bzeeno regression: {len(gen) // 2} generated, {len(bad)} differ from {prov["dir"]}: {bad}')
    return 1 if bad else 0


def audit_roles(design):
    """Validate framework/lift-roles/<design>.json: provider dirs exist, the module is the one in the dir's report, theorem patterns are present."""
    R = json.loads((ROOT / 'framework' / 'lift-roles' / f'{design}.json').read_text())
    provs = R.get('providers') or {'provider': R['provider']}
    bad = 0
    for name, p in provs.items():
        d = ROOT / p['dir']
        if not (d / 'report.json').exists():
            print(f'[{name}] MISSING result dir {p["dir"]}'); bad += 1; continue
        rep = json.loads((d / 'report.json').read_text())
        ok = rep.get('module') == '.'.join(p['module'].split('.')[:2])
        text = ''.join(f.read_text() for f in d.glob('*.v'))
        thm = p.get('thm')
        thms = [thm] if isinstance(thm, str) else (thm or [])
        found = []
        for t in thms:
            if '{C}' in t:
                found.append(f'{sum(1 for c in isa.classes() if re.search(chr(94) + "Theorem " + re.escape(t.format(C=c["name"])) + " ", text, re.M))}/29 classes')
            else:
                found.append('present' if re.search(r'^Theorem ' + re.escape(t) + r' ', text, re.M) else 'ABSENT')
        acc = rep.get('accepted') or rep.get('coqc_accepted')
        print(f'[{name}] {p["dir"]}: module {"ok" if ok else "MISMATCH " + str(rep.get("module"))}, coqc_accepted={acc}, theorems {found}')
        bad += (not ok) + (not acc)
    print(f'design {design}: kind {R["kind"]}, lift_ready={R.get("lift_ready", True)}')
    for o in R.get('lift_obligations', []):
        print(f'  obligation {o["id"]}: {o["what"]}  [needs: {o["needs"]}]')
    return 1 if bad else 0
