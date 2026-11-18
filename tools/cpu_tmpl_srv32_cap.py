#!/usr/bin/env python3
"""srv32 capture (decode) facts per ISA class: after the rising edge, the ex_* flag registers captured by process 4 from the
instruction word `inst` (233) hold the class values, given the slices opcode / funct3 / funct7 (/ bit 30) of the word.
Per class one theorem  rise hyps -> resetb = 1 -> if_stall = 0 -> norm 32 inst = w -> slice premises -> conjunction of
norm w_R (read (PhaseSemantics P ev pre) R) = v_R ; proof: `rise_R` (stage layer) + ExtendedSVSymExec.xeval under facts keyed by the
slices (symbolic facts for slices the class does not determine).  The expected values are the determined flags found by sampling the
capture decode (cpu_tmpl_srv32_ex.flag_values) plus ex_illegal = 0; Coq checks them by computation.
Untrusted generator.  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import argparse
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_isa_classes as isa
import cpu_tmpl_srv32_ex as X

STAGE = 'TmplSrv32Stage.Srv32TmplStage.Srv32TmplStage'
EDGE = 'TmplSrv32Edge.Srv32TmplEdge.Srv32TmplEdge'
REG = dict(memwr=257, jal=266, jalr=267, lui=264, auipc=265, csr=262, mul=288, alu=261, alu_op=255, subtype=256, branch=268, imm_sel=251)
WIDTH = dict(alu_op=3)
ILLEGAL = 279
INST = '(EVar 32%nat 233%nat)'
HDR = """From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVSeqTree Srv32.Srv32AST @STAGE_MOD@ @EDGE_MOD@.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVSeqTree Srv32AST.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics phase_driven_state.
"""


def class_text(c, regs_override=None, proc=4, suffix='cap'):
    n, opc, f3, f7 = c['name'], c['opcode'], c['funct3'], c['funct7']
    if n in ('Slli', 'Srli', 'Srai'):
        f7 = 32 if n == 'Srai' else 0
    fv = X.flag_values(c)
    regs = [(REG[k], WIDTH.get(k, 1), v) for k, v in fv.items() if k in REG] + [(ILLEGAL, 1, 0)]
    if regs_override is not None:
        regs = regs_override
    import os
    if os.environ.get('CAP_REGS') and regs_override is None:
        regs = [x for x in regs if str(x[0]) in os.environ['CAP_REGS'].split(',')]
    sl = lambda lsb, w: f'(ESel {w}%nat {INST} (EConst 5%nat {lsb}))'
    nx = lambda lsb, w: f'norm {w} (Z.shiftr w {lsb})'
    b30 = None if f7 is None else (f7 >> 5) & 1
    # slices: (lsb, width, determined value or None, variable name)
    slices = [(0, 7, opc, None), (12, 3, f3, 'f3'), (25, 7, f7, 'f7'), (30, 1, b30, 'b30')]
    params = [v for (_, _, val, v) in slices if val is None]
    facts = [('(EVar 1%nat 19%nat)', '1', 'cbn [eval_expr]; exact Hrs'), ('(EVar 1%nat 236%nat)', '0', 'cbn [eval_expr]; exact Hif')]
    prem = []
    for k, (lsb, w, val, var) in enumerate(slices):
        hn = f'hx{k}'
        prem.append((hn, f'{nx(lsb, w)} = {val if val is not None else var}'))
        facts.append((sl(lsb, w), str(val) if val is not None else var,
                      f'cbn [eval_expr]; rewrite hw; replace (norm 5 {lsb}) with {lsb} by reflexivity; exact {hn}'))
    if b30 is None and any(r == REG['subtype'] for r, _, _ in regs):
        # ex_subtype = inst[30] && !(opcode == ARITHI && funct3 == ADD): the class (Addi) fixes the second factor to 0 although bit 30
        # is free; xeval needs the whole conjunction as a fact (Z.land evaluates its first argument first)
        rhs = ('(EBinary 1%nat BAnd (ESel 1%nat (EVar 32%nat 233%nat) (EConst 5%nat 30)) (EUnary 1%nat UNot (EBinary 1%nat BAnd '
               '(EBinary 1%nat BEq (EConst 7%nat 19) (ESel 7%nat (EVar 32%nat 233%nat) (EConst 5%nat 0))) '
               '(EBinary 1%nat BEq (EConst 3%nat 0) (ESel 3%nat (EVar 32%nat 233%nat) (EConst 5%nat 12))))))')
        facts.append((rhs, '0', 'cbn [eval_expr]; rewrite hw; replace (norm 5 30) with 30 by reflexivity; replace (norm 5 0) with 0 by reflexivity; '
                                'replace (norm 5 12) with 12 by reflexivity; rewrite hx0, hx1; generalize (norm 1 (Z.shiftr w 30)) as ib; intro ib; '
                                'rewrite Z.land_comm; vm_compute; reflexivity'))
    fx = '' if suffix == 'cap' else '_' + suffix
    L = [f'Definition facts_{n}{fx} ({" ".join(params) + " : Z" if params else "_u : unit"}) : Facts := [' + '; '.join(f'({e}, {z})' for e, z, _ in facts) + '].']
    fcall = f'(facts_{n}{fx} {" ".join(params) if params else "tt"})'
    concl = ' /\\ '.join(f'norm {w}%nat (read_signal (PhaseSemantics P ev pre) {r}%nat) = {v}' for r, w, v in regs)
    binders = 'ev pre seed (w : Z)' + (' (' + ' '.join(params) + ' : Z)' if params else '')
    hyps = ('changed_signal ev = 0%nat -> new_value ev = 1 -> read_signal pre 0%nat = 0 -> read_signal pre 1%nat = 1 -> ' + f'{EDGE}.NetWords pre -> CombLFP P seed pre -> '
            'CombLFP P (write_signal pre (changed_signal ev) (new_value ev)) (phase_driven_state P ev pre) -> '
            'norm 1 (read_signal (phase_driven_state P ev pre) 19%nat) = 1 -> norm 1 (read_signal (phase_driven_state P ev pre) 236%nat) = 0 -> '
            'norm 32 (read_signal (phase_driven_state P ev pre) 233%nat) = w -> ' + ''.join(f'{p} -> ' for _, p in prem))
    L.append(f'Theorem {n}_{suffix} {binders} : {hyps}{concl}.')
    pf = [f'Proof. intros Hc Hv H0 H1 HW HL HD Hrs Hif hw {" ".join(h for h, _ in prem)}.']
    pf.append(f' assert (HF : FactsHold (phase_driven_state P ev pre) {fcall}).')
    pf.append(f' {{ intros e z HI. cbn [facts_{n}{fx} In] in HI.')
    for k, (e, z, pr) in enumerate(facts):
        pf.append(f'   destruct HI as [HI|HI]; [injection HI as <- <-; {pr}|].')
    pf.append('   contradiction. }')
    pf.append(' repeat split.')
    for r, w, v in regs:
        pf.append(f'  - pose proof ({STAGE}.rise_{r} ev pre seed Hc Hv H0 H1 HW HL HD) as RR. '
                  f'assert (XX : xeval {fcall} [] (texpr {w}%nat {r}%nat ({STAGE}.tree_of process_{proc})) = Some {v}) by (vm_compute; reflexivity). '
                  f'rewrite RR, (xeval_sound {fcall} (phase_driven_state P ev pre) HF _ [] _ {v} (agree_nil _) XX). vm_compute; reflexivity.')
    pf.append('Qed.')
    return '\n'.join(L + pf)


def text(module, names='all'):
    cl = [c for c in isa.classes() if names == 'all' or c['name'] in names.split(',')]
    body = ['Notation P := srv32_program (only parsing).'] + [class_text(c) for c in cl]
    ex = [f'{module}.{c["name"]}_cap' for c in cl]
    hdr = HDR.replace('@STAGE_MOD@', STAGE.rsplit('.', 1)[0]).replace('@EDGE_MOD@', EDGE.rsplit('.', 1)[0])
    t = (f'(** srv32: capture (decode) facts per class (tools/cpu_tmpl_srv32_cap.py). proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + hdr
         + f'Module {module}.\n' + '\n'.join(body) + f'\nEnd {module}.\n' + ''.join(f'Print Assumptions {e}.\n' for e in ex))
    return t, ex


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--classes', default='all')
    ap.add_argument('--module', default='Srv32Cap')
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    t, ex = text(a.module, a.classes)
    Path(a.out).write_text(t)
    print(a.out, len(t.splitlines()))
