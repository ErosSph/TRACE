#!/usr/bin/env python3
"""Execute-stage ALU result per class (angelo5fix process 182, the ALU, which reads its own intermediates 268/269 and is therefore out of reach of pex).
Overlay engine (Lang/ExtendedSVSymExecOverlay), as for the decoder immediates (cpu_tmpl_a5dec.py): per class the facts are
  i_alu (210) = packed decoder ALU flags, i_opcode (221) = packed opcode flags   (the class constants of the decoder, dec a3 `outs_C`),
ox_run derives the one-hot flags 243..256 / 257..267, the overlay gives `norm 32 (read y_d) = norm 32 (eval alu_C)`.
Roles used: template_roles.alu = {fact_regs: [i_alu, i_opcode], result: y_d, process}. Untrusted generator; Coq checks everything.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import argparse, json, re, subprocess, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles
import cpu_tmpl_edge as E
import cpu_isa_classes as isa
import cpu_tmpl_a5dec as D

ALU_PROC, ALU_RES, IALU, IOPC = 182, 270, (210, 14), (221, 11)
DEC_DIR = 'results/r-tmpl-a5-dec-20261104-a3'


def dec_consts():
    txt = Path(DEC_DIR, 'A5TmplDec.v').read_text()
    res = {}
    for m in re.finditer(r'Definition outs_(\w+):list\(\(signal\*nat\)\*Z\):=\[(.*?)\]\.', txt):
        res[m.group(1)] = {int(a): int(z) for a, z in re.findall(r'\(\((\d+)%nat,\d+%nat\),(\d+)\)', m.group(2))}
    return res


def class_regs(c, dc):
    o = dc[c['name']]
    ia = sum(o[179 + k] << k for k in range(14))
    op = sum(o[193 + k] << k for k in range(11))
    return ia, op


def text(design, module, rounds, shapes=None):
    ast, pr, tr, d, pre, body = D.header(design, module)
    dc = dec_consts()
    kproc = [kk for kk, i in enumerate(ast.comb_ids) if ALU_RES in E.assigned_roots(ast.procs[i]['body'])][0]
    iproc = ast.comb_ids[kproc]
    assert iproc == ALU_PROC
    body.append(f'Definition TALU : nat := {kproc}%nat.')
    ex, L = [], []
    for c in isa.classes():
        n = c['name']
        ia, op = class_regs(c, dc)
        L += [f'Definition facts_{n}:Facts:=[((EVar {IALU[1]} {IALU[0]}%nat),{ia}); ((EVar {IOPC[1]} {IOPC[0]}%nat),{op})].',
              f'Definition F0s_{n} : Facts := filter (tail_okb wtab TALU) (ox_run comb_ps wtab (statement_fuel P) {rounds}%nat facts_{n}).',
              f'Definition F0_{n} : Facts := Eval vm_compute in F0s_{n}.',
              f'Lemma F0eq_{n} : F0s_{n} = F0_{n}. Proof. vm_compute; reflexivity. Qed.',
              f'Definition ov_{n} : SOv := Eval vm_compute in match oxexec F0_{n} (statement_fuel P) (nbfix (process_body process_{iproc})) [] with Some o => o | None => [] end.',
              f'Definition alu_{n} : Expr := Eval vm_compute in match sov_lookup ov_{n} {ALU_RES}%nat with Some (_,e) => e | None => EConst 1 0 end.']
        if shapes is None:
            L.append(f'Eval vm_compute in alu_{n}.')
            continue
        L += [f'Theorem {n}_alu seed fixed:CombLFP P seed fixed->FactsHold fixed facts_{n}->norm 32 (read_signal fixed {ALU_RES}%nat)=norm 32 (eval_expr fixed alu_{n}).',
              'Proof. intros HL HF.',
              f' pose proof (ox_run_sound P comb_ps wtab (statement_fuel P) seed fixed eq_refl wtab_ok eq_refl HL {rounds}%nat _ HF) as H1.',
              f' assert (H0s:FactsHold fixed F0s_{n}) by exact (filter_hold fixed _ _ H1).',
              f' rewrite F0eq_{n} in H0s.',
              f' exact(oxrun_comb_lfp P comb_ps wtab TALU process_{iproc} F0_{n} ov_{n} seed fixed eq_refl wtab_ok (ltac:(vm_compute;reflexivity)) (ltac:(vm_compute;reflexivity)) H0s HL (ltac:(vm_compute;reflexivity)) {ALU_RES}%nat 32%nat alu_{n} (ltac:(vm_compute;reflexivity)) (ltac:(vm_compute;reflexivity)) (ltac:(vm_compute;reflexivity))).',
              'Qed.']
        ex.append(f'{module}.{n}_alu')
    out = (f'(** {design}: ALU result per class (tools/cpu_tmpl_a5alu.py; overlay engine). proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + pre +
           f'Module {module}.\n' + '\n'.join(body) + '\n' + '\n'.join(L) + f'\nEnd {module}.\n' + ''.join(f'Print Assumptions {e}.\n' for e in ex))
    return out, ex


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', default='angelo5fix'); ap.add_argument('--module', default='A5TmplAlu'); ap.add_argument('--namespace', default='TmplA5Alu')
    ap.add_argument('--out', required=True); ap.add_argument('--accept', action='store_true'); ap.add_argument('--probe', action='store_true')
    ap.add_argument('--rounds', type=int, default=2)
    a = ap.parse_args()
    if a.probe:
        t, _ = text(a.design, a.module, a.rounds, None)
        Path(a.out).write_text(t); sys.exit(0)
    t, ex = text(a.design, a.module, a.rounds, True)
    if not a.accept:
        Path(a.out).write_text(t); sys.exit(0)
    import cpu_tmpl_accept as acc
    prof = json.loads(Path(f'framework/auto-contract-profiles/{a.design}.json').read_text())
    lp = [(prof['pipeline_roles']['ast']['file'].rsplit('/', 1)[0], prof['pipeline_roles']['ast']['module'].split('.')[0])]
    r = acc.accept(a.out, a.namespace, a.module, t, ex, lp, timeout=7200, extra=dict(generator='tools/cpu_tmpl_a5alu.py', design=a.design))
    print(json.dumps(r, indent=1)[:1500]); sys.exit(0 if r['accepted'] else 1)
