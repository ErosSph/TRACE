#!/usr/bin/env python3
"""Per-class decoder facts for a decoder made of several comb processes (flags/ALU/immediate), template route.

Generalised rule (reuse of the CV32E40P overlay engine, Lang/ExtendedSVSymExecOverlay.v): the class facts are slices of the
instruction word (opcode, funct3, bit 30 / bit 25 where the ISA fixes them).  `ox_run` pushes them through the comb processes
(wire copies of the slices, flag process, ALU/immediate process) with guards decided through earlier in-process assignments.
Constant outputs: `DecOut` of every root of the decoder processes that the run derives (found by a Coq probe, then re-checked).
Symbolic outputs (the immediate): `oxrun_comb_lfp` gives  norm w (read root) = norm w (eval expr)  for the expression of the
overlay (the expression is computed inside Coq, never typed by the generator).
Roles: pipeline_roles.fetch_slot is not used; template_roles.decoder = {word, processes[], imm}.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
"""
import argparse, json, re, subprocess, sys, time
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles
import cpu_tmpl_edge as E
import cpu_isa_classes as isa
import cpu_class_table as ct

PRE = """From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVSymExecOverlay Lang.ExtendedSVWordInvariant @AST@
 coqutil.Z.BitOps coqutil.Z.bitblast coqutil.Z.prove_Zeq_bitwise riscv.Utility.Utility Ex.External.CPUImmediateShapes Ex.External.CPUImmediateRtlShapes.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVSymExecOverlay ExtendedSVWordInvariant @ASTNS@.
Import CPUImmediateShapes CPUImmediateRtlShapes.
Local Open Scope Z_scope.
Definition P:=@PROG@.
"""


IMMK = {'OPIMM': 'I', 'JALR': 'I', 'BRANCH': 'B', 'JAL': 'J', 'LUI': 'U', 'AUIPC': 'U'}


def decoder_roles(design):
    ast, pr, tr = roles.load_all(design)
    d = tr['decoder']
    return ast, pr, tr, d


def class_facts(word, c):
    sl = lambda w, l: ('ESel', w, word, ('EConst', 5, l))
    out = [(sl(7, 0), c['opcode'])]
    if ct.isa_f3(c) is not None:
        out.append((sl(3, 12), ct.isa_f3(c)))
    if c['name'] in ct.SHIFT_IMM or c['group'] == 'OP':
        f7 = c['funct7']
        out += [(sl(1, 30), (f7 >> 5) & 1), (sl(1, 25), f7 & 1)]
    return out


def coq_facts(fl):
    return '[' + '; '.join(f'({T.coq(e)},{z})' for e, z in fl) + ']'


def header(design, module):
    ast, pr, tr, d = decoder_roles(design)
    nsig = max(ast.sig) + 1
    wt = [[] for _ in range(nsig)]
    for kk, i in enumerate(ast.comb_ids):
        for r in E.assigned_roots(ast.procs[i]['body']):
            wt[r].append(kk)
    pre = (PRE.replace('@AST@', pr['ast']['module']).replace('@ASTNS@', pr['ast']['program'].split('.')[0])
           .replace('@PROG@', pr['ast']['program'].split('.')[-1]))
    body = ['Definition wtab:list(list nat):=[' + '; '.join('[' + ';'.join(f'{x}%nat' for x in w) + ']' for w in wt) + '].',
            'Definition comb_ps:=filter is_comb (processes P).',
            'Lemma wtab_ok:TabC comb_ps wtab.', 'Proof. apply tab_okb_sound. vm_compute;reflexivity. Qed.',
            'Lemma filter_hold s F f : FactsHold s F -> FactsHold s (filter f F).',
            'Proof. intros H e z HI. apply filter_In in HI as [HI _]. exact (H e z HI). Qed.']
    return ast, pr, tr, d, pre, body


def outs_roots(ast, d):
    rs = set()
    for p in d['processes']:
        rs |= set(E.assigned_roots(ast.procs[int(p.split('_')[1])]['body']))
    return sorted(rs)


def probe_text(design, rounds):
    ast, pr, tr, d, pre, body = header(design, 'Probe')
    word = ('EVar', 32, d['word']['id'])
    roots = outs_roots(ast, d)
    L = []
    for c in isa.classes():
        n = c['name']
        L.append(f'Definition facts_{n}:Facts:={coq_facts(class_facts(word, c))}.')
        L.append(f'Definition F_{n} := ox_run comb_ps wtab (statement_fuel P) {rounds} facts_{n}.')
        L.append(f'Eval vm_compute in (map (fun rw => (fst rw, fact_find F_{n} (EVar (snd rw) (fst rw)))) [' + ';'.join(f'({r}%nat,{ast.sig[r]["width"]}%nat)' for r in roots) + ']).')
    return pre + '\n'.join(body) + '\n' + '\n'.join(L) + '\n', roots


def run_probe(design, rounds, out):
    txt, roots = probe_text(design, rounds)
    Path(out).write_text(txt)
    return txt, roots


def probe_outs(design, rounds, work, ast_dir=None, query_report=None):
    txt, roots = probe_text(design, rounds)
    f = Path(work) / 'Probe.v'
    f.write_text(txt)
    started = time.monotonic()
    r = subprocess.run(['_opam/bin/coqc', '-R', 'src', 'Pfv', '-R', 'dep/coqutil/src/coqutil', 'coqutil', '-R', 'dep/riscv-coq/src/riscv', 'riscv',
                        '-R', str(ast_dir or 'experiments/framework/generated/angelo5-fixed'), 'Angelo5', str(f)], capture_output=True, text=True)
    elapsed = time.monotonic() - started
    if query_report is not None:
        Path(query_report).write_text(json.dumps(dict(queries=[dict(command=r.args, exit=r.returncode, wall_seconds=elapsed)]), indent=2)+"\n")
    if r.returncode:
        raise SystemExit(r.stdout + r.stderr)
    blocks = r.stdout.split(': list (signal * option Z)')[:-1]
    res = {}
    for c, b in zip(isa.classes(), blocks):
        res[c['name']] = {int(a): (int(z) if z else None)
                          for a, z in re.findall(r'\((\d+)%nat,\s*(Some (\d+)|None)\)', b.replace('Some ', 'Some '))[:0]} or None
        pairs = re.findall(r'\((\d+)%nat,\s*(None|Some \d+)\)', b)
        res[c['name']] = {int(a): (None if z == 'None' else int(z.split()[1])) for a, z in pairs}
    return res


def build(design, module, rounds, work, ast_dir=None, query_report=None):
    ast, pr, tr, d, pre, body = header(design, module)
    word = ('EVar', 32, d['word']['id'])
    probe = probe_outs(design, rounds, work, ast_dir=ast_dir, query_report=query_report)
    imm = d['imm']['id']
    kimm = [kk for kk, i in enumerate(ast.comb_ids) if imm in E.assigned_roots(ast.procs[i]['body'])][0]
    iproc = ast.comb_ids[kimm]
    exports = []
    info = {}
    body.append('Definition TIMM : nat := %d%%nat.' % kimm)
    body += ['Definition aimm_J (W:Expr) : Expr := EConcat 32 (EReplicate 11 11 (sel 1 W 31)) (EConcat 21 (sel 1 W 31) (EConcat 20 (sel 8 W 12) (EConcat 12 (sel 1 W 20) (EConcat 11 (sel 10 W 21) (EConst 1 0))))).',
             'Theorem eval_aimm_J s W : eval_expr s (aimm_J W) = norm 32 (isa_imm_J (eval_expr s W)).',
             'Proof. unfold aimm_J, isa_imm_J. close_rimm s W. all: finish_imm. all: (replace (i - 20 + 31) with 31 by lia; rewrite ?Tsign; reflexivity). Qed.']
    for c in isa.classes():
        n = c['name']
        outs = sorted((r, ast.sig[r]['width'], z) for r, z in probe[n].items() if z is not None)
        info[n] = dict(outputs=len(outs), symbolic=[r for r, z in probe[n].items() if z is None and r in (imm,)])
        body += [f'Definition facts_{n}:Facts:={coq_facts(class_facts(word, c))}.',
                 f'Definition outs_{n}:list((signal*nat)*Z):=[' + '; '.join(f'(({r}%nat,{w}%nat),{z})' for r, w, z in outs) + '].',
                 f'Theorem {n}_dec seed fixed:CombLFP P seed fixed->FactsHold fixed facts_{n}->DecOut fixed outs_{n}.',
                 f'Proof. intros HL HF. exact(ox_run_outs P comb_ps wtab {rounds}%nat facts_{n} outs_{n} seed fixed eq_refl wtab_ok HF HL (ltac:(vm_compute;reflexivity))). Qed.']
        exports.append(f'{module}.{n}_dec')
        if probe[n].get(imm) is None:
            body += [f'Definition F0s_{n} : Facts := filter (tail_okb wtab TIMM) (ox_run comb_ps wtab (statement_fuel P) {rounds}%nat facts_{n}).',
                     f'Definition F0_{n} : Facts := Eval vm_compute in F0s_{n}.',
                     f'Lemma F0eq_{n} : F0s_{n} = F0_{n}. Proof. vm_compute; reflexivity. Qed.',
                     f'Definition ov_{n} : SOv := Eval vm_compute in match oxexec F0_{n} (statement_fuel P) (nbfix (process_body process_{iproc})) [] with Some o => o | None => [] end.',
                     f'Definition imm_{n} : Expr := Eval vm_compute in match sov_lookup ov_{n} {imm}%nat with Some (_,e) => e | None => EConst 1 0 end.',
                     f'Theorem {n}_imm seed fixed:CombLFP P seed fixed->FactsHold fixed facts_{n}->norm 32 (read_signal fixed {imm}%nat)=norm 32 (eval_expr fixed imm_{n}).',
                     'Proof. intros HL HF.',
                     f' pose proof (ox_run_sound P comb_ps wtab (statement_fuel P) seed fixed eq_refl wtab_ok eq_refl HL {rounds}%nat _ HF) as H1.',
                     f' assert (H0s:FactsHold fixed F0s_{n}) by exact (filter_hold fixed _ _ H1).',
                     f' rewrite F0eq_{n} in H0s.',
                     f' exact(oxrun_comb_lfp P comb_ps wtab TIMM process_{iproc} F0_{n} ov_{n} seed fixed eq_refl wtab_ok (ltac:(vm_compute;reflexivity)) (ltac:(vm_compute;reflexivity)) H0s HL (ltac:(vm_compute;reflexivity)) {imm}%nat 32%nat imm_{n} (ltac:(vm_compute;reflexivity)) (ltac:(vm_compute;reflexivity)) (ltac:(vm_compute;reflexivity))).',
                     'Qed.']
            k = IMMK[c['group']]
            sh = {'I': 'rimm_I', 'B': 'rimm_B', 'J': 'aimm_J', 'U': 'imm_U'}[k]
            ev = {'I': 'eval_rimm_I', 'B': 'eval_rimm_B', 'J': 'eval_aimm_J', 'U': 'eval_imm_U'}[k]
            body += [f'Theorem {n}_imm_isa seed fixed:CombLFP P seed fixed->FactsHold fixed facts_{n}->norm 32 (read_signal fixed {imm}%nat)=norm 32 (isa_imm_{k} (norm 32 (read_signal fixed {d["word"]["id"]}%nat))).',
                     f'Proof. intros HL HF. rewrite ({n}_imm seed fixed HL HF).',
                     f' assert (E: imm_{n} = {sh} (EVar 32 {d["word"]["id"]}%nat)) by (vm_compute; reflexivity).',
                     f' rewrite E, {ev}. cbn [eval_expr]. rewrite norm_idempotent. reflexivity. Qed.']
            exports += [f'{module}.{n}_imm', f'{module}.{n}_imm_isa']
    text = (f'(** {design}: per-class decoder facts (tools/cpu_tmpl_a5dec.py; overlay engine). proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + pre +
            f'Module {module}.\n' + '\n'.join(body) + f'\nEnd {module}.\n' + ''.join(f'Print Assumptions {e}.\n' for e in exports))
    return text, exports, info


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--ast-dir',type=Path)
    ap.add_argument('--query-report',type=Path)
    ap.add_argument('--design', default='angelo5fix')
    ap.add_argument('--out', required=True)
    ap.add_argument('--probe', action='store_true')
    ap.add_argument('--rounds', type=int, default=2)
    ap.add_argument('--module', default='A5TmplDec')
    ap.add_argument('--namespace')
    ap.add_argument('--accept', action='store_true')
    a = ap.parse_args()
    if a.probe:
        txt, roots = run_probe(a.design, a.rounds, a.out)
        print(a.out, len(roots), 'roots')
    else:
        import tempfile
        text, exports, info = build(a.design, a.module, a.rounds, tempfile.mkdtemp(),ast_dir=a.ast_dir,query_report=a.query_report)
        if not a.accept:
            Path(a.out).write_text(text); print(a.out, len(exports), 'exports', info); sys.exit(0)
        import cpu_tmpl_accept as acc
        prof = json.loads(Path(f'framework/auto-contract-profiles/{a.design}.json').read_text())
        lp = [(prof['pipeline_roles']['ast']['file'].rsplit('/', 1)[0], prof['pipeline_roles']['ast']['module'].split('.')[0])]
        r = acc.accept(a.out, a.namespace, a.module, text, exports, lp, extra=dict(generator='tools/cpu_tmpl_a5dec.py', design=a.design, per_class=info))
        print(json.dumps({k: r[k] for k in r if k != 'per_class'}, indent=1)); sys.exit(0 if r['accepted'] else 1)
