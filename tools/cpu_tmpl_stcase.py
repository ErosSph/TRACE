#!/usr/bin/env python3
"""Steel per-class constant propagation through the generic fast engine (Lang/ExtendedSVFast4.v), used as an ORACLE:
the Python generator asks Coq (vm_compute on `fs_find`) which wire constants the engine derives from the class facts, and then states
exactly those as the `cf_outs` of the checked cases.  Untrusted; Coq re-checks every case (check_shared4).
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import re, subprocess, sys, tempfile, os, json, time, resource, hashlib
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_tmpl_stex as S
import cpu_isa_classes as isa

ROOT = Path(__file__).resolve().parent.parent
HDR = '''From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVSymExecOverlay Lang.ExtendedSVBackward Lang.ExtendedSVEval3 Lang.ExtendedSVSymExecFast Lang.ExtendedSVFastCond Lang.ExtendedSVEval4 Lang.ExtendedSVFast4 Steel.SteelAST.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVSymExecOverlay ExtendedSVBackward ExtendedSVEval3 ExtendedSVSymExecFast ExtendedSVFastCond ExtendedSVEval4 ExtendedSVFast4.
Local Open Scope Z_scope.
'''
_P = None


def planner():
    global _P
    if _P is None:
        _P = S.SteelPlanner()
    return _P


def wtab_text(P):
    wt = [[] for _ in range(P.nsig)]
    for r, ks in P.writers.items():
        wt[r] = ks
    return 'Definition wtab:list(list nat):=[' + '; '.join('[' + ';'.join(f'{x}%nat' for x in w) + ']' for w in wt) + '].'


def script_text(P, rounds=2):
    nc = len(P.ast.comb_ids)
    return '[' + '; '.join(f'(false,{k}%nat)' for _ in range(rounds) for k in range(nc)) + ']'


def facts_text(P, consts):
    return '[' + '; '.join(f'((EVar {P.width_of(r)} {r}%nat), {v})' for r, v in consts) + ']'


def oracle(cases, rounds=2):
    """cases: {name: [(root, value)]} -> {name: {root: value}} of all roots that the fast engine decides."""
    P = planner()
    roots = sorted(P.ast.sig)
    t = HDR + 'Definition P:=SteelAST.steel_program.\n' + wtab_text(P) + '\nDefinition comb_ps:=filter is_comb (processes P).\n'
    t += f'Definition sc0:Script:={script_text(P, rounds)}.\n'
    t += 'Definition rl := [' + '; '.join(f'({P.width_of(r)}%nat,{r}%nat)' for r in roots) + '].\n'
    names = list(cases)
    for i, n in enumerate(names):
        t += f'Definition f_{i}:Facts:={facts_text(P, cases[n])}.\n'
        t += f'Definition fs_{i} := frun4 comb_ps wtab (statement_fuel P) (add_facts fs_empty f_{i}) sc0.\n'
        t += f'Eval vm_compute in (map (fun p => fs_find fs_{i} (fst p) (snd p)) rl).\n'
    cache=None
    if os.environ.get('VERILROCQ_STEEL_QUERY_CACHE'):
        # This directory is created fresh by one production preparation. The
        # query text and same-run AST path form a memoization key, not an audit.
        cache_root=Path(os.environ['VERILROCQ_STEEL_QUERY_CACHE']);cache_root.mkdir(exist_ok=True)
        key=hashlib.sha256((os.environ['VERILROCQ_STEEL_AST_DIR']+'\n'+t).encode()).hexdigest()
        cache=cache_root/(key+'.json')
    if cache is not None and cache.exists():
        stdout=json.loads(cache.read_text())['stdout']
    else:
      with tempfile.TemporaryDirectory() as td:
        fn = Path(td) / 'Probe.v'
        fn.write_text(t)
        # Production queries use the AST compiled during this same preparation.
        # Defaults preserve the historical generator interface.
        ast_dir=os.environ.get('VERILROCQ_STEEL_AST_DIR','../experiments/framework/generated/steel')
        compiler=str(ROOT/'_opam/bin/coqc') if 'VERILROCQ_STEEL_AST_DIR' in os.environ else 'coqc'
        before=resource.getrusage(resource.RUSAGE_CHILDREN);started=time.monotonic()
        r = subprocess.run([compiler, '-R', '.', 'Pfv', '-R', '../dep/coqutil/src/coqutil/', 'coqutil', '-R', '../dep/riscv-coq/src/riscv/', 'riscv',
                            '-R', ast_dir, 'Steel', str(fn)], cwd=ROOT / 'src', capture_output=True, text=True)
        elapsed=time.monotonic()-started;after=resource.getrusage(resource.RUSAGE_CHILDREN)
        if os.environ.get('VERILROCQ_STEEL_QUERY_TIMING'):
            with open(os.environ['VERILROCQ_STEEL_QUERY_TIMING'],'a') as log:
                log.write(json.dumps(dict(kind='required_generation_coqc_query',classes=names,wall_seconds=elapsed,cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,peak_rss_kib=after.ru_maxrss,exit=r.returncode))+'\n')
      if r.returncode != 0:
        raise RuntimeError(r.stdout + r.stderr)
      stdout=r.stdout
      if cache is not None:cache.write_text(json.dumps(dict(stdout=stdout)))
    outs = re.findall(r'=\s*\[(.*?)\]\s*:\s*list \(option Z\)', stdout, re.S)
    assert len(outs) == len(names), (len(outs), len(names), stdout[:500])
    res = {}
    for n, o in zip(names, outs):
        vals = re.findall(r'Some\s+(-?\d+)|None', o)
        items = re.findall(r'(Some\s+-?\d+|None)', o)
        assert len(items) == len(roots), (len(items), len(roots))
        res[n] = {r: int(it.split()[1]) for r, it in zip(roots, items) if it != 'None'}
    return res


CLASSES = None


def classes():
    global CLASSES
    if CLASSES is None:
        CLASSES = {}
        for c in isa.classes():
            c = dict(c)
            if c['name'] == 'Jalr':
                c['funct3'] = 0      # RV32I decode of JALR fixes funct3 = 0 (the class table leaves it open)
            CLASSES[c['name']] = c
    return CLASSES


def class_consts(name):
    c = classes()[name]
    cs = list(S.BASE) + [(221, c['opcode'])]
    if c['funct3'] is not None:
        cs.append((219, c['funct3']))
    if c['funct7'] is not None:
        cs.append((220, c['funct7']))
    return cs


if __name__ == '__main__':
    names = sys.argv[1:] or list(classes())
    o = oracle({n: class_consts(n) for n in names})
    P = planner()
    for n in names:
        miss = [r for r in (161, 243, 277, 215, 268, 244, 256, 25, 23, 29, 223, 205, 162) if r not in o[n]]
        print(n, len(o[n]), 'undecided of key:', miss)
