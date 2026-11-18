#!/usr/bin/env python3
"""srv32: (1) AST simulator vs Verilator 4.028 C++ model of the same wrapper, (2) differential bug hunt vs the RV32I reference.

  python tools/cpu_srv32_bughunt.py cross <programs> <cycles> [--jobs 2]   # per-cycle state equality AST sim vs C++
  python tools/cpu_srv32_bughunt.py hunt  <programs-per-set> <cycles> [--jobs 2]   # sets: jump29 (random), hazard (dependency-heavy)

Programs are in the 29-class jump-family domain (CPUJumpFamilyProgramDomain.check_program ported as
cpu_ast_sim.jump_family_check).  On a mismatch the program is minimised (instruction replacement by NOP / truncation) and printed.
proof_author='LLM-generated: Claude Code (claude-sonnet-5-5)'; external_llm_api_calls=0.
"""
import argparse, json, os, random, subprocess, sys, time, multiprocessing as mp
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_ast_sim as S

ROOT = Path(__file__).resolve().parent.parent
V = Path('/opt/miniforge3/envs/verilator4/opt/verilator-4.028')
RTL = ROOT.parent / 'datasets/new/kuopinghsu_srv32/rtl'
DEFAULT_BUILD = Path(os.environ.get('SRV32_CPP_BUILD', '/tmp/srv32_cpp_build'))
# (name, signal id) compared every cycle; regs are compared as x1..x31
CMP = [('fetch_pc', 239), ('if_pc', 240), ('ex_pc', 241), ('ex_insn', 249), ('wb_result', 290), ('wb_dst_sel', 294),
       ('wb_alu2reg', 289), ('wb_branch', 295), ('wb_branch_nxt', 296), ('flush', 234), ('stall_r', 232),
       ('imem_rdata', 12), ('imem_addr', 4), ('ex_stall', 237), ('ex_flush', 272)]


def build_cpp(build):
    build = Path(build)
    env = dict(os.environ, LC_ALL='C', VERILATOR_ROOT=str(V))
    build.mkdir(parents=True, exist_ok=True)
    subprocess.run([str(V / 'bin/verilator'), '--cc', '--public', '-Wno-fatal', '-Wno-BLKANDNBLK', '-Wno-PINCONNECTEMPTY',
                    '-DSYNTHESIS', '--x-initial', '0', '--x-assign', '0', f'-I{RTL}', '--top-module', 'srv32_env',
                    '--Mdir', str(build), str(ROOT / 'experiments/framework/srv32/srv32_env.v'), str(RTL / 'riscv.v')],
                   check=True, env=env, capture_output=True)
    inc = V / 'share/verilator/include'
    subprocess.run(['g++', '-O2', '-w', f'-I{build}', f'-I{inc}', f'-I{inc}/vltstd', '-o', str(build / 'tb'),
                    str(ROOT / 'experiments/framework/srv32/tb_srv32.cpp'), str(build / 'Vsrv32_env.cpp'),
                    str(build / 'Vsrv32_env__Syms.cpp'), str(inc / 'verilated.cpp')], check=True)
    return build / 'tb'


def gen_hazard(rng):
    """Dependency-heavy: tiny register pool, most readers use the previous writer, back-to-back control transfers."""
    while True:
        n = rng.randint(4, 30)
        pool = rng.sample(range(1, 8), rng.choice([2, 3]))
        words, last = [], pool[0]
        for i in range(n):
            kind = rng.choices(['data', 'br', 'jal', 'jalr'], [55, 25, 10, 10])[0]
            if i == n - 1:
                kind = rng.choice(['jal', 'jalr'])
            hot = pool + [last] * 6          # bias reads toward the most recent writer
            w = S.gen_instruction(rng, kind, i, n, hot)
            words.append(w)
            if kind in ('data', 'jal', 'jalr') and (w >> 7) & 31:
                last = (w >> 7) & 31
        if S.jump_family_check(words):
            return words


def gen_set(kind, rng):
    return gen_hazard(rng) if kind == 'hazard' else S.gen_program(rng)


def shift_rf(rf_int):
    return [(rf_int >> (32 * i)) & S.M32 for i in range(32)]


def ast_states(sim, words, cycles):
    run = S.Srv32Run(sim, words)
    out = []
    for _ in range(cycles):
        run.step()
        st = run.state
        out.append([st[i] & S.M32 for _, i in CMP] + [(st[S.SV_REGS] >> (32 * k)) & S.M32 for k in range(31)])
    return out


def cpp_states(tb, progs, cycles):
    text = f'{cycles}\n' + ''.join(f'{len(w)} ' + ' '.join(f'{x:x}' for x in w) + '\n' for w in progs)
    res = subprocess.run([str(tb)], input=text, capture_output=True, text=True, check=True).stdout.split('\n')
    out, cur = [], []
    for line in res:
        if line == 'END':
            out.append(cur); cur = []
        elif line:
            cur.append([int(x, 16) for x in line.split()])
    return out


G = {}


def _cross_chunk(chunk):
    sim, tb, cycles = G['sim'], G['tb'], G['cycles']
    cpp = cpp_states(tb, chunk, cycles)
    bad, cmpd = [], 0
    for w, c in zip(chunk, cpp):
        a = ast_states(sim, w, cycles)
        for cyc, (x, y) in enumerate(zip(a, c)):
            cmpd += len(x)
            if x != y:
                names = [n for n, _ in CMP] + [f'x{k+1}' for k in range(31)]
                bad.append(dict(words=[hex(v) for v in w], cycle=cyc,
                                diff=[(names[i], x[i], y[i]) for i in range(len(x)) if x[i] != y[i]][:4]))
                break
    return len(chunk), cmpd, bad


def cmd_cross(a):
    sim = S.load_sim(S.DEFAULT_AST['srv32'])
    tb = build_cpp(a.build)
    rng = random.Random(a.seed)
    progs = [list(w) for w in S.Srv32Design.examples]
    while len(progs) < a.programs:
        progs.append(gen_set('hazard' if len(progs) % 3 == 0 else 'jump29', rng))
    G.update(sim=sim, tb=tb, cycles=a.cycles)
    chunks = [progs[i:i + 25] for i in range(0, len(progs), 25)]
    t = time.time()
    with mp.get_context('fork').Pool(a.jobs) as p:
        res = p.map(_cross_chunk, chunks)
    rep = dict(programs=sum(r[0] for r in res), cycles_each=a.cycles,
               signal_values_compared=sum(r[1] for r in res), signals_per_cycle=len(CMP) + 31,
               mismatches=sum(len(r[2]) for r in res), first=[b for r in res for b in r[2]][:3],
               seconds=round(time.time() - t, 1))
    print(json.dumps(rep, indent=1))
    return 1 if rep['mismatches'] else 0


NOP = 0x13


def mismatch(sim, words, cycles):
    try:
        return S.validate_against_isa(S.DESIGNS['srv32'], sim, words, cycles)
    except Exception as e:  # noqa
        return 'EXC ' + repr(e)[:200]


def minimise(sim, words, cycles):
    """Greedy: replace instructions by NOP, drop suffix; keep only programs still accepted by the domain checker and still failing."""
    words = list(words)
    changed = True
    while changed:
        changed = False
        for i in range(len(words)):
            if words[i] == NOP:
                continue
            cand = words[:i] + [NOP] + words[i + 1:]
            if S.jump_family_check(cand) and mismatch(sim, cand, cycles):
                words, changed = cand, True
    return words


def _hunt_one(args):
    kind, seed, cycles = args
    rng = random.Random(seed)
    words = gen_set(kind, rng)
    err = mismatch(G['sim'], words, cycles)
    return kind, seed, err, (words if err else None)


def cmd_hunt(a):
    sim = S.load_sim(S.DEFAULT_AST['srv32'])
    G.update(sim=sim)
    jobs = [(k, a.seed + i, a.cycles) for i in range(a.programs) for k in ('jump29', 'hazard')]
    t = time.time(); bad = []; n = 0
    with mp.get_context('fork').Pool(a.jobs) as p:
        for kind, seed, err, words in p.imap_unordered(_hunt_one, jobs, chunksize=4):
            n += 1
            if err:
                bad.append(dict(kind=kind, seed=seed, err=err, words=[hex(w) for w in words]))
    rep = dict(programs=n, per_set=a.programs, cycles=a.cycles, total_cycles=n * a.cycles, mismatches=len(bad),
               seconds=round(time.time() - t), bad=bad[:5])
    if bad:
        mn = minimise(sim, [int(x, 16) for x in bad[0]['words']], a.cycles)
        rep['minimised_first'] = dict(words=[hex(w) for w in mn], mismatch=mismatch(sim, mn, a.cycles))
    print(json.dumps(rep, indent=1))
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest='cmd', required=True)
    for name in ('cross', 'hunt'):
        s = sub.add_parser(name)
        s.add_argument('programs', type=int)
        s.add_argument('cycles', type=int)
        s.add_argument('--jobs', type=int, default=2)
        s.add_argument('--seed', type=int, default=20261104)
        s.add_argument('--build', default=str(DEFAULT_BUILD))
    a = ap.parse_args()
    return {'cross': cmd_cross, 'hunt': cmd_hunt}[a.cmd](a)


if __name__ == '__main__':
    sys.exit(main())
