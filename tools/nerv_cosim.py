#!/usr/bin/env python3
"""Validate the AST simulator (cpu_ast_sim.NervRun) against a Verilator-compiled C++ model of the same wrapper.

For every program the FULL per-cycle observation must be identical: commit pc | none, ram0, all 32 raw regfile words
(x0 word included).  The Verilator model is built from the unmodified datasets/nerv/nerv.sv plus
experiments/framework/nerv/nerv_top.sv with --public-flat-rw (so internal signals are readable; no RTL change).
Usage: nerv_cosim.py --build-dir DIR [--x-assign {default,0,1}] --programs N --cycles C [--seed S] [--check-ids]
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
"""
import argparse, json, os, random, subprocess, sys, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_ast_sim as S

ROOT = Path(__file__).resolve().parent.parent
VROOT = Path('/opt/miniforge3/envs/verilator4/opt/verilator-4.028')
VLT = VROOT / 'bin/verilator'
CORE = ROOT.parent / 'datasets/nerv/nerv.sv'
TOP = ROOT / 'experiments/framework/nerv/nerv_top.sv'


def build(bdir, xassign):
    bdir.mkdir(parents=True, exist_ok=True)
    env = {k: v for k, v in os.environ.items() if k != 'VERILATOR_ROOT'}
    env['LC_ALL'] = 'C'
    cmd = [str(VLT), '--cc', '--public-flat-rw', '-Wno-fatal', '-Wno-WIDTH', '-Wno-BLKANDNBLK', '-Wno-PINCONNECTEMPTY',
           '-Wno-UNOPTFLAT', '-Wno-CASEINCOMPLETE', '--top-module', 'nerv_top', '-Mdir', str(bdir), '-I' + str(CORE.parent)]
    if xassign != 'default':
        cmd += ['--x-assign', xassign]
    cmd += [str(CORE), str(TOP)]
    subprocess.run(cmd, check=True, env=env, capture_output=True)
    subprocess.run(['make', '-f', 'Vnerv_top.mk', '-j2', f'VERILATOR_ROOT={VROOT}/share/verilator', 'Vnerv_top__ALL.a',
                    'verilated.o'], cwd=bdir, check=True, env=env, capture_output=True)
    inc = f'{VROOT}/share/verilator/include'
    subprocess.run(['g++', '-O1', '-o', 'nerv_cosim', str(ROOT / 'tools/nerv_cosim_main.cpp'), 'Vnerv_top__ALL.a', 'verilated.o',
                    '-I.', f'-I{inc}', f'-I{inc}/vltstd', '-faligned-new'], cwd=bdir, check=True, env=env, capture_output=True)
    return bdir / 'nerv_cosim'


def run_cpp(exe, progs, cycles):
    inp = ''.join(f'{cycles} {len(w)} ' + ' '.join(f'{x:x}' for x in w) + '\n' for w in progs)
    out = subprocess.run([str(exe)], input=inp, capture_output=True, text=True, check=True).stdout.split('\n')
    res, cur = [], []
    for ln in out:
        if ln == 'E':
            res.append(cur); cur = []
        elif ln.startswith('C '):
            f = ln.split()
            cur.append((None if f[1] == '-' else int(f[1], 16), int(f[2], 16), [int(x, 16) for x in f[3:]]))
    return res


def ast_trace(sim, w, cycles):
    run = S.NervRun(sim, w, check_stable=True)
    out = []
    for _ in range(cycles):
        pc, rf, mem = run.step()
        out.append((pc, mem, S.rf_from_int(rf)))
    return out


def check_ids():
    rep = json.loads((ROOT / 'experiments/framework/generated/nerv/report.json').read_text())
    tbl = {s['path'].replace('nerv_top.', ''): s['id'] for s in rep['signal_table']}
    for name, i in S.NV_SIGNALS.items():
        assert tbl[name] == i, (name, i, tbl[name])
    return len(S.NV_SIGNALS)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--build-dir', type=Path, required=True)
    ap.add_argument('--x-assign', default='default', choices=['default', '0', '1'])
    ap.add_argument('--programs', type=int, default=300)
    ap.add_argument('--cycles', type=int, default=300)
    ap.add_argument('--seed', type=int, default=5150)
    ap.add_argument('--set', default='domain', choices=['domain', 'wide'],
                    help='domain: jump-family programs; wide: loads/stores/CSR/ECALL/illegal/Zbb words (RTL-vs-C++ only, no ISA)')
    ap.add_argument('--out')
    a = ap.parse_args()
    t0 = time.time()
    ids = check_ids()
    exe = build(a.build_dir, a.x_assign)
    sim = S.load_sim(S.DEFAULT_AST['nerv'])
    rng = random.Random(a.seed)
    progs = [list(w) for w in S.DESIGNS['nerv'].examples] if a.set == 'domain' else []
    while len(progs) < a.programs:
        if a.set == 'wide':
            k = len(progs) % 4        # 1/2 dark-style memory programs (x0+0 loads/stores), 1/4 mostly-legal mix, 1/4 chaos
            progs.append(S.gen_dark_program(rng) if k < 2 else gen_wide(rng, legal=(k == 2)))
        else:
            progs.append(S.gen_program(rng) if len(progs) % 2 == 0 else gen_hazard(rng))
    cpp = run_cpp(exe, progs, a.cycles)
    bad, commits = [], 0
    for k, (w, ct) in enumerate(zip(progs, cpp)):
        at = ast_trace(sim, w, a.cycles)
        commits += sum(1 for x in at if x[0] is not None)
        if len(ct) != len(at) or any(x != y for x, y in zip(at, [(p, m, r) for p, m, r in ct])):
            d = next((i for i, (x, y) in enumerate(zip(at, ct)) if x != y), None)
            bad.append(dict(program=k, words=[hex(x) for x in w], first_diff_cycle=d))
    rep = dict(set=a.set, x_assign=a.x_assign, signal_ids_checked=ids, programs=len(progs), cycles_each=a.cycles,
               total_cycles=len(progs) * a.cycles, committed=commits, mismatches=len(bad), first=bad[:3],
               stability_check='comb_round fixed point asserted before every cycle', seconds=round(time.time() - t0, 1))
    print(json.dumps(rep, indent=1))
    if a.out:
        Path(a.out).write_text(json.dumps(rep, indent=1) + '\n')
    return 1 if bad else 0


def gen_wide(rng, legal=False):
    """Words outside the jump-family domain, to exercise the rest of the AST (RAM wrapper, loads/stores, traps, CSRs,
    ECALL/EBREAK/MRET, Zba/Zbb/Zbs/Zbc, misaligned targets, illegal words).  Only RTL-vs-C++ equality is checked."""
    n = rng.randint(8, 60)
    w = []
    for i in range(n):
        c = rng.randrange(14)
        if legal:     # mostly-legal mix: no SYSTEM/MISC-MEM/random words, aligned targets, so programs keep running
            c = rng.choice([0, 1, 2, 3, 4, 5, 5, 6, 6, 7, 8, 9, 12])
        rd, rs1, rs2 = rng.randrange(6), rng.randrange(6), rng.randrange(6)
        if c <= 2:   # OP with random funct7/funct3 (incl. Zb*)
            w.append(S.r_type(rng.choice([0, 0x20, 0x10, 0x14, 0x30, 0x05, 0x04, 0x24, 0x34, 0x7f]), rs2, rs1, rng.randrange(8), rd, 51))
        elif c <= 4:  # OP-IMM
            w.append((rng.getrandbits(12) << 20) | (rs1 << 15) | (rng.randrange(8) << 12) | (rd << 7) | 19)
        elif c == 5:  # LOAD x0+0.. and others
            w.append(((rng.choice([0, 0, 1, 2, 3, 4, 8]) & 0xFFF) << 20) | (rng.choice([0, 0, rs1]) << 15) | (rng.randrange(8) << 12) | (rd << 7) | 3)
        elif c == 6:  # STORE
            imm = rng.choice([0, 0, 1, 2, 3, 4, 8])
            w.append(((imm >> 5) << 25) | (rs2 << 20) | (rng.choice([0, 0, rs1]) << 15) | (rng.randrange(4) << 12) | ((imm & 31) << 7) | 35)
        elif c == 7:  # BRANCH to a random (maybe misaligned) offset
            imm = rng.choice([4 * rng.randrange(-4, 8), 4 * rng.randrange(-4, 8) + (0 if legal else 2), 8]) & 0x1FFF
            w.append((((imm >> 12) & 1) << 31) | (((imm >> 5) & 0x3F) << 25) | (rs2 << 20) | (rs1 << 15) | (rng.randrange(8) << 12) | (((imm >> 1) & 0xF) << 8) | (((imm >> 11) & 1) << 7) | 99)
        elif c == 8:  # JAL / JALR
            if rng.random() < .5:
                imm = (4 * rng.randrange(-3, 8) + (0 if legal else rng.choice([0, 0, 2]))) & 0x1FFFFF
                w.append((((imm >> 20) & 1) << 31) | (((imm >> 1) & 0x3FF) << 21) | (((imm >> 11) & 1) << 20) | (((imm >> 12) & 0xFF) << 12) | (rd << 7) | 111)
            else:
                w.append(((rng.choice([0, 4, 8, 12, 5]) & 0xFFF) << 20) | (rng.choice([0, rs1]) << 15) | (rng.randrange(8) << 12) | (rd << 7) | 103)
        elif c == 9:  # LUI / AUIPC
            w.append((rng.getrandbits(20) << 12) | (rd << 7) | rng.choice([55, 23]))
        elif c == 10:  # SYSTEM: CSR ops (known and random addresses), ECALL, EBREAK, MRET, WFI
            csr = rng.choice([0x300, 0x304, 0x305, 0x340, 0x341, 0x342, 0xB00, 0xB02, 0xB80, 0xC00, 0xBC0, 0xFC0, 0xF11, rng.getrandbits(12)])
            w.append(rng.choice([0x00000073, 0x00100073, 0x30200073, 0x10500073,
                                 (csr << 20) | (rs1 << 15) | (rng.choice([1, 2, 3, 5, 6, 7]) << 12) | (rd << 7) | 115]))
        elif c == 11:  # MISC-MEM (fence, fence.i)
            w.append(rng.choice([0x0ff0000f, 0x0000100f]))
        elif c == 12:  # Zbb unary forms
            w.append((rng.choice([0x600, 0x601, 0x602, 0x604, 0x605, 0x287, 0x698, 0x687]) << 20) | (rs1 << 15) | (rng.choice([1, 5]) << 12) | (rd << 7) | 19)
        else:        # fully random word
            w.append(rng.getrandbits(32))
    return w


def gen_hazard(rng):
    """Hazard-heavy member of the jump-family domain: 1-3 live registers (back-to-back RAW/WAW chains), x0
    destinations, branches/JAL/JALR(base x0) and loops; checked by jump_family_check."""
    while True:
        n = rng.randint(4, 40)
        pool = [0] + rng.sample(range(1, 32), rng.choice([1, 2, 3]))
        w = []
        for i in range(n):
            k = rng.choices(['data', 'br', 'jal', 'jalr'], [58, 24, 8, 10])[0]
            if i == n - 1:
                k = rng.choice(['jal', 'jalr'])
            w.append(S.gen_instruction(rng, k, i, n, pool))
        if S.jump_family_check(w):
            return w


if __name__ == '__main__':
    sys.exit(main())
