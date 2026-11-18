"""Simulation-first check of the NERV joint invariant INV, with mutation probes (template route, N = 0).

INV is the exact relation the proof will carry (Coq: Nerv state `s`, ISA state `isa` after the commits so far):
  boot   (reset_q = 1):  reset = 0, rom = image, regfile = 0, ISA = initial
  run    (reset_q = 0):  reset = 0, stall = 0, mem_rd_enable_q = 0, irq_num = 0, ram0 = 0, rom = image,
                         pc = ISA pc (mod 2^32), ISA nextpc = pc + 4,  imem_data = image[pc/4],
                         regfile lane i = ISA reg i for i in 1..31 (lane 0 is free: it is written by `addi x0` but never read)
Every state before a rising edge of every run is checked.  Each mutated invariant (a plausible wrong clause) must be
falsified by at least one run, otherwise the clause set would be too weak to be tested ("mutation probes").
Evidence: results/nerv-inv-sim-20261104/report.json.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
Usage: python tools/nerv_inv_sim.py <programs> <cycles> [seed-base] [out.json]
"""
import json
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_ast_sim as S  # noqa: E402
import nerv_cosim as C  # noqa: E402

M32 = (1 << 32) - 1
MEMWRQ, HPM_EVENT = 41, 436
RESET, STALL, RESET_Q, MEMRDQ, IRQ_NUM, IMEM_DATA, PC, RAM0, ROM, REGFILE = 1, 17, 109, 38, 104, 4, 45, 3, 2, 42
CTRL = dict(cycle_insn=112, cycle_trap=113, cycle_intr=111, cycle_late_wr=114, mem_rd_enable=33, mem_wr_enable=29, illinsn=108)


def lanes(rf):
    return [(rf >> (32 * i)) & M32 for i in range(32)]


def clauses(s, words, regs, pc_isa, mut=None):
    """Return the list of violated clause names for state s (a list of ints) against the ISA state (regs, pc_isa)."""
    bad = []
    img = S.pack_words(words)
    rom_ok = s[ROM] == img
    if not rom_ok:
        bad.append('rom')
    if s[RESET] != 0:
        bad.append('reset')
    if s[STALL] != 0:
        bad.append('stall')
    if s[RESET_Q] == 1:
        if any(lanes(s[REGFILE])):
            bad.append('boot_regfile')
        return bad
    if s[RESET_Q] != 0:
        bad.append('reset_q')
    if s[MEMRDQ] != (1 if mut == 'memrdq_one' else 0):
        bad.append('mem_rd_enable_q')
    if s[MEMWRQ] != (1 if mut == 'memwrq_one' else 0):
        bad.append('mem_wr_enable_q')
    if s[HPM_EVENT] != (1 if mut == 'hpm_event_one' else 0):
        bad.append('csr_hpm_event_value')
    if s[IRQ_NUM] != 0:
        bad.append('irq_num')
    if s[RAM0] != 0:
        bad.append('ram0')
    pc = s[PC] & M32
    if (pc if mut != 'pc_plus4' else (pc + 4) & M32) != pc_isa:
        bad.append('pc')
    idx = (pc // 4) if mut != 'imem_off_by_one' else (pc // 4 + 1)
    want = words[idx] if idx < len(words) else 0
    if s[IMEM_DATA] != want:
        bad.append('imem_data')
    ln = lanes(s[REGFILE])
    first = 1 if mut != 'lane0_zero' else 0
    for i in range(first, 32):
        if ln[i] != (regs[i] if i else 0):
            bad.append('lane%d' % i)
            break
    return bad


def run_one(sim, words, cycles, mut=None):
    r = S.NervRun(sim, words)
    regs = [0] * 32
    pc = 0
    first_bad = None
    commits = 0
    for c in range(cycles):
        bad = clauses(r.state, words, regs, pc, mut)
        if bad:
            return dict(cycle=c, commits=commits, violated=bad)
        commit, _, _ = r.step()
        if commit is not None:
            assert commit == pc, (commit, pc)
            pc = S.isa_step(regs, pc, S.decode(words[pc // 4] if pc // 4 < len(words) else S.CV_NOP), bytearray(4))
            commits += 1
    return None


if __name__ == '__main__':
    n, cycles = int(sys.argv[1]), int(sys.argv[2])
    base = int(sys.argv[3]) if len(sys.argv) > 3 else 8100000
    sim = S.load_sim(S.DEFAULT_AST['nerv'])
    t = time.time()
    progs = []
    for i in range(n):
        rng = random.Random(base + i)
        progs.append(S.gen_program(rng) if i % 2 == 0 else C.gen_hazard(rng))
    rep = dict(programs=n, cycles=cycles, seed_base=base)
    bad = []
    for words in progs:
        assert S.jump_family_check(words)
        e = run_one(sim, words, cycles)
        if e:
            bad.append(dict(words=[hex(w) for w in words], **e))
    rep['inv_violations'] = len(bad)
    rep['inv_first_violations'] = bad[:3]
    probes = {}
    for mut in ('memwrq_one', 'hpm_event_one', 'memrdq_one', 'pc_plus4', 'imem_off_by_one', 'lane0_zero'):
        hit = 0
        for words in progs:
            if run_one(sim, words, cycles, mut):
                hit += 1
        probes[mut] = hit
    rep['mutation_probes_detected_programs'] = probes
    rep['mutation_probes_all_detected'] = all(v > 0 for v in probes.values() if True)
    rep['seconds'] = round(time.time() - t)
    print(json.dumps(rep, indent=1))
    if len(sys.argv) > 4:
        Path(sys.argv[4]).parent.mkdir(parents=True, exist_ok=True)
        Path(sys.argv[4]).write_text(json.dumps(rep, indent=1) + '\n')
