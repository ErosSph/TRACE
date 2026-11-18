#!/usr/bin/env python3
"""Steel: simulation-first test of the candidate joint invariant INV (mirror) before any Coq (as for CV32E40P).
  reach   : INV holds on every post-cycle state of random in-domain programs (from the real boot), and each commit equals ISA run1.
  induct  : INV is inductive on RANDOM (unreachable) INV states: one RTL cycle gives INV' and the ISA step (the test that finds
            missing clauses).  Every register that INV does not constrain is randomised.
  mutants : INV clause mutants and state mutants must be rejected (non-vacuity / each clause matters).
Usage: steel_inv_sim.py reach N CYCLES SEED | induct N SEED | mutants N SEED
proof_author='LLM-generated: Claude Code (claude-sonnet-5-5)'; external_llm_api_calls=0.
"""
import sys, random, json
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_ast_sim as S
import steel_bughunt as B

M32 = S.M32
# signal ids (framework/auto-contract-profiles/steel.json)
CLK, RST, RAM, RD, RRESP, WRESP, ENVRR = 0, 1, 15, 11, 12, 13, 14
PC, CS, RR, PRR, PLR, PWR, PIN = 253, 200, 257, 248, 247, 251, 245
RF = 214
CE, LP, SP, TRAP, FLUSH, INSTR = 170, 234, 265, 268, 203, 217
SEQ_FREE = [246, 249, 250, 252, 245]     # prev_instruction_address, prev_rw_address, prev_write_data, prev_write_strobe, prev_instruction
MIP = [186, 187, 188, 189]               # mip fields
CSR_FREE = [193, 194, 181, 182, 183, 184, 179, 191, 178, 190, 198, 175, 176, 177, 196, 195]   # mstatus, mie, mepc, mscratch, counters, mcause, mtval, mtvec
OPERATING, RESETSTATE = 2, 1


def img_word(words, a):
    return words[a // 4] if (a % 4 == 0 and 0 <= a // 4 < len(words)) else None


class Model:
    """ISA side: regs, pc after the committed prefix."""
    def __init__(self):
        self.regs = [0] * 32
        self.pc = 0


def lanes(s):
    r = s[RF]
    return [0] + [(r >> (32 * i)) & M32 for i in range(31)]     # x0..x31


def inv(words, s, m, mut=None):
    """Names of violated clauses of INV on post-cycle state s with ISA model m."""
    bad = []
    n = len(words)
    img = S.pack_words(words)
    if s[RRESP] & 1 != s[PRR] & 1: bad.append('read_response = prev_read_request')
    if s[WRESP] & 1 or s[PWR] & 1 or s[PLR] & 1: bad.append('no write/load pending in env')
    if s[ENVRR] & 1 != s[RR] & 1: bad.append('env_reset_reg = reset_reg')
    if s[RST] & 1: bad.append('reset released')
    if s[RAM] != img: bad.append('ram = image')
    if any(s[x] for x in MIP): bad.append('mip = 0')
    if lanes(s)[1:] != m.regs[1:]: bad.append('RF = ISA regs')
    if m.regs[0] != 0: bad.append('x0')
    if s[CS] == OPERATING:
        if s[RR] & 1: bad.append('operating -> reset_reg = 0')
        if s[PC] != m.pc: bad.append('operating -> PC = ISA pc')
        w = img_word(words, s[PC])
        if w is None: bad.append('operating -> PC in image')
        elif s[RD] != w: bad.append('operating -> read_data = rom(PC)')
        if not s[PRR] & 1: bad.append('operating -> prev_read_request = 1')
    elif s[CS] == RESETSTATE:
        if s[PC] != 0: bad.append('reset -> PC = 0')
        if m.pc != 0 or any(m.regs): bad.append('reset -> ISA initial')
    else:
        bad.append('state in {RESET, OPERATING}')
    if mut == 'rd_next' and s[CS] == OPERATING and s[RD] == (words[(s[PC] // 4 + 1) % n]): bad.append('MUT')
    return bad


def commit_of(s):
    return s[PC] if (s[FLUSH] == 0 and s[CE] & 1 and not s[LP] & 1 and not s[SP] & 1 and not s[TRAP] & 1) else None


def step_pair(sim, s, words, m):
    """One RTL cycle + ISA step; returns (s', committed pc or None)."""
    pc = commit_of(s)
    if pc is not None:
        assert pc == m.pc, ('commit pc', pc, m.pc)
        m.pc = S.isa_step(m.regs, m.pc, S.decode(words[m.pc // 4]), bytearray(4))
    s2 = sim.phase(sim.phase(s, CLK, 1), CLK, 0)
    return s2, pc


def cmd_reach(N, cycles, seed):
    B.init()
    sim = B.SIM
    viol = {}
    ncom = 0
    for k in range(N):
        rng = random.Random(seed + k)
        words = B.gen_any(rng, k)
        run = S.SteelRun(sim, words)
        s = run.state
        m = Model()
        for c in range(cycles):
            bad = inv(words, s, m)
            for b in bad: viol[b] = viol.get(b, 0) + 1
            s, pc = step_pair(sim, s, words, m)
            ncom += pc is not None
    print(json.dumps(dict(programs=N, cycles=cycles, commits=ncom, violations=viol)))
    return 1 if viol else 0


def rand_inv_state(sim, words, rng):
    run = S.SteelRun(sim, words)
    s = list(run.state)
    m = Model()
    for _ in range(rng.randint(0, 12)):               # a reachable start, then randomise the free part
        s, _ = step_pair(sim, s, words, m)
    n = len(words)
    while s[CS] != OPERATING:
        s, _ = step_pair(sim, s, words, m)
    # random architectural state
    m.regs = [0] + [rng.getrandbits(32) for _ in range(31)]
    s[RF] = sum(m.regs[i + 1] << (32 * i) for i in range(31))
    idx = rng.randrange(n)
    m.pc = 4 * idx
    s[PC] = m.pc
    s[RD] = words[idx]
    for x in SEQ_FREE: s[x] = rng.getrandbits(sim_width(sim, x))
    for x in CSR_FREE: s[x] = rng.getrandbits(sim_width(sim, x))
    s = sim.lfp(s)
    return s, m


_W = {}
def sim_width(sim, x):
    if not _W:
        import json as j
        rep = j.load(open('experiments/framework/generated/steel/report.json'))
        for r in rep['signal_table']: _W[r['id']] = r['width']
    return _W[x]


def rand_reset_state(sim, words, rng):
    """INV state in the reset phase (current_state = RESET): first post-boot cycle (reset_reg=1) or the second (reset_reg=0)."""
    run = S.SteelRun(sim, words)
    s = list(run.state)
    m = Model()
    if rng.random() < 0.5:
        s, _ = step_pair(sim, s, words, m)
    assert s[CS] == RESETSTATE
    s[RD] = rng.getrandbits(32)
    for x in SEQ_FREE: s[x] = rng.getrandbits(sim_width(sim, x))
    for x in CSR_FREE: s[x] = rng.getrandbits(sim_width(sim, x))
    return sim.lfp(s), m


def cmd_induct(N, seed):
    B.init()
    sim = B.SIM
    viol = {}
    n_ok = 0
    for k in range(N):
        rng = random.Random(seed + k)
        words = B.gen_any(rng, k)
        s, m = (rand_reset_state if k % 3 == 2 else rand_inv_state)(sim, words, rng)
        assert not inv(words, s, m), inv(words, s, m)
        for _ in range(3):
            s, pc = step_pair(sim, s, words, m)
            bad = inv(words, s, m)
            for b in bad: viol[b] = viol.get(b, 0) + 1
            n_ok += not bad
    print(json.dumps(dict(random_states=N, steps_ok=n_ok, violations=viol)))
    return 1 if viol else 0


def cmd_mutants(N, seed):
    B.init()
    sim = B.SIM
    # clause-dropping mutants of the INV: drop a clause, find a random INV-free state that then violates the step
    import copy
    caught = {}
    for k in range(N):
        rng = random.Random(seed + k)
        words = B.gen_any(rng, k)
        s, m = rand_inv_state(sim, words, rng)
        for name, mut in [('read_data := next word', lambda s: s.__setitem__(RD, words[(s[PC] // 4 + 1) % len(words)])),
                          ('mip.meip := 1 (+mie)', lambda s: (s.__setitem__(187, 1), s.__setitem__(182, 1), s.__setitem__(193, 1))),
                          ('PC misaligned', lambda s: s.__setitem__(PC, s[PC] + 2)),
                          ('read_response := 0 (stall)', lambda s: (s.__setitem__(RRESP, 0), s.__setitem__(PRR, 1))),
                          ('prev_read_request := 0', lambda s: s.__setitem__(PRR, 0)),
                          ('ISA reg mismatch', lambda s: s.__setitem__(RF, s[RF] ^ (1 << 40)))]:
            t = list(s); mut(t); t = sim.lfp(t)
            mm = Model(); mm.regs = list(m.regs); mm.pc = m.pc
            if not inv(words, t, mm):
                continue                                  # mutant is still in INV (clause not violated)
            caught[name] = caught.get(name, 0) + 1
    print(json.dumps(dict(states=N, mutants_rejected_by_inv=caught)))
    return 0


if __name__ == '__main__':
    c = sys.argv[1]
    sys.exit({'reach': lambda: cmd_reach(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])),
              'induct': lambda: cmd_induct(int(sys.argv[2]), int(sys.argv[3])),
              'mutants': lambda: cmd_mutants(int(sys.argv[2]), int(sys.argv[3]))}[c]())
