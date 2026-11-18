#!/usr/bin/env python3
"""angelo5fix: simulation-first test of the pipeline token invariant (before any Coq), modelled on steel_inv_sim.py.
Register stages (oldest first): MEM/WB (m4 outputs, writeback_ce 90 = m4.o_ce 305), EXEC (m3 outputs), DEC (m2 outputs), FETCH (m1 outputs).
Candidate clause TOK: the CE=1 tokens, oldest first, carry exactly the ISA path pcs  path[0], path[1], ...  (path[0] = model pc = next to commit),
except that a younger token may be a wrong-path token when a flush (242) is combinationally active in the same state (it is killed at the edge).
Usage: angelo5_inv_sim.py reach N CYCLES SEED
proof_author='LLM-generated: Claude Code (claude-sonnet-5-5)'; external_llm_api_calls=0."""
import sys, random, json
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_ast_sim as S

M32 = S.M32
STAGES = [('mem', 305, 286), ('exe', 237, 227), ('dec', 171, 159), ('fet', 143, 134)]
FLUSH, STALL, CHG = 242, 240, 229
RF = 128


def regs_of(s):
    r = (s[RF] << 32) & ((1 << 1024) - 1)
    return [(r >> (32 * i)) & M32 for i in range(32)]


def path(words, regs, pc, n):
    regs = list(regs); out = []
    for _ in range(n):
        out.append(pc)
        if not (0 <= pc // 4 < len(words)) or pc % 4: break
        pc = S.isa_step(regs, pc, S.decode(words[pc // 4]), bytearray(4))
    return out


def steps(words, regs, pc, n):
    """ISA path with effects: list of (pc, word, regs_before, rd or None, value)."""
    regs = list(regs); out = []
    for _ in range(n):
        if not (0 <= pc // 4 < len(words)) or pc % 4: break
        w = words[pc // 4]; before = list(regs)
        npc = S.isa_step(regs, pc, S.decode(w), bytearray(4))
        ch = [i for i in range(1, 32) if regs[i] != before[i]]
        d = S.decode(w)
        out.append((pc, w, before, d, ch[0] if ch else None, regs[ch[0]] if ch else None, list(regs)))
        pc = npc
    return out


def run(N, cycles, seed, mut=None):
    sim = S.load_sim(S.DEFAULT_AST['angelo5fix']); design = S.DESIGNS['angelo5fix']
    progs = S.program_set(design, N, seed)
    stats = {}; commits = 0
    def bump(k): stats[k] = stats.get(k, 0) + 1
    for words in progs:
        r = S.Angelo5Run(sim, words); pc_m = 0; regs = [0] * 32
        for _ in range(cycles):
            s = r.state
            toks = [(n, s[b] & M32) for n, c, b in STAGES if s[c] & 1]
            p = path(words, regs, pc_m, 5)
            fl = s[FLUSH] & 1
            if mut == 'pcshift' and toks: toks[0] = (toks[0][0], toks[0][1] + 4)
            st = steps(words, regs, pc_m, 5)
            if mut == 'val': st = [x[:5] + ((x[5] + 1) & M32 if x[5] is not None else None,) + x[6:] for x in st]
            if mut == 'stale': st = [(x[0], x[1], regs, *x[3:]) for x in st]   # operands read from the committed file only (no older in-flight effects)
            if mut == 'rfskip' and s[90] & 1: regs = list(regs)
            pos = {n: i for i, (n, _) in enumerate(toks)}
            # D0: RF equals the ISA registers before the commit of this state (writes land at the edge)
            if regs_of(s)[1:] != regs[1:]: bump('viol RF = ISA regs')
            # D1: alu token (m3 outputs): wr_rd/rd_addr/rd_valid/rd vs ISA effect
            for nm, pi, (wr, ra, val, vld) in (('exe', 1, (66, 67, 68, 69)), ('mem', 0, (77, 78, 79, None))):
                if nm in pos and pos[nm] < len(st):
                    e = st[pos[nm]]
                    if s[wr] & 1 != (1 if (e[4] is not None or (e[3][1] and e[3][0] not in ('BEQ','BNE','BLT','BGE','BLTU','BGEU','SW','SH','SB'))) else 0) and e[4] is not None:
                        bump(f'viol {nm} wr_rd=0 but ISA writes')
                    if e[4] is not None and s[wr] & 1:
                        if s[ra] != e[4]: bump(f'viol {nm} rd_addr')
                        if (vld is None or s[vld] & 1) and nm == 'exe' and s[val] & M32 != e[5]: bump(f'viol {nm} rd value ({e[3][0]})')
                        if nm == 'mem' and e[3][0] not in ('LW','LH','LB','LHU','LBU') and s[val] & M32 != e[5]: bump(f'viol {nm} rd value ({e[3][0]})')
            # D3: dec token operands after forwarding (valid unless a force stall is raised)
            if 'dec' in pos and pos['dec'] < len(st) and not (s[105] & 1):
                e = st[pos['dec']]
                a, b = e[3][2], e[3][3]
                if e[3][0] in ('ADD','SUB','AND','OR','XOR','SLL','SRL','SRA','SLT','SLTU','BEQ','BNE','BLT','BGE','BLTU','BGEU','SW','SH','SB'):
                    bump('dec rs2 used')
                bump('dec checked')
                if s[106] & M32 != e[2][a] and a: bump(f'viol dec rs1 forwarded ({e[3][0]})')
                if s[107] & M32 != e[2][b] and b: bump(f'viol dec rs2 forwarded ({e[3][0]})')
            ok = True
            for i, (n, pc) in enumerate(toks):
                if i < len(p) and pc == p[i]: continue
                ok = False
                bump(f'dev {n} idx{i} flush={fl} stall={s[STALL]&1}')
                break
            bump('ok' if ok else 'viol')
            if s[90] & 1:
                assert s[76] & M32 == pc_m, ('commit pc', s[76], pc_m)
                pc_m = S.isa_step(regs, pc_m, S.decode(words[pc_m // 4]), bytearray(4)); commits += 1
            r.step()
    print(json.dumps(dict(programs=N, cycles=cycles, commits=commits, stats=stats), indent=1))


if __name__ == '__main__':
    if sys.argv[1] == 'reach': run(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    if sys.argv[1] == 'mut': run(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5])
