#!/usr/bin/env python3
"""Simulation-first INV for the srv32 template route (before any Coq): the joint invariant INV(rtl state, ISA state) that the
Coq D step will prove, checked on random in-domain programs at every cycle boundary of the validated AST simulator, plus
mutation probes (AST mutants must violate it).  Untrusted; the clauses below are the specification of the Coq `Inv`.

  python tools/srv32_inv_sim.py reach 300 120          # INV holds on all reached states (programs x cycles)
  python tools/srv32_inv_sim.py inductive 600          # INV is inductive: random INV states, one step, INV again
  python tools/srv32_inv_sim.py mutants 60 100         # each AST mutant is rejected (some reached state violates INV)
Cycle index n = number of completed cycles (events = 2n).  n = 0,1,2 are the boot states (silent); n >= 3 the main states.
Observer: cycle n >= 3 commits the EX token iff ex_flush = 0, token pc = ex_pc (pre-state, after the previous falling edge).
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import random
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_ast_sim as S
import cpu_srv32_bughunt as BH

M = S.M32
FETCH, IFPC, EXPC, IRD, EXINSN, FLUSH, STALLR, PIPEF = 239, 240, 241, 12, 249, 234, 232, 235
WBA, WBR, WBD, WBM, WBRD, WBB, WBN, WBT, WBNO, WBMO = 289, 290, 294, 293, 304, 295, 296, 297, 298, 299
EXFL, EXC, REGS, EXMEM = 272, 3, 244, 258
OPC = dict(auipc=0x17, lui=0x37, jal=0x6f, jalr=0x67, branch=0x63, load=0x03, store=0x23, arithi=0x13, arithr=0x33, fence=0x0f, system=0x73)


def bits(w, lo, n):
    return (w >> lo) & ((1 << n) - 1)


def rom(words, a):
    a &= M
    if a >> 9:
        return 0
    i = (a >> 2) & 127
    return words[i] if i < len(words) else 0


def lane(s, k):
    return (s[REGS] >> (32 * k)) & M


def pulses(s):
    return (s[WBB] & 1, s[WBN] & 1, s[WBMO] & 1)


def ctl_state(s):
    """S0 (000) normal, S1 (100) EX junk1, S2 (010) EX junk2, S3 (001) EX valid, WB junk"""
    return {(0, 0, 0): 0, (1, 0, 0): 1, (0, 1, 0): 2, (0, 0, 1): 3}.get(pulses(s))


def mirror_decode(w):
    """expected ex_* register values for the instruction word w (mirror of riscv.v stage 1; RV32M=0)"""
    op, f3, f7 = bits(w, 0, 7), bits(w, 12, 3), bits(w, 25, 7)
    if op == OPC['auipc'] or op == OPC['lui']:
        imm = w & 0xfffff000
    elif op == OPC['jal']:
        imm = (bits(w, 31, 1) * 0xfff00000) | (bits(w, 12, 8) << 12) | (bits(w, 20, 1) << 11) | (bits(w, 21, 10) << 1)
    elif op in (OPC['jalr'], OPC['load']):
        imm = (bits(w, 31, 1) * 0xfffff000) | bits(w, 20, 12)
    elif op == OPC['branch']:
        imm = (bits(w, 31, 1) * 0xfffff000) | (bits(w, 7, 1) << 11) | (bits(w, 25, 6) << 5) | (bits(w, 8, 4) << 1)
    elif op == OPC['store']:
        imm = (bits(w, 31, 1) * 0xfffff000) | (bits(w, 25, 7) << 5) | bits(w, 7, 5)
    elif op == OPC['arithi']:
        imm = bits(w, 20, 5) if f3 in (1, 5) else (bits(w, 31, 1) * 0xfffff000) | bits(w, 20, 12)
    elif op == OPC['system']:
        imm = bits(w, 20, 12)
    else:
        imm = 0
    return {'imm': imm & M, 'imm_sel': int(op in (OPC['jalr'], OPC['load'], OPC['arithi'])), 's1': bits(w, 15, 5), 's2': bits(w, 20, 5),
            'dst': bits(w, 7, 5), 'alu_op': f3, 'subtype': int(bits(w, 30, 1) and not (op == OPC['arithi'] and f3 == 0)),
            'memwr': int(op == OPC['store']), 'alu': int(op == OPC['arithi'] or (op == OPC['arithr'] and f7 in (0, 0x20))),
            'lui': int(op == OPC['lui']), 'auipc': int(op == OPC['auipc']), 'jal': int(op == OPC['jal']), 'jalr': int(op == OPC['jalr']),
            'branch': int(op == OPC['branch']), 'system': int(op == OPC['system'] and f3 == 0), 'mem2reg': int(op == OPC['load'])}


EXREG = dict(imm=250, imm_sel=251, s1=252, s2=253, dst=254, alu_op=255, subtype=256, memwr=257, mem2reg=258, alu=261, lui=264,
             auipc=265, jal=266, jalr=267, branch=268, system=269)


def inv(s, words, regs, pc, n):
    """violations (list of clause names) of INV(s, isa=(regs, pc)) at cycle index n (state after the n-th falling edge)"""
    v = []
    if n < 3:
        want = {0: dict(stall=1, flush=1), 1: dict(stall=0, flush=1), 2: dict(stall=0, flush=0)}[n]
        if (s[STALLR] & 1, s[FLUSH] & 1) != (want['stall'], want['flush']):
            v.append('boot_flags')
        if n == 2 and (s[IRD] & M != rom(words, 0) or s[IFPC] & M != 0 or s[FETCH] & M != 4 or s[EXFL] & 1):
            v.append('boot_b2')
        if any(regs[1:]) or pc:
            v.append('boot_isa')
        return v
    c = ctl_state(s)
    if c is None:
        return ['pulses']
    if s[WBN] & 1 != s[WBNO] & 1:
        v.append('nop_eq_nxt')
    if s[STALLR] & 1 or s[FLUSH] & 1 or s[PIPEF] & 3 != 2 or s[EXC] & 1:
        v.append('housekeeping')
    if s[WBT] & 1 or s[EXMEM] & 1 != int(OPC['load'] == bits(s[EXINSN], 0, 7)):
        v.append('trap_nop_or_mem2reg')
    if s[EXFL] & 1 != int(c in (1, 2)):
        v.append('ex_flush')
    ex, ifp, fe = s[EXPC] & M, s[IFPC] & M, s[FETCH] & M
    if s[IRD] & M != rom(words, ifp):
        v.append('fetch_contract')
    if s[EXINSN] & M != rom(words, ex):
        v.append('ex_insn_rom')
    if ifp != (ex + 4) & M and c != 2:
        v.append('if_pc_rel')
    if c in (0, 3):
        if ex != pc or fe != (ex + 8) & M:
            v.append('pc_rel_N')
    elif c == 1:
        if fe != pc:
            v.append('pc_rel_S1')
    else:
        if ifp != pc or fe != (ifp + 4) & M:
            v.append('pc_rel_S2')
    # coherence of the EX stage registers with ex_insn
    mir = mirror_decode(s[EXINSN] & M)
    bad = [k for k, r in EXREG.items() if (s[r] & ((1 << 32) - 1) if k == 'imm' else s[r]) != mir[k]]
    if bad:
        v.append('coherence:' + ','.join(bad))
    # register file relation: lanes + pending WB write == ISA registers
    wbw = s[WBA] & 1 and not (s[WBNO] & 1 or s[WBMO] & 1)
    wval = s[WBRD] & M if s[WBM] & 1 else s[WBR] & M
    for r in range(1, 32):
        val = wval if (wbw and (s[WBD] & 31) == r) else lane(s, r - 1)
        if val != regs[r]:
            v.append(f'regsrel:x{r}')
            break
    return v


def run_prog(sim, words, cycles, collect=None):
    """returns the list of (n, violations); drives the ISA reference with the observer's commits"""
    run = S.Srv32Run(sim, words)
    regs, pc = [0] * 32, 0
    out = []
    for n in range(cycles):
        s = run.state
        out.append((n, inv(s, words, regs, pc, n)))
        if collect is not None:
            collect.append((n, list(s), list(regs), pc))
        if n >= 3 and not (s[EXFL] & 1):
            tok = s[EXPC] & M
            if tok != pc:
                out[-1] = (n, out[-1][1] + ['token_pc'])
            ins = S.decode(rom(words, pc))
            pc = S.isa_step(regs, pc, ins)
        run.step()
    return out


def enc_b(f3, rs1, rs2, imm):
    return (((imm >> 12) & 1) << 31) | (((imm >> 5) & 63) << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | (((imm >> 1) & 15) << 8) | (((imm >> 11) & 1) << 7) | 0x63


def directed():
    """sign-sensitive programs: x1 = -1, x2 = 1, x3 = 0x80000000, then every branch both ways and slt/sltu/sra/srl"""
    out = []
    for f3 in (0, 1, 4, 5, 6, 7):
        for a, b in ((1, 2), (2, 1), (1, 3), (3, 1), (1, 1)):
            out.append([0xfff00093, 0x00100113, 0x800001b7, enc_b(f3, a, b, 8), 0x00700213, 0x00900293, 0x0000006f])
    out.append([0xfff00093, 0x00100113, 0x800001b7, 0x0020a233, 0x0020b2b3, 0x4010d333, 0x0010d3b3, 0x0000006f])
    return out


def gen(rng, i):
    return BH.gen_hazard(rng) if i % 2 else S.gen_program(rng)


def cmd_reach(a, sim=None):
    sim = sim or S.load_sim(S.DEFAULT_AST['srv32'])
    rng = random.Random(a.seed)
    bad, tot = {}, 0
    for i in range(a.programs):
        words = gen(rng, i)
        for n, v in run_prog(sim, words, a.cycles):
            tot += 1
            for x in v:
                bad[x.split(':')[0]] = bad.get(x.split(':')[0], 0) + 1
    print(f'reach: {a.programs} programs x {a.cycles} cycles = {tot} states; violations by clause: {bad or 0}')
    return 1 if bad else 0


def cmd_inductive(a, sim=None):
    """random INV states (reached state with the data parts re-randomised consistently), one real cycle, INV again"""
    sim = sim or S.load_sim(S.DEFAULT_AST['srv32'])
    rng = random.Random(a.seed)
    bad, tot = {}, 0
    for i in range(a.programs):
        words = gen(rng, i)
        col = []
        run_prog(sim, words, 40, col)
        n, s, regs, pc = rng.choice([c for c in col if c[0] >= 3])
        s = list(s)
        rf = 0
        for k in range(32):
            rf |= rng.getrandbits(32) << (32 * k)
        s[REGS] = rf
        s[WBR], s[WBRD] = rng.getrandbits(32), rng.getrandbits(32)
        s[WBA], s[WBD] = rng.getrandbits(1), rng.getrandbits(5)
        s = sim.lfp(s)
        wbw = s[WBA] & 1 and not (s[WBNO] & 1 or s[WBMO] & 1)
        wval = s[WBRD] & M if s[WBM] & 1 else s[WBR] & M
        regs = [0] + [wval if (wbw and (s[WBD] & 31) == r) else lane(s, r - 1) for r in range(1, 32)]
        if inv(s, words, regs, pc, n):
            continue                       # (cannot happen: regsrel holds by construction)
        mid = sim.phase(s, 0, 1)
        t = sim.phase(mid, 0, 0)
        regs2, pc2 = list(regs), pc
        if not s[EXFL] & 1:
            pc2 = S.isa_step(regs2, pc, S.decode(rom(words, pc)))
        v = inv(t, words, regs2, pc2, n + 1)
        tot += 1
        for x in v:
            bad[x.split(':')[0]] = bad.get(x.split(':')[0], 0) + 1
    print(f'inductive: {tot} random INV states, one cycle; violations by clause: {bad or 0}')
    return 1 if bad else 0


MUTANTS = [   # (name, signal written by the mutated process, old text, new text, occurrence)
    ('fwd_rs1_off', '32 245', '(EBinary 1 BEq (EVar 5 294) (EVar 5 252))', '(EBinary 1 BEq (EVar 5 294) (EConst 5 31))', 0),
    ('fwd_rs2_off', '32 246', '(EBinary 1 BEq (EVar 5 294) (EVar 5 253))', '(EBinary 1 BEq (EVar 5 294) (EConst 5 31))', 0),
    ('ex_flush_one_slot', '1 272', '(EBinary 1 BOr (EVar 1 295) (EVar 1 296))', '(EVar 1 295)', 0),
    ('wb_flush_one_slot', '1 305', '(EBinary 1 BOr (EVar 1 298) (EVar 1 299))', '(EVar 1 298)', 0),
    ('flush_fetch_plus8', '32 239', '(EBinary 32 BAdd (EConst 32 4) (EVar 32 239)) (ECond', '(EBinary 32 BAdd (EConst 32 8) (EVar 32 239)) (ECond', 0),
    ('link_plus8', '32 323', '(EBinary 32 BAdd (EConst 32 4) (EVar 32 241))', '(EBinary 32 BAdd (EConst 32 8) (EVar 32 241))', 0),
    ('blt_unsigned', '32 324', '(ESel 1 (EVar 33 321) (EConst 6 32))', '(ESel 1 (EVar 33 322) (EConst 6 32))', 0),
    ('rf_write_index', '1024 244', '(EBinary 5 BSub (EVar 5 294) (EConst 5 1))', '(EBinary 5 BSub (EVar 5 294) (EConst 5 2))', 0),
    ('wb_branch_never', '1 295', '(EBinary 1 BOr', '(EBinary 1 BAnd', 0),
]


def cmd_mutants(a):
    import re
    src = Path(S.DEFAULT_AST['srv32']).read_text()
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    rows = []
    for name, lv, old, new, occ in MUTANTS:
        procs = [(m.start(), m.group(0)) for m in re.finditer(r'Definition process_(\d+) : Process := .*', src)]
        hit = [(st, t) for st, t in procs if f'(LVar {lv})' in t and old in t]
        if not hit:
            rows.append((name, 'NO-SITE', {})); continue
        st, t = hit[0]
        t2 = t.replace(old, new, 1)
        path = out / f'mut_{name}.v'
        path.write_text(src[:st] + t2 + src[st + len(t):])
        sim = S.load_sim(str(path))
        rng = random.Random(a.seed)
        bad = {}
        dirs = directed()
        for i in range(a.programs + len(dirs)):
            words = dirs[i] if i < len(dirs) else gen(rng, i)
            for n, v in run_prog(sim, words, a.cycles):
                for x in v:
                    k = x.split(':')[0]
                    bad[k] = bad.get(k, 0) + 1
        rows.append((name, 'REJECTED' if bad else 'SURVIVED', bad))
    for r in rows:
        print(r)
    return 1 if any(r[1] != 'REJECTED' for r in rows) else 0


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd')
    ap.add_argument('programs', type=int)
    ap.add_argument('cycles', type=int, nargs='?', default=100)
    ap.add_argument('--seed', type=int, default=11)
    ap.add_argument('--out', default='/tmp/claude-0/-workspace-TP/97d2f0d7-21f5-44fd-9196-e0c1c4022556/scratchpad/mut')
    a = ap.parse_args()
    return {'reach': cmd_reach, 'inductive': cmd_inductive, 'mutants': cmd_mutants}[a.cmd](a)


if __name__ == '__main__':
    sys.exit(main())
