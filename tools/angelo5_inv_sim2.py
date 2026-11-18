#!/usr/bin/env python3
"""angelo5fix: simulation check of the FULL candidate Coq INV (all register clauses), before writing it in Coq.
Extends tools/angelo5_inv_sim.py (TOK/D0/D1/D1'/D3) with the fetch front, the control vector, the decode-stage, CSR and bus clauses.
Positions: k(mem)=0, k(exe)=v4, k(dec)=v4+v3; sigma_k = ISA state after k steps from the model state (all committed).
Usage: angelo5_inv_sim2.py N CYCLES SEED [mutation]
proof_author='LLM-generated: Claude Code (claude-opus-5-5)'; external_llm_api_calls=0."""
import sys, random, json
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_ast_sim as S

M32 = S.M32
OPC = {'r': 1, 'i': 2, 'load': 4, 'store': 8, 'branch': 16, 'jal': 32, 'jalr': 64, 'lui': 128, 'auipc': 256, 'system': 512, 'fence': 1024}
ALU = ['add', 'sub', 'slt', 'sltu', 'xor', 'or', 'and', 'sll', 'srl', 'sra', 'eq', 'neq', 'ge', 'geu']
CLS = {  # mnemonic -> (opcode flag, alu flag)
    'add': ('r', 'add'), 'sub': ('r', 'sub'), 'sll': ('r', 'sll'), 'slt': ('r', 'slt'), 'sltu': ('r', 'sltu'), 'xor': ('r', 'xor'), 'srl': ('r', 'srl'),
    'sra': ('r', 'sra'), 'or': ('r', 'or'), 'and': ('r', 'and'), 'addi': ('i', 'add'), 'slti': ('i', 'slt'), 'sltiu': ('i', 'sltu'), 'xori': ('i', 'xor'),
    'ori': ('i', 'or'), 'andi': ('i', 'and'), 'slli': ('i', 'sll'), 'srli': ('i', 'srl'), 'srai': ('i', 'sra'), 'lui': ('lui', 'add'), 'auipc': ('auipc', 'add'),
    'jal': ('jal', 'add'), 'jalr': ('jalr', 'add'), 'beq': ('branch', 'eq'), 'bne': ('branch', 'neq'), 'blt': ('branch', 'slt'), 'bge': ('branch', 'ge'),
    'bltu': ('branch', 'sltu'), 'bgeu': ('branch', 'geu')}


def regs_of(s):
    r = (s[128] << 32) & ((1 << 1024) - 1)
    return [(r >> (32 * i)) & M32 for i in range(32)]


def isa_states(words, regs, pc, n):
    out = []
    regs = list(regs)
    for _ in range(n):
        out.append((pc, list(regs)))
        w = words[pc // 4]; d = S.decode(w)
        pc = S.isa_step(regs, pc, d, bytearray(4))
    out.append((pc, list(regs)))
    return out


def eff(words, st):
    """(mnemonic, rd, writes?, value) of the instruction at ISA state st"""
    pc, regs = st
    d = S.decode(words[pc // 4]); r2 = list(regs)
    S.isa_step(r2, pc, d, bytearray(4))
    name, rd = d[0], d[1]
    wr = name not in S.BRANCHES
    return name, rd, wr, (r2[rd] if rd else None), d


def mem(words, k):
    k &= 127
    return words[k] if k < len(words) else 0


def run(N, cycles, seed, mut=None):
    sim = S.load_sim(S.DEFAULT_AST['angelo5fix']); design = S.DESIGNS['angelo5fix']
    progs = S.program_set(design, N, seed)
    stats, ctl = {}, {}
    def bad(k): stats[k] = stats.get(k, 0) + 1
    states = 0
    for words in progs:
        r = S.Angelo5Run(sim, words); pc_m = 0; regs = [0] * 32
        for _ in range(cycles):
            s = r.state; states += 1
            b = lambda x: s[x] & 1
            v1, v2, v3, v4, ce, ack = b(143), b(171), b(237), b(305), b(150), b(5)
            ctl[(ce, ack, v1, v2, v3, v4)] = ctl.get((ce, ack, v1, v2, v3, v4), 0) + 1
            sig = isa_states(words, regs, pc_m, 4)
            k3, k2 = v4, v4 + v3
            # control
            if v2 and not (v1 and ce and ack): bad('ctl v2 -> v1 ce ack')
            if v1 and not (ce and ack): bad('ctl v1 -> ce ack')
            for x in (153, 313, 294, 295, 235, 358, 359, 418):
                if s[x] & 1: bad(f'zero {x}')
            # fetch front
            o_pc, prev, iad = s[134] & M32, s[147] & M32, s[133] & M32
            if mut == 'front': iad = (iad + 4) & M32
            if v1:
                fr = o_pc
                if prev != (o_pc + 4) & M32: bad('front prev=opc+4')
                if iad != (o_pc + 8) & M32: bad('front iaddr=opc+8')
                if s[136] & M32 != mem(words, o_pc >> 2): bad('o_inst = mem[o_pc]')
            elif ce and ack:
                fr = prev
                if iad != (prev + 4) & M32: bad('front iaddr=prev+4 (110)')
            elif ce:
                fr = prev
                if iad != prev: bad('front iaddr=prev (100)')
            else:
                fr = iad
            if s[6] & M32 != mem(words, prev >> 2): bad('inst = mem[prev]')
            if v2:
                if fr != (s[159] + 4) & M32: bad('fr = dec+4')
            else:
                if fr != sig[k2][0]: bad('fr = pc(sigma_k2)')
            # RF
            if regs_of(s)[1:] != regs[1:]: bad('RF')
            # mem token
            if v4:
                n, rd, wr, val, d = eff(words, sig[0])
                if s[286] & M32 != sig[0][0]: bad('mem pc')
                if (s[288] & 1) != (1 if wr else 0): bad('mem wr')
                if wr and s[290] & 31 != rd: bad('mem rd')
                if wr and rd and s[292] & M32 != val: bad('mem val')
                if (s[284] >> 2) & 1 or (s[284] >> 9) & 1: bad('mem opc load/system')
            if v3:
                n, rd, wr, val, d = eff(words, sig[k3])
                if s[227] & M32 != sig[k3][0]: bad('exe pc')
                if (s[230] & 1) != (1 if wr else 0): bad('exe wr')
                if wr and s[232] & 31 != rd: bad('exe rd')
                if wr and rd and s[233] & M32 != val: bad('exe val')
                if not (s[234] & 1): bad('exe rd_valid')
                if s[222] & (4 | 8 | 512): bad('exe opc')
                if s[224] & 15: bad('exe exc')
                if s[410] & 1: bad('exe 410')
            if v2:
                n, rd, wr, val, d = eff(words, sig[k2])
                w = words[sig[k2][0] // 4]
                if s[159] & M32 != sig[k2][0]: bad('dec pc')
                o, a = CLS[n]
                if s[168] & 2047 != OPC[o]: bad('dec opcode')
                if s[167] & 16383 != 1 << ALU.index(a): bad(f'dec alu {n}')
                if s[169] & 15: bad('dec exc')
                if s[164] & 31 != (w >> 7) & 31: bad('dec rd')
                if s[161] & 31 != (w >> 15) & 31 or s[126] & 31 != (w >> 15) & 31: bad('dec rs1')
                if s[163] & 31 != (w >> 20) & 31 or s[127] & 31 != (w >> 20) & 31: bad('dec rs2')
                if s[166] & 7 != (w >> 12) & 7: bad('dec f3')
            if s[90] & 1:
                pc_m = S.isa_step(regs, pc_m, S.decode(words[pc_m // 4]), bytearray(4))
            r.step()
    print(json.dumps(dict(programs=N, cycles=cycles, states=states, violations=stats, control_vectors={str(k): v for k, v in sorted(ctl.items())}), indent=1))


if __name__ == '__main__':
    run(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] if len(sys.argv) > 4 else None)
