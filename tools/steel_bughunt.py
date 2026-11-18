#!/usr/bin/env python3
"""Steel: (1) AST simulator vs Verilator-4.028 C++ model cross-validation, (2) differential bug hunt vs the independent
RV32I reference on the 29-class jump-family domain, (3) failing-program minimiser.
Usage: steel_bughunt.py xval N CYCLES SEED CXX_BIN | hunt N CYCLES SEED | minimise HEXWORDS...
proof_author='LLM-generated: Claude Code (claude-sonnet-5-5)'; external_llm_api_calls=0.
"""
import sys, json, random, time, subprocess, multiprocessing as mp
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_ast_sim as S

SIM = None
def init():
    global SIM
    SIM = S.load_sim(S.DEFAULT_AST['steel'])

def gen_stress(rng):
    """Hazard-heavy: tiny register pool (2-3 regs), dense branches/JALR/JAL, back-to-back dependent ops."""
    while True:
        n = rng.randint(3, rng.choice([8, 16, 40, 101]))
        pool = [0] + rng.sample(range(1, 32), rng.choice([1, 2, 3]))
        wt = dict(data=rng.choice([30, 50]), br=rng.choice([25, 40]), jal=rng.choice([5, 10]), jalr=rng.choice([5, 12]))
        words = []
        for i in range(n):
            k = rng.choices(list(wt), list(wt.values()))[0]
            if i == n - 1:
                k = rng.choice(['jal', 'jalr'])
            words.append(S.gen_instruction(rng, k, i, n, pool))
        if S.jump_family_check(words):
            return words

def gen_any(rng, k):
    return S.gen_program(rng) if k % 2 == 0 else gen_stress(rng)

def traces_ast(words, cycles):
    return S.trace(S.DESIGNS['steel'], SIM, words, cycles)

def check(words, cycles):
    """None if OK, else mismatch text.  Beyond validate_against_isa: no trap, and no stall (commits >= cycles-6)."""
    d = S.DESIGNS['steel']
    run = S.SteelRun(SIM, words)
    tr = []
    for _ in range(cycles):
        pc, rf, mem = run.step()
        tr.append((pc, S.rf_from_int(rf), mem))
    if run.trapped:
        return 'core took a trap (take_trap asserted)'
    err = S._compare_trace_to_isa(d, words, tr)
    if err:
        return err
    commits = sum(1 for t in tr if t[0] is not None)
    if commits < cycles - 6:
        return f'stall: only {commits} commits in {cycles} cycles'
    return None

def hunt_one(a):
    k, seed, cycles = a
    rng = random.Random(seed)
    words = gen_any(rng, k)
    try:
        err = check(words, cycles)
    except Exception as e:
        err = 'EXC ' + repr(e)[:200]
    return k, seed, err, words

def cmd_hunt(n, cycles, seed):
    jobs = [(k, seed + k, cycles) for k in range(n)]
    t = time.time(); bad = []; commits = 0; mn = {}
    with mp.get_context('fork').Pool(2, initializer=init) as p:
        for k, sd, err, words in p.imap_unordered(hunt_one, jobs, chunksize=4):
            if err: bad.append(dict(kind='stress' if k % 2 else 'jumpfam', seed=sd, err=err, words=[hex(w) for w in words]))
    # instruction mix of the ISA trace (commits per mnemonic), computed on the same programs
    for k in range(n):
        words = gen_any(random.Random(seed + k), k)
        pcs, _, _ = S.isa_trace(words, cycles - 6)
        for pc in pcs:
            m = S.decode(words[pc // 4])[0]; mn[m] = mn.get(m, 0) + 1; commits += 1
    print(json.dumps(dict(programs=n, cycles_each=cycles, total_cycles=n * cycles, isa_instructions_covered=commits,
                          by_mnemonic=dict(sorted(mn.items())), mismatches=len(bad), seconds=round(time.time() - t),
                          first_bad=bad[:5]), indent=1))
    return 1 if bad else 0

def cmd_xval(n, cycles, seed, cxx):
    init()
    progs = [gen_any(random.Random(seed + k), k) for k in range(n)]
    inp = '\n'.join(' '.join('%x' % w for w in p) for p in progs) + '\n'
    out = subprocess.run([cxx, str(cycles)], input=inp, capture_output=True, text=True, timeout=3000).stdout.split('P\n')[1:]
    assert len(out) == n, (len(out), n)
    bad = []; cyc = 0
    for k, (p, o) in enumerate(zip(progs, out)):
        lines = o.strip().split('\n')
        tr = traces_ast(p, cycles)
        for c, (line, (pc, rf, _)) in enumerate(zip(lines, tr)):
            f = line.split()
            cpc = None if f[0] == '-1' else int(f[0])
            crf = [0] + [int(x, 16) for x in f[1:]]
            cyc += 1
            if cpc != pc or crf != rf:
                bad.append(dict(program=k, cycle=c, ast=(pc, rf[:4]), cxx=(cpc, crf[:4]))); break
    print(json.dumps(dict(programs=n, cycles_each=cycles, compared_cycles=cyc, mismatches=len(bad), bad=bad[:5])))
    return 1 if bad else 0

def cmd_min(words, cycles=300):
    init()
    words = list(words)
    assert check(words, cycles), 'program does not fail'
    changed = True
    while changed:
        changed = False
        for i in range(len(words)):          # try replacing by NOP (addi x0,x0,0), keeping the domain
            if words[i] == 0x13: continue
            w = words[:i] + [0x13] + words[i + 1:]
            if S.jump_family_check(w) and check(w, cycles):
                words, changed = w, True
        for i in range(len(words) - 1, 0, -1):   # try deleting trailing instruction
            pass
    print([hex(w) for w in words], check(words, cycles))

if __name__ == '__main__':
    c = sys.argv[1]
    if c == 'xval': raise SystemExit(cmd_xval(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]))
    if c == 'hunt': raise SystemExit(cmd_hunt(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])))
    if c == 'minimise': cmd_min([int(x, 16) for x in sys.argv[2:]])
