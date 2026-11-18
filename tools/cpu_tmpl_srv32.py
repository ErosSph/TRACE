#!/usr/bin/env python3
"""srv32 template-route driver (additive): thin wrappers that instantiate the role-parameterised / generalized generators
for srv32 and run them through the acceptance gate (tools/cpu_tmpl_accept.py; run with TMPL_DEFER_COQCHK=1).
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import json
import sys
from pathlib import Path
from pathlib import Path
import cpu_tmpl_accept as acc

if __import__('os').environ.get('SRV32_SKIP_DEPS') == '1':    # deps were built by the first gate of the session
    acc.ensure_generic_deps = lambda: None
LOAD = [('experiments/framework/generated/srv32', 'Srv32')]
STAMP = '20261104'


def provider(result_dir, namespace):
    return dict(directory=str(result_dir), namespace=namespace)


LEDGER = Path('framework/template-route-ledger.json')


def ledger_add(entry):
    """append one ledger entry (re-read right before writing: other agents edit this file)"""
    led = json.loads(LEDGER.read_text())
    ids = {m.get('id') for m in led['modules']}
    if entry['id'] in ids:
        led['modules'] = [entry if m.get('id') == entry['id'] else m for m in led['modules']]
    else:
        led['modules'].append(entry)
    LEDGER.write_text(json.dumps(led, indent=1) + '\n')


def gate(name, namespace, module, text, exports, providers=(), extra=None, ver='a1', prov='automatic', note='', classes=0, kind='generated'):
    out = f'results/r-tmpl-srv32-{name}-{STAMP}-{ver}'
    r = acc.accept(out, namespace, module, text, exports, LOAD, providers=providers,
                   extra=dict(design='srv32', **(extra or {})))
    print(json.dumps({k: r[k] for k in r if k not in ('per_class', 'info')}, indent=1))
    ledger_add(dict(id=f'srv32-{name}-{ver}', kind=kind, generator=(extra or {}).get('generator', ''), result_dir=out, provenance=prov,
                    accepted=bool(r.get('accepted')), coqc_accepted=bool(r.get('coqc_accepted')), coqchk_deferred=bool(r.get('coqchk_deferred')),
                    coqc_seconds=round(r.get('coqc_seconds', 0), 1), classes=classes, note=note, design='srv32'))
    return r


def lfp(ver='a1'):
    import cpu_tmpl_lfpnl as L
    text, ex = L.build('srv32', 'Srv32Lfp', 1)
    # the generalized generator relies on the AST module being opened; make it explicit (additive fix)
    text = text.replace('ExtendedSVPhaseLength.\nModule', 'ExtendedSVPhaseLength Srv32AST.\nModule')
    return gate('lfp', 'TmplSrv32Lfp', 'Srv32Lfp', text, ex, extra=dict(generator='tools/cpu_tmpl_lfpnl.py (Steel agent, generalized_rule) via tools/cpu_tmpl_srv32.py'), ver=ver)


def edge(ver='a1'):
    import cpu_tmpl_edge as E
    text, ex, info = E.build('srv32', 'Srv32TmplEdge')
    return gate('edge', 'TmplSrv32Edge', 'Srv32TmplEdge', text, ex, extra=dict(generator='tools/cpu_tmpl_edge.py (generalized_rule, Bzeeno route)', info=info), ver=ver)


EDGE = 'TmplSrv32Edge.Srv32TmplEdge.Srv32TmplEdge'
EDGE_DIR = f'results/r-tmpl-srv32-edge-{STAMP}-a1'
# processes whose body the decision-tree converter does not handle (case statement / CSR / pipefill / RF bank): not needed
# for the jump-family domain (store data path, CSR and counters are unobserved); the RF bank has its own layer.
STAGE_PROCS = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11]


def stage(ver='a1'):
    import cpu_tmpl_stage as S
    text, ex, info = S.build('srv32', 'Srv32TmplStage', EDGE, rise_procs=STAGE_PROCS)
    return gate('stage', 'TmplSrv32Stage', 'Srv32TmplStage', text, ex, providers=[provider(EDGE_DIR, 'TmplSrv32Edge')],
                extra=dict(generator='tools/cpu_tmpl_stage.py (generalized_rule, Bzeeno route)', info=info,
                           skipped_processes=[10, 12, 13, 14, 15]), ver=ver)


def frame(ver='a1'):
    import cpu_tmpl_stage as S
    text, ex, info = S.frame_text('srv32', 'Srv32TmplFrame', EDGE)
    return gate('frame', 'TmplSrv32Frame', 'Srv32TmplFrame', text, ex, providers=[provider(EDGE_DIR, 'TmplSrv32Edge')],
                extra=dict(generator='tools/cpu_tmpl_stage.py --frame (generalized_rule, Bzeeno route)', info=info), ver=ver)


def ex(ver='a1'):
    import cpu_tmpl_srv32_ex as X
    text, ex_, info = X.run('all', 'Srv32Ex')
    return gate('ex', 'TmplSrv32Ex', 'Srv32Ex', text, ex_, extra=dict(generator='tools/cpu_tmpl_srv32_ex.py on the planner of tools/cpu_tmpl_bzex.py', per_class=info),
                prov='llm_adapted', classes=29, ver=ver,
                note='EX facts for all 29 classes: ex_result (323) for the 21 data ops + Jal/Jalr link; next_pc (324) and branch_taken (325) for the 6 branches in both outcomes; the 33-bit '
                     'subtraction wires 321/322. Flags are the determined ex_* values of the class. srv32 specs new (llm_adapted), planner/emitter of the Bzeeno route unchanged; '
                     'new generic library CPUSubSign33 (llm_written) for the compare sign bits')


STAGE_DIR = f'results/r-tmpl-srv32-stage-{STAMP}-a1'


def cap(ver='a1'):
    import cpu_tmpl_srv32_cap as C
    text, ex_ = C.text('Srv32Cap')
    return gate('cap', 'TmplSrv32Cap', 'Srv32Cap', text, ex_, providers=[provider(EDGE_DIR, 'TmplSrv32Edge'), provider(STAGE_DIR, 'TmplSrv32Stage')],
                extra=dict(generator='tools/cpu_tmpl_srv32_cap.py (+ rise_R of the stage layer, ExtendedSVSymExec.xeval)'), prov='llm_written', classes=29, ver=ver,
                note='capture (decode) facts for 29 classes: after the rising edge the ex_* flag registers (memwr, jal, jalr, lui, auipc, csr, mul, alu, alu_op, subtype, branch, imm_sel, illegal) '
                     'hold the class values given the opcode/funct3/funct7/bit30 slices of the instruction word; new generator srv32-specific (xeval under slice facts)')


def rf(ver='a1'):
    import cpu_tmpl_srv32_rf as R
    text, ex_ = R.text('Srv32Rf')
    return gate('rf', 'TmplSrv32Rf', 'Srv32Rf', text, ex_, providers=[provider(EDGE_DIR, 'TmplSrv32Edge')],
                extra=dict(generator='tools/cpu_tmpl_srv32_rf.py + framework/template-sources/Srv32RfCore.v.in; library src/Lang/ExtendedSVBankWriteBlk.v'),
                prov='llm_adapted', ver=ver,
                note='RF write step at the rising edge: rf_write_lane (lane i = i == (wb_dst_sel-1) mod 32 ? norm 32 data : old) and rf_write_off (guard false: bank unchanged); '
                     'expressions read from the AST; new generic library ExtendedSVBankWriteBlk (block-wrapped slice write, variant of ExtendedSVBankWriteStep shape B)')


def _provs(*names):
    """providers of the srv32 template modules built so far: (namespace, result directory)"""
    return [provider(d, ns) for ns, d in names]


BASE_PROVS = [('TmplSrv32Lfp', 'results/r-tmpl-srv32-lfp-20261104-a1'), ('TmplSrv32Edge', EDGE_DIR), ('TmplSrv32Stage', STAGE_DIR),
              ('TmplSrv32Frame', 'results/r-tmpl-srv32-frame-20261104-a1')]


def base(ver='a1'):
    import cpu_tmpl_srv32_step as S
    text, ex_ = S.base_text('Srv32Base')
    return gate('base', 'TmplSrv32Base', 'Srv32Base', text, ex_, providers=_provs(*BASE_PROVS),
                extra=dict(generator='tools/cpu_tmpl_srv32_step.py base (Lo/Hi/Basic phase invariants incl. post-phase NetWords; per-register one-cycle lemmas cyc_R)'),
                prov='generalized_rule', ver=ver,
                note='item 4: basic invariant (length, comb fixed point, NetWords) preserved by clock/reset phases; clock/reset/rom after a phase; driven registers; cyc_R = value after one cycle '
                     '(rise tree on the driven state, fall frame) for the 41 stage registers')


def wire(ver='a1'):
    import cpu_tmpl_srv32_wire as W
    text, ex_, info = W.run('Srv32Wire')
    return gate('wire', 'TmplSrv32Wire', 'Srv32Wire', text, ex_, extra=dict(generator='tools/cpu_tmpl_srv32_wire.py on the planner of tools/cpu_tmpl_bzex.py', per_class=info),
                prov='llm_adapted', ver=ver,
                note='comb-wire facts of a settled state: stall wires = 0, inst without flush, imem_addr copy, constant wires, ROM word value, flush_zero/ld_m2r0/st_mw0, and junk_bt0 '
                     '(branch_taken = 0 in every flushed token whatever the decoded flags; 17 scenario theorems over process 80)')


BASE_DIR = 'results/r-tmpl-srv32-base-20261104-a2'
RF_DIR = 'results/r-tmpl-srv32-rf-20261104-a1'
EX_DIR = 'results/r-tmpl-srv32-ex-20261104-a4'
CAP_DIR = 'results/r-tmpl-srv32-cap-20261104-a1'
WIRE_DIR = 'results/r-tmpl-srv32-wire-20261104-a2'
ALL_PROVS = BASE_PROVS + [('TmplSrv32Base', BASE_DIR), ('TmplSrv32Rf', RF_DIR), ('TmplSrv32Ex', EX_DIR), ('TmplSrv32Cap', CAP_DIR), ('TmplSrv32Wire', WIRE_DIR)]


def nx(ver='a1'):
    import cpu_tmpl_srv32_nx as N
    text, ex_ = N.text('Srv32Nx')
    return gate('nx', 'TmplSrv32Nx', 'Srv32Nx', text, ex_, providers=_provs(*ALL_PROVS),
                extra=dict(generator='tools/cpu_tmpl_srv32_nx.py (one same-statement optimisation: proofs on D-form hypotheses, no drv rewriting inside the evaluated tree)'),
                prov='llm_written', ver=ver,
                note='next-value layer: one-cycle value of the pipeline registers (pc chain 239/240/241, ex_insn-side 250, ex_result copy 290, wb dst/m2r/branch/nop/trap 293..299, wb_memwr 292, '
                     'wb_alu2reg 289 in 6 flag scenarios) from wire/register facts; each theorem has a D-form helper nx_R_D')


def nx2(ver='a1'):
    import cpu_tmpl_srv32_nx2 as N
    text, ex_ = N.text('Srv32Nx2')
    return gate('nx2', 'TmplSrv32Nx2', 'Srv32Nx2', text, ex_, providers=_provs(*ALL_PROVS),
                extra=dict(generator='tools/cpu_tmpl_srv32_nx2.py (same D-form method as nx)'), prov='llm_written', ver=ver,
                note='next-value lemmas of the captured instruction fields: ex_insn (249), ex_src1/src2/dst_sel (252..254) as slices of the instruction word, imem_rdata (12) = rom word or 0 outside the image')


def cap3(ver='a1'):
    import cpu_tmpl_srv32_cap3 as C
    text, ex_ = C.text('Srv32Cap3')
    return gate('cap3', 'TmplSrv32Cap3', 'Srv32Cap3', text, ex_, providers=[provider(EDGE_DIR, 'TmplSrv32Edge'), provider(STAGE_DIR, 'TmplSrv32Stage')],
                extra=dict(generator='tools/cpu_tmpl_srv32_cap3.py (same xeval method as cap)'), prov='llm_written', classes=29, ver=ver,
                note='capture facts part 3: ex_system (269) and ex_system_op (270) are 0 after the rise for each of the 29 classes')


if __name__ == '__main__':
    globals()[sys.argv[1]](*sys.argv[2:])
