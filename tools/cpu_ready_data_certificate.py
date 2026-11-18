"""Consume CDFG selector/mux queries and certify actual ready-data equations.

No program age is inferred from branch priority. RF and producer-effect
correspondence are explicit remaining R obligations in the ISA connection.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_two_stage_selector as selectors
import cpu_selected_data_paths as data
from cpu_add_control_certificate import verified
from cpu_cdfg_result_consumer import checked_graph
from cpu_pyslang_cdfg import dependencies, backward_slice
from cpu_certificate_acceptance import run_stage, parse_assumptions, ALLOWED_AXIOMS

rtl = selectors.rtl


def discover(raw):
    rows = []
    for s in selectors.selectors.discover(raw)['selected']:
        try:
            binding = selectors.match(rtl.Parser(s['expression']).complete())
        except ValueError:
            continue
        paths = data.discover(raw, [dict(selector=s, code=c) for c in range(4)])
        if len({p['output'] for p in paths}) != 1:
            raise ValueError('selector codes do not share one data output')
        rows.append(dict(selector=s, binding=binding, paths=paths))
    if not rows:
        raise ValueError('no complete ready selector/data path')
    return rows


def check_graph(graph, raw, rows):
    """Cross-check every consumed local expression, without executing a slice."""
    if graph['obligations']:
        raise ValueError('unresolved graph obligations')
    symbols = {s['path']: s for s in graph['symbols']}
    by_root = {s['coq_root']: s for s in graph['symbols']}
    processes = {p['id']: p for p in graph['processes']}
    checks = {}
    for row in rows:
        s = row['selector']
        checks[s['root']] = (s['width'], rtl.Parser(s['expression']).complete())
        for path in row['paths']:
            proc = next(p for p in raw['processes'] if p['name'] == path['process'])
            w, root, expr = data.cases.case_plan(proc)
            checks[root] = (w, expr)
            for route in [path['control'], path['data']]:
                for edge in route['edges']:
                    proc = next(p for p in raw['processes'] if p['name'] == edge['process'])
                    st = data.cases.unwrap(proc['body'])
                    if st.name != 'SAssign' or st.args[0].name != 'false':
                        raise ValueError('consumed wire is not a blocking assignment')
                    checks[edge['root']] = (edge['width'], st.args[1])
    for root, (width, expr) in checks.items():
        symbol = by_root[root]
        edges = [e for e in graph['edges'] if e['target'] == symbol['path']]
        if not edges or len({e['process'] for e in edges}) != 1:
            raise ValueError(f'graph writer mismatch at root {root}')
        for edge in edges:
            if edge['assignment'] == 'port_connection':
                if (len(edges) != 1 or processes[edge['process']]['kind'] != 'port' or
                        edge['guards'] or edge['address'] or len(edge['data']) != 1 or
                        edge['reads_version'] != 'current' or edge['writes_version'] != 'current'):
                    raise ValueError(f'graph port connection mismatch at root {root}')
            elif edge['assignment'] == 'blocking':
                body = processes[edge['process']].get('body', {})
                if (edge['writes_version'] != 'procedural_current' or
                        body.get('timing', {}).get('kind') not in [None, 'ImplicitEventControl']):
                    raise ValueError(f'graph phase mismatch at root {root}')
            else:
                raise ValueError(f'graph assignment mismatch at root {root}')
        actual = sorted((symbols[p]['width'], symbols[p]['coq_root'])
                        for p in set().union(*(dependencies(e) for e in edges)))
        expected = sorted({tuple(int(a.name) for a in n.args)
                           for n in rtl.walk(expr) if n.name == 'EVar'})
        if symbol['width'] != width or actual != expected:
            raise ValueError('graph/Coq mux dependency or width mismatch')
    return dict(checked_roots=sorted(checks), queries=[
        backward_slice(graph, by_root[r['paths'][0]['output']]['path']) for r in rows])


def render(ast, module, profile, rows):
    p = profile['ast']['program']
    flat = [dict(selector=r['selector'], code=c) for r in rows for c in range(4)]
    text, paths = data.render(ast, module, flat)
    source = 'Module D.\n' + text + '\nEnd D.\n'
    source += f'''From Coq Require Import ZArith List.
Require Import {module} Lang.ExtendedSV Ex.External.CPUTwoStageReadySelection
 Ex.External.CPUReadyOperand Ex.External.CPUISAReadyBatches Ex.External.CPUISAOwnedEffects
 Ex.External.CPURegisterEffectRelation Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 GeneratedReadySelector.ReadySelector.
Import ExtendedSV CPUTwoStageReadySelection CPUReadyOperand CPUISAReadyBatches CPUISAOwnedEffects CPURegisterEffectRelation.
Module S:=GeneratedReadySelector.ReadySelector.
Local Opaque {p}.
'''
    for i, row in enumerate(rows):
        sr = row['selector']['root']
        first, second = row['binding']['first'], row['binding']['second']
        by_code = {r['code']: r for r in paths if r['control']['terminal'] == sr}
        output = by_code[0]['output']
        rf, young, old, load = [by_code[c]['data']['terminal'] for c in [0, 1, 2, 3]]
        address = f"(norm 5(read_signal fixed {first['rs']}%nat))"
        args = (f"(S.bit fixed {second['write']}%nat)(norm 5(read_signal fixed {second['rd']}%nat))(S.bit fixed {second['load']}%nat)"
                f"(norm 32(read_signal fixed {old}%nat))(norm 32(read_signal fixed {load}%nat))"
                f"(S.bit fixed {first['write']}%nat)(norm 5(read_signal fixed {first['rd']}%nat))(S.bit fixed {first['load']}%nat)"
                f"(norm 32(read_signal fixed {young}%nat))")
        eligible_y = f"(eligible(S.bit fixed {first['write']}%nat)(norm 5(read_signal fixed {first['rd']}%nat)){address})"
        eligible_o = f"(eligible(S.bit fixed {second['write']}%nat)(norm 5(read_signal fixed {second['rd']}%nat)){address})"
        guard_y = f"({eligible_y} && negb(S.bit fixed {first['load']}))%bool"
        guard_o = f"({eligible_o} && negb(S.bit fixed {second['load']}))%bool"
        guard_l = f"({eligible_o} && S.bit fixed {second['load']})%bool"
        indices = {r['code']: paths.index(r) for r in by_code.values()}
        source += f'''Theorem actual_operand_{sr} seed fixed physical:CombLFP {p} seed fixed ->
 physical {address}=norm 32(read_signal fixed {rf}) ->
 norm 32(read_signal fixed {output})=operand physical {address} {args}.
Proof. intros HL HR;pose proof(S.selector_{sr}_normal_form seed fixed HL)as HC.
 unfold operand,selected_code in HC|-*.
 destruct {guard_y};[exact(D.data_{indices[1]}_lfp seed fixed HL HC)|].
 destruct {guard_o};[exact(D.data_{indices[2]}_lfp seed fixed HL HC)|].
 destruct {guard_l};[exact(D.data_{indices[3]}_lfp seed fixed HL HC)|].
 rewrite HR;exact(D.data_{indices[0]}_lfp seed fixed HL HC). Qed.

Theorem actual_ready_resolution_{sr} seed fixed physical:CombLFP {p} seed fixed ->
 physical {address}=norm 32(read_signal fixed {rf}) ->physical 0%Z=0%Z ->
 ({eligible_y} && S.bit fixed {first['load']})%bool=false ->
 resolve 0%Z physical {address}(slots {args})=Some(norm 32(read_signal fixed {output})).
Proof. intros HL HR HZ HA;rewrite(actual_operand_{sr} seed fixed physical HL HR).
 exact(admitted_selection physical {address} {args} HZ HA). Qed.

Section ISA_{sr}.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{Token:Type}}.
Theorem actual_operand_matches_original_read_{sr} (token_pc token_word:Token->Z)
 seed fixed physical initial batches before after value:
 CombLFP {p} seed fixed ->
 physical {address}=norm 32(read_signal fixed {rf}) ->
 CertifiedBatches token_pc token_word initial batches before ->RegisterRelated physical initial ->
 (0<={address}<32)%Z ->Machine.getRegister {address} before=(Some value,after) ->
 Forall2 SlotRelated(slots {args})(batch_writes 32 {address} batches) ->
 physical 0%Z=0%Z ->({eligible_y} && S.bit fixed {first['load']})%bool=false ->
 norm 32(read_signal fixed {output})=word.unsigned value.
Proof. intros HL HR HB HP HA HREAD HS HZ HREADY.
 exact(actual_ready_selector_matches_read token_pc token_word initial batches before after {address} value physical
 (slots {args}) _ HB HP HA HREAD HS(actual_ready_resolution_{sr} seed fixed physical HL HR HZ HREADY)). Qed.
End ISA_{sr}.
'''
    source += 'Goal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\n'
    for row in rows:
        sr = row['selector']['root']
        source += f'Print Assumptions actual_operand_{sr}.\nPrint Assumptions actual_ready_resolution_{sr}.\n'
    source += 'Goal True. idtac "REFINEMENT_ASSUMPTIONS". exact I. Qed.\n'
    for row in rows:
        source += f'Print Assumptions actual_operand_matches_original_read_{row["selector"]["root"]}.\n'
    return source


def check(a):
    verified(a.selectors, 'ReadySelector')
    raw, profile, paths = selectors.selectors.origin.raw_binding(a.ast, a.ast_module)
    provider_plan = json.loads((Path(a.selectors) / 'plan.json').read_text())
    if provider_plan['ast_sha256'] != raw['source_sha256']:
        raise ValueError('selector provider configuration differs')
    rows = discover(raw)
    if [(r['selector'], r['binding']) for r in rows] != [(r['selector'], r['binding']) for r in provider_plan['rows']]:
        raise ValueError('selector provider discovery differs')
    out = Path(a.output)
    out.mkdir(parents=True, exist_ok=False)
    try:
        graph = checked_graph(a.graph, a.ast, out / 'replayed')
        graph_queries = check_graph(graph, raw, rows)
    except ValueError as error:
        report = dict(accepted=False, stage='graph_admission', error=str(error), complete_R_generated=False)
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        return report
    source = render(a.ast, a.ast_module, profile, rows)
    file = out / 'ReadyData.v'
    file.write_text(source)
    (out / 'plan.json').write_text(json.dumps(dict(rows=rows, ast_sha256=raw['source_sha256'],
        graph_sha256=hashlib.sha256(Path(a.graph).read_bytes()).hexdigest()), indent=2) + '\n')
    (out / 'queries.json').write_text(json.dumps(graph_queries, indent=2) + '\n')
    flags = list(rtl.framework.FLAGS)
    for path in paths:
        flags += ['-R', path['directory'], path['namespace']]
    flags += ['-R', str(Path(a.selectors).resolve()), 'GeneratedReadySelector',
              '-R', str(out.resolve()), 'GeneratedReadyData']
    start = time.monotonic()
    baseline = out / 'Baseline.v'
    baseline.write_text('Require Import Ex.External.CPUTwoStageReadySelection.\n'
        'Goal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\n'
        'Print Assumptions CPUTwoStageReadySelection.selected_operand_matches_original_read.\n')
    bc, _ = run_stage([str(selectors.selectors.origin.ROOT / '_opam/bin/coqc'), *flags, str(baseline.resolve())],
                      out / 'baseline.log', 1200)
    report = dict(accepted=False, baseline_coqc_exit=bc.returncode, source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        ast_sha256=raw['source_sha256'], complete_R_generated=False, operand_freshness_proved=False,
        program_age_proved=False, llm_calls=0, old_inv_read=False,
        scope='actual CDFG-selected forwarding mux and conditional original-ISA operand correspondence')
    if bc.returncode == 0:
        base_axioms = parse_assumptions(bc.stdout)
        cc, timeout = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqc.resources').resolve()),
            str(selectors.selectors.origin.ROOT / '_opam/bin/coqc'), '-time', *flags, str(file.resolve())],
            out / 'coqc.log', max(.1, 1200 - (time.monotonic() - start)))
        report.update(coqc_exit=cc.returncode, coqc_timed_out=timeout, baseline_assumptions=sorted(base_axioms))
        if cc.returncode == 0 and time.monotonic() - start < 1200:
            local_audit = cc.stdout.split('ACCEPTANCE_ASSUMPTIONS')[-1].split('REFINEMENT_ASSUMPTIONS')[0]
            closed = local_audit.count('Closed under the global context') == 2 * len(rows) and 'Axioms:' not in local_audit
            isa_axioms = parse_assumptions(cc.stdout, 'REFINEMENT_ASSUMPTIONS')
            audit = closed and not (isa_axioms - base_axioms) and not (base_axioms - ALLOWED_AXIOMS)
            kk, timeout = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqchk.resources').resolve()),
                str(selectors.selectors.origin.ROOT / '_opam/bin/coqchk'), '-silent', *flags, '-norec', 'GeneratedReadyData.ReadyData'],
                out / 'coqchk.log', max(.1, 1200 - (time.monotonic() - start)))
            report.update(coqchk_exit=kk.returncode, coqchk_timed_out=timeout, local_assumptions_closed=closed,
                isa_assumptions=sorted(isa_axioms), assumptions_audit_passed=audit, accepted=audit and kk.returncode == 0)
    report['seconds'] = time.monotonic() - start
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    for key in ['ast', 'ast-module', 'graph', 'selectors', 'output']:
        p.add_argument('--' + key, required=True)
    a = p.parse_args()
    r = check(a)
    print(json.dumps(r, indent=2))
    raise SystemExit(0 if r['accepted'] else 1)
