"""Check raw operand-route equations against actual combinational LFPs.

This discharges physical connections, not token age or ISA freshness. Preserve
unhandled branch processes and sequential captures as explicit residuals.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
import cpu_pending_origins as origin
import cpu_operand_routes as routes
import cpu_rf_read_ports as ports
from cpu_certificate_acceptance import run_stage


def requirement_plan(expression, width):
    """Guard-sensitive candidate R clauses, preserving casts and arithmetic."""
    if expression.name == 'ECond' and int(expression.args[0].name) == width:
        _, guard, yes, no = expression.args
        return dict(kind='guard', expression=ports.adapter.render(guard),
            zero=requirement_plan(no, width), nonzero=requirement_plan(yes, width))
    return dict(kind='value_equals_reference', width=width,
        expression=ports.adapter.render(expression),
        roots=sorted({int(n.args[1].name) for n in ports.adapter.walk(expression) if n.name=='EVar'}))


def requirement_source(program, outputs):
    lines=['Require Import Lang.ExtendedSVValueRequirements.',
           'Import ExtendedSVValueRequirements.']
    for n, row in enumerate(outputs):
        width, root = row['width'], row['output_root']
        lines += [f'Definition port_{n}_R s expected : Prop := requirements {width} port_{n}_rhs s expected.',
            f'Theorem port_{n}_R_exact seed fixed expected : CombLFP {program} seed fixed ->',
            f' (port_{n}_R fixed expected <-> norm {width}(read_signal fixed {root})=expected).',
            f'Proof. intro HL;unfold port_{n}_R;exact(actual_output_requirements {width} {root}',
            f' port_{n}_rhs fixed expected (port_{n}_lfp seed fixed HL)). Qed.']
    lines += ['Goal True. idtac "R_REQUIREMENTS_AUDIT". exact I. Qed.']
    lines += [f'Print Assumptions port_{n}_R_exact.' for n in range(len(outputs))]
    return '\n'.join(lines)+'\n'


def audit_requirements(log, count):
    chunks=log.split('\nR_REQUIREMENTS_AUDIT\n')
    return (len(chunks)==2 and ports.audit_output(chunks[0],count)
        and chunks[1].count('Closed under the global context')==count
        and 'Axioms:' not in chunks[1])


def analyze(ast):
    graph = routes.discover(ast)
    wanted = {(r['process'], r['root']) for r in graph['routes']}
    combs = [p for p in ast['processes'] if p['kind'] == 'Combinational']
    blocks, outputs, residuals = [], [], []
    for proc in ast['processes']:
        selected = sorted(root for name, root in wanted if name == proc['name'])
        if not selected:
            continue
        if proc['kind'] != 'Combinational':
            residuals.append(dict(process=proc['name'], roots=selected,
                reason='sequential sampling requires token-history preservation'))
            continue
        try:
            assignments = ports.flatten_blocking(proc['body'])
        except ValueError as exc:
            residuals.append(dict(process=proc['name'], roots=selected, reason=str(exc)))
            continue
        block_index = len(blocks)
        blocks.append(dict(process=proc['name'], comb_index=combs.index(proc),
                           assignments=assignments))
        for index, st in enumerate(assignments):
            _, rhs, lhs = st.args
            root = int(lhs.args[1].name)
            if root in selected:
                outputs.append(dict(block_index=block_index, assignment_index=index,
                    process=proc['name'], width=int(lhs.args[0].name),
                    output_root=root, rhs=rhs))
    return dict(blocks=blocks, ports=outputs, residuals=residuals), graph


def check(ast_path, ast_module, output):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    ast, binding, paths = origin.raw_binding(ast_path, ast_module)
    analysis, graph = analyze(ast)
    source = ports.render(binding['ast'], ast, analysis, opaque_single=True)
    source += requirement_source(binding['ast']['program'], analysis['ports'])
    (output/'requirements.json').write_text(json.dumps([
        dict(process=row['process'], root=row['output_root'],
             requirement=requirement_plan(row['rhs'], row['width']))
        for row in analysis['ports']], indent=2)+'\n')
    path = output/'OperandRoutes.v'
    path.write_text(source)
    report = dict(accepted=False, all_routes_proved=False, old_inv_read=False,
        operand_freshness_proved=False, complete_R_generated=False,
        candidate_value_relations_generated=True, candidate_relations_established=False,
        ast_sha256=ast['source_sha256'], source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        equation_count=len(analysis['ports']), residuals=analysis['residuals'],
        outputs=[{k:v for k,v in p.items() if k != 'rhs'} for p in analysis['ports']])
    (output/'routes.json').write_text(json.dumps(graph, indent=2)+'\n')
    flags = list(origin.pending.rtl.framework.FLAGS)
    for row in paths:
        flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(output.resolve()), 'GeneratedOperandRoutes']
    start = time.monotonic()
    deadline = start+1200
    c, timed = run_stage([str(origin.ROOT/'_opam/bin/coqc'), '-time', *flags, str(path.resolve())],
                        output/'coqc.log', deadline-time.monotonic())
    report.update(coqc_exit=c.returncode, coqc_timed_out=timed)
    if c.returncode == 0 and time.monotonic() < deadline:
        report['assumptions_closed'] = audit_requirements(c.stdout,len(analysis['ports']))
        k, timed = run_stage([str(origin.ROOT/'_opam/bin/coqchk'), '-silent', *flags,
            '-norec', 'GeneratedOperandRoutes.OperandRoutes'], output/'coqchk.log',
            deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode, coqchk_timed_out=timed,
            accepted=k.returncode == 0 and report['assumptions_closed'])
        report['all_routes_proved'] = report['accepted'] and not analysis['residuals']
    report['seconds'] = time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


def review_existing(ast_path, ast_module, provider, output):
    """Recheck an unchanged generated artifact after an audit-only repair.

    Never upgrades failed compilation; preserves the original report verbatim.
    """
    provider,output=Path(provider),Path(output)
    ast,binding,paths=origin.raw_binding(ast_path,ast_module)
    analysis,_=analyze(ast)
    source=ports.render(binding['ast'],ast,analysis,opaque_single=True)
    source+=requirement_source(binding['ast']['program'],analysis['ports'])
    previous=json.loads((provider/'report.json').read_text())
    digest=hashlib.sha256(source.encode()).hexdigest()
    if not(previous.get('coqc_exit')==0 and previous.get('coqchk_exit')==0
        and previous.get('source_sha256')==digest
        and (provider/'OperandRoutes.v').read_text()==source
        and (provider/'OperandRoutes.vo').is_file()):
        raise ValueError('unchanged successfully compiled raw-generated provider required')
    output.mkdir(parents=True,exist_ok=False)
    flags=list(origin.pending.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(provider.resolve()),'GeneratedOperandRoutes']
    started=time.monotonic()
    k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,
        '-norec','GeneratedOperandRoutes.OperandRoutes'],output/'coqchk.log',1200)
    report=dict(previous,accepted=False,provider=str(provider.resolve()),
        audit_only_repair=True,previous_report_preserved=True,
        assumptions_closed=audit_requirements((provider/'coqc.log').read_text(),len(analysis['ports'])),
        coqchk_exit=k.returncode,coqchk_timed_out=t,review_seconds=time.monotonic()-started,
        object_sha256=hashlib.sha256((provider/'OperandRoutes.vo').read_bytes()).hexdigest())
    report['accepted']=report['assumptions_closed'] and k.returncode==0
    report['all_routes_proved']=report['accepted'] and not analysis['residuals']
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    for name in ['ast', 'ast-module', 'output']:
        p.add_argument('--'+name, required=True)
    p.add_argument('--review-existing',help='Recheck unchanged successful native outputs after an audit-only repair')
    a = p.parse_args()
    result = (review_existing(a.ast,a.ast_module,a.review_existing,a.output)
        if a.review_existing else check(a.ast, a.ast_module, a.output))
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['accepted'] else 1)
