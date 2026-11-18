"""Discover operand storage boundaries and check original phase expressions.

Selection comes from raw RF payload reachability, not an old CPU invariant.
This proves stored-value updates, not the ISA ownership of sampled inputs.
"""
import argparse
import json
import time
from pathlib import Path
import cpu_pending_origins as origin
import cpu_operand_routes as routes
import cpu_operand_phase_requirements as phase_requirements
import cpu_effect_requirements as effect_requirements
from cpu_certificate_acceptance import run_stage


def mixed_analysis(ast, roots):
    rtl = origin.pending.rtl
    base = rtl.analyze(ast)
    unsupported = sorted(set(roots)-set(base['roots']))
    names = {p['name'] for p in ast['processes'] if set(roots) & set(p['writers'])}
    plans = [(p, plan) for p, plan in base['plans'] if p['name'] in names]
    effects = [(p, plan) for p, plan in base['effects'] if p['name'] in names]
    covered = {p['name'] for p, _ in plans+effects}
    missing = sorted(names-covered)
    return dict(plans=plans, effects=effects, roots=roots,
        plan_roots=sorted(set(roots)&set(base['plan_roots'])), residual=[]), unsupported, missing


def mixed_check(ast, profile, roots, output):
    """Use full state-threaded processes when a scalar NBA expression is invalid."""
    output.mkdir(parents=True, exist_ok=False)
    rtl = origin.pending.rtl
    analysis, unsupported, missing = mixed_analysis(ast, roots)
    plans, effects = analysis['plans'], analysis['effects']
    report = dict(accepted=False, roots=roots, unsupported_roots=unsupported,
                  unsupported_processes=missing, mode='complete_state_threaded_effects',
                  operand_freshness_proved=False, complete_R_generated=False,
                  reference_binding_proved=False, old_inv_read=False)
    if not unsupported and not missing:
        binding = profile['ast']
        source = rtl.render_adapter(binding['module'], binding['program'], ast, analysis)
        count = 3*len(plans)+2*len(effects)+len(roots)+len(analysis['plan_roots'])
        source, count, relations, nodes = effect_requirements.extend(
            ast, binding, analysis, source, count)
        report.update(relations=relations, transformer_nodes=nodes)
        path = output/'CaptureEffects.v'
        path.write_text(source)
        flags = list(rtl.framework.FLAGS)
        for row in profile['coq_load_paths']:
            flags += ['-R', row['directory'], row['namespace']]
        flags += ['-R', str(output.resolve()), 'GeneratedCaptureEffects']
        start = time.monotonic()
        deadline = start+1200
        c, timed = run_stage([str(origin.ROOT/'_opam/bin/coqc'), '-time', *flags, str(path.resolve())],
                            output/'coqc.log', deadline-time.monotonic())
        report.update(coqc_exit=c.returncode, coqc_timed_out=timed, audited_exports=count)
        if c.returncode == 0 and time.monotonic() < deadline:
            report['assumptions_closed'] = origin.captures.audit_output(c.stdout, count)
            k, timed = run_stage([str(origin.ROOT/'_opam/bin/coqchk'), '-silent', *flags,
                '-norec', 'GeneratedCaptureEffects.CaptureEffects'], output/'coqchk.log',
                deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode, coqchk_timed_out=timed,
                accepted=k.returncode == 0 and report['assumptions_closed'])
        report['seconds'] = time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


def check(ast_path, ast_module, output):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    ast, profile, paths = origin.raw_binding(ast_path, ast_module)
    profile['coq_load_paths'] = paths
    graph = routes.discover(ast)
    roots = sorted({r['root'] for r in graph['routes'] if r['crossed_sampling_boundary']})
    report = dict(accepted=False, roots=roots, old_inv_read=False,
        complete_R_generated=False, operand_freshness_proved=False,
        scope='actual phase expressions for discovered operand-copy storage; not all data registers')
    if roots:
        result = phase_requirements.check_profile(profile, output/'phases', roots, timeout=1200)
        report['phase_equations'] = result
        report['accepted'] = result['accepted']
        if result.get('status') == 'unsupported_scalar_expression_selection':
            report['mixed_phase_equations'] = mixed_check(ast, profile, roots, output/'mixed')
            report['accepted'] = report['mixed_phase_equations']['accepted']
        expressions = {row['root']: row for row in result.get('outputs', [])}
        report['pending_obligations'] = []
        for root in roots:
            row = dict(root=root, obligations=['instruction token at sampling edge',
                'sampled source equals that token reference value',
                'validity and token preserved under hold/reset/flush'])
            if root in expressions:
                row['sampled_inputs'] = expressions[root]['sampled_inputs']
            else:
                # A blocking temporary read is NOT necessarily an old-state read.
                row['process_read_roots_conservative'] = sorted({
                    int(n.args[1].name) for p in ast['processes'] if root in p['writers']
                    for n in origin.pending.rtl.walk(p['body']) if n.name == 'EVar'})
                row['input_semantics'] = 'state-threaded; temporary reads may observe earlier blocking writes'
            report['pending_obligations'].append(row)
    else:
        report['status'] = 'no_copy_storage_discovered_not_a_completeness_claim'
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    for name in ['ast', 'ast-module', 'output']:
        p.add_argument('--'+name, required=True)
    a = p.parse_args()
    result = check(a.ast, a.ast_module, a.output)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['accepted'] else 1)
