"""Discover and check full case selections on raw RF-to-operand paths.

No process IDs, role profile, or old CPU invariant is an input. These proofs
establish actual selection expressions, not their correspondence to token age.
"""
import argparse
import json
from pathlib import Path
import cpu_operand_route_proofs as routes
import cpu_blocking_case_binding as cases


def discover(ast):
    analysis, _ = routes.analyze(ast)
    processes = {p['name']: p for p in ast['processes']}
    selected, residuals = [], []
    for row in analysis['residuals']:
        proc = processes[row['process']]
        plan = cases.case_plan(proc)
        if plan is None or plan[1] not in row['roots']:
            residuals.append(row)
            continue
        selected.append(dict(process=proc['name'], width=plan[0], root=plan[1],
            expression=cases.rtl.render(plan[2])))
        remaining = [r for r in row['roots'] if r != plan[1]]
        if remaining:
            residuals.append(dict(row, roots=remaining))
    return dict(ast_sha256=ast['source_sha256'], selected=selected,
        residuals=residuals, old_inv_read=False, operand_freshness_proved=False)


def check(ast_path, ast_module, output):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    ast, _, _ = routes.origin.raw_binding(ast_path, ast_module)
    plan = discover(ast)
    (output/'plan.json').write_text(json.dumps(plan, indent=2)+'\n')
    results = []
    for row in plan['selected']:
        result = cases.check(ast_path, ast_module, row['process'], output/row['process'], structural=True)
        results.append(result)
    report = dict(accepted=bool(results) and all(r['accepted'] for r in results),
        status='checked' if results else 'no_supported_branch', results=results,
        residuals=plan['residuals'], old_inv_read=False,
        operand_freshness_proved=False, complete_R_generated=False)
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['ast', 'ast-module', 'output']:
        parser.add_argument('--'+name, required=True)
    args = parser.parse_args()
    result = check(args.ast, args.ast_module, args.output)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['accepted'] or result['status']=='no_supported_branch' else 1)
