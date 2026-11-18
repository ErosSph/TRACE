"""Generate checked scalar-state capture/hold projections from the actual AST.

Reuses the existing NBA compiler and exact ordered writer certificates. This
constructs local transition equations, not token freshness or an ISA invariant.
No architectural roles, CPU names, signal IDs or writer IDs are built in.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_auto_adapter as adapter
from cpu_certificate_acceptance import run_stage


def analyze(ast, roots=None):
    base = adapter.analyze(ast)
    scalar, excluded = [], []
    for root in base['roots']:
        assignments = [node for proc in ast['processes']
            for node in adapter.walk(proc['body']) if node.name == 'SAssign'
            and adapter.root_of(node.args[2]) == root]
        widths = {int(node.args[2].args[0].name) for node in assignments
            if node.args[2].name == 'LVar'}
        if (assignments and all(node.args[2].name == 'LVar' for node in assignments)
                and len(widths) == 1 and min(widths) > 0):
            scalar.append(root)
        else:
            excluded.append({'root': root, 'reason': 'not a consistent whole scalar root'})
    if roots is not None:
        if (not roots or any(type(r) is not int or r < 0 for r in roots)
                or len(set(roots)) != len(roots)):
            raise ValueError('roots must be distinct nonnegative integers, not empty')
        selected = sorted(roots)
    else:
        selected = scalar
    residuals = []
    supported = []
    for root in selected:
        if root not in scalar:
            residuals.append({'root': root, 'reason': 'not a pure-state whole scalar root'})
        elif root not in base['plan_roots']:
            residuals.append({'root': root, 'reason': 'a complete actual writer is not NBA-compilable'})
        else:
            supported.append(root)
    names = {p['name'] for p in ast['processes'] if p['kind'] == 'Sequential'
        and any(root in p['writers'] for root in supported)}
    # Keep COMPLETE writer bodies and their original Program order. Root selection
    # must never prune updates inside a process, or choose a preferred writer.
    narrowed = dict(plans=[(p, plan) for p, plan in base['plans'] if p['name'] in names],
        effects=[], residual=[], roots=supported, plan_roots=supported)
    return dict(analysis=narrowed, requested_roots=selected,
        scalar_candidates=scalar, excluded=excluded, residuals=residuals)


def proposal(profile, roots=None):
    binding = profile['ast']
    ast = adapter.load_ast(adapter.ROOT / binding['file'])
    found = analyze(ast, roots)
    source = adapter.render_adapter(binding['module'], binding['program'], ast,
        found['analysis'], binding.get('program_imports', []))
    return ast, found, source


def audit_output(log, count):
    markers = list(re.finditer(r'^AUTO_ADAPTER_ASSUMPTIONS_([0-9]+)\s*$', log, re.M))
    if count <= 0 or [int(m.group(1)) for m in markers] != list(range(count)):
        return False
    for i, marker in enumerate(markers):
        stop = markers[i+1].start() if i+1 < len(markers) else len(log)
        chunk = log[marker.end():stop]
        if chunk.count('Closed under the global context') != 1 or 'Axioms:' in chunk:
            return False
    return True


def emit_library(profile, destination, roots=None, check=False):
    _, found, source = proposal(profile, roots)
    if found['residuals'] or not found['analysis']['roots']:
        raise ValueError('unsupported scalar roots: ' + json.dumps(found['residuals']))
    destination = Path(destination)
    if check:
        if not destination.is_file() or destination.read_text() != source:
            raise ValueError('persistent scalar source differs from current generation')
    elif destination.exists():
        raise ValueError('destination exists; use --check-source')
    else:
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(source)
    return dict(source=str(destination), roots=found['analysis']['roots'],
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        source_matches_generator=True, coq_checked=False)


def check_profile(profile, output, roots=None, timeout=1200):
    output = Path(output)
    if output.exists():
        raise ValueError('output must be fresh; preserve previous evidence')
    output.mkdir(parents=True)
    ast, found, source = proposal(profile, roots)
    path = output / 'ScalarCaptures.v'
    path.write_text(source)
    analysis = found['analysis']
    count = 3*len(analysis['plans']) + 2*len(analysis['roots'])
    report = dict(schema_version=1, ast_sha256=ast['source_sha256'],
        actual_program=profile['ast']['program'], requested_roots=found['requested_roots'],
        generated_roots=analysis['roots'], scalar_candidates=found['scalar_candidates'],
        excluded=found['excluded'], residuals=found['residuals'],
        generated_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        writers=[p['name'] for p, _ in analysis['plans']], accepted=False,
        audited_exports=count,
        llm_calls=0, global_invariant_synthesized=False, token_freshness_proved=False)
    if found['residuals'] or not analysis['roots']:
        report['status'] = 'unsupported_scalar_selection'
    else:
        flags = list(adapter.framework.FLAGS)
        for extra in profile.get('coq_load_paths', []):
            flags += ['-R', extra['directory'], extra['namespace']]
        flags += ['-R', str(output.resolve()), 'GeneratedScalar']
        start = time.monotonic()
        compiled, timed = run_stage([str(adapter.ROOT/'_opam/bin/coqc'), '-q', *flags,
            str(path.resolve())], output/'coqc.log', timeout)
        report.update(coqc_exit=compiled.returncode, coqc_timed_out=timed,
            coqc_seconds=time.monotonic()-start)
        if compiled.returncode == 0:
            report['assumptions_closed'] = audit_output(compiled.stdout, count)
            start = time.monotonic()
            checked, timed = run_stage([str(adapter.ROOT/'_opam/bin/coqchk'), '-silent',
                *flags, '-norec', 'GeneratedScalar.ScalarCaptures'], output/'coqchk.log', timeout)
            report.update(coqchk_exit=checked.returncode, coqchk_timed_out=timed,
                coqchk_seconds=time.monotonic()-start)
            report['accepted'] = report['assumptions_closed'] and checked.returncode == 0
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', type=Path, required=True)
    parser.add_argument('--roots', type=int, nargs='+')
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument('--output', type=Path)
    target.add_argument('--emit-source', type=Path)
    parser.add_argument('--check-source', action='store_true')
    parser.add_argument('--timeout', type=float, default=1200)
    args = parser.parse_args()
    if not 0 < args.timeout <= 1200:
        parser.error('timeout must be positive and at most1200 seconds')
    profile = json.loads(args.profile.read_text())
    if args.emit_source:
        report = emit_library(profile, args.emit_source, args.roots, args.check_source)
    else:
        if args.check_source:
            parser.error('--check-source requires --emit-source')
        report = check_profile(profile, args.output, args.roots, args.timeout)
    print(json.dumps(report, indent=2))
    return 0 if args.emit_source or report['accepted'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
