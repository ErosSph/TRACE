"""Propose and kernel-check scalar RHS phase equations from imported AST.

Conservative initial subset: one actual sequential writer, a complete sequence
of NBA assignments, and exactly one whole-root assignment. Control-flow writers
are explicit residuals. This is a capture equation, not token freshness.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_auto_adapter as adapter
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage


def sequence_assignments(stmt):
    if stmt.name == 'SSkip':
        return []
    if stmt.name == 'SAssign' and stmt.args[0].name == 'true':
        return [stmt]
    if stmt.name == 'SSeq':
        return [a for child in stmt.args[0].args for a in sequence_assignments(child)]
    raise ValueError('writer has control flow or blocking assignment; sequence-only RHS subset')


def analyze(ast, roots=None):
    candidates = scalar.analyze(ast, roots)
    residuals = list(candidates['residuals'])
    supported = []
    for root in candidates['analysis']['roots']:
        writers = [p for p in ast['processes'] if p['kind'] == 'Sequential'
            and root in p['writers']]
        try:
            if len(writers) != 1:
                raise ValueError('RHS subset requires exactly one complete actual sequential writer')
            proc = writers[0]
            assignments = sequence_assignments(proc['body'])
            hits = [a for a in assignments if adapter.root_of(a.args[2]) == root]
            if len(hits) != 1 or hits[0].args[2].name != 'LVar':
                raise ValueError('RHS subset requires exactly one whole-root assignment')
            assignment = hits[0]
            supported.append(dict(root=root, width=int(assignment.args[2].args[0].name),
                rhs=assignment.args[1], process=proc['name']))
        except ValueError as exc:
            residuals.append(dict(root=root, reason=str(exc)))
    accepted_roots = [s['root'] for s in supported]
    narrowed = scalar.analyze(ast, accepted_roots)['analysis'] if accepted_roots else dict(
        plans=[], effects=[], residual=[], roots=[], plan_roots=[])
    return dict(supported=supported, residuals=residuals,
        requested_roots=candidates['requested_roots'], analysis=narrowed)


def render_rhs(binding, ast, found, base_module=None):
    if base_module is not None and not adapter.SYMBOL.fullmatch(base_module):
        raise ValueError('invalid base module symbol')
    if base_module:
        imports = [binding['module'], *binding.get('program_imports', []), base_module]
        if not all(adapter.SYMBOL.fullmatch(s) for s in [binding['program'], *imports]):
            raise ValueError('invalid AST module/program symbol')
        source = ('(** Generated RHS equations over an explicitly supplied, source-checked base module. *)\n'
            'From Coq Require Import List ZArith Arith.\n'
            'Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection\n'
            ' Lang.ExtendedSVAutoAdapterPlan Lang.ExtendedSVAutoAdapterPhase\n '
            + ' '.join(imports) + '.\n'
            'Import ListNotations ExtendedSV ExtendedSVRootProjection\n'
            ' ExtendedSVAutoAdapterPlan ExtendedSVAutoAdapterPhase ' + ast['module'] + '.\n')
    else:
        source = adapter.render_adapter(binding['module'], binding['program'], ast,
            found['analysis'], binding.get('program_imports', []))
    program, mod = binding['program'], ast['module']
    lines = ['Require Import Lang.ExtendedSVAssignment Lang.ExtendedSVWordInvariant.',
        'Import ExtendedSVAssignment ExtendedSVWordInvariant.',
        'Local Opaque norm read_signal eval_expr.']
    n = 0 if base_module else 3*len(found['analysis']['plans']) + 2*len(found['analysis']['roots'])
    qualifier = base_module.rsplit('.', 1)[-1] + '.' if base_module else ''
    for item in found['supported']:
        root, width, proc = item['root'], item['width'], item['process']
        prefix = f'root_{root}'
        lines += [f'Definition {prefix}_rhs : Expr := {adapter.render(item["rhs"])}.',
            f'Lemma {prefix}_rhs_phase ev pre : changed_signal ev <> {root}%nat ->',
            f' norm {width} (read_signal (PhaseSemantics {program} ev pre) {root}%nat) =',
            f' if process_matches_states pre (phase_driven_state {program} ev pre) {mod}.{proc}',
            f' then norm {width} (eval_expr (phase_driven_state {program} ev pre) {prefix}_rhs)',
            f' else norm {width} (read_signal pre {root}%nat).',
            'Proof.',
            f' intro HE. rewrite ({qualifier}{prefix}_compiled_phase ev pre HE).',
            f' cbn [plan_transition_updates {qualifier}{prefix}_plan_entries fst snd flat_map].',
            f' destruct (process_matches_states pre (phase_driven_state {program} ev pre) {mod}.{proc});',
            f' cbn [{qualifier}{proc}_plan eval_plan flat_map app apply_updates_root_value',
            ' apply_update_root_value resolve_update resolve_lvalue',
            ' update_signal update_offset update_width update_value]; [|reflexivity].',
            ' unfold apply_update_root_value.',
            ' cbn [update_signal update_offset update_width update_value Nat.eqb].',
            ' rewrite norm_full_low_write, norm_idempotent. reflexivity.',
            'Qed.',
            f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{n}". exact I. Qed.',
            f'Print Assumptions {prefix}_rhs_phase.']
        n += 1
    return source + '\n'.join(lines) + '\n'


def base_provenance(profile, roots, base_module=None, base_source=None):
    if base_module is None:
        if base_source is not None:
            raise ValueError('base source requires base module')
        return None
    if not adapter.SYMBOL.fullmatch(base_module):
        raise ValueError('invalid base module symbol')
    path = Path(base_source) if base_source else adapter.ROOT/'src'/Path(*base_module.split('.')).with_suffix('.v')
    _, found, expected = scalar.proposal(profile, roots)
    if found['residuals'] or not found['analysis']['roots']:
        raise ValueError('unsupported scalar base selection')
    if not path.is_file() or path.read_text() != expected:
        raise ValueError('base source is not the exact current scalar-capture generation')
    return dict(module=base_module, source=str(path),
        source_sha256=hashlib.sha256(expected.encode()).hexdigest(),
        source_matches_scalar_generator=True,
        boundary='exact source regeneration; Coq checks imported certificate proof objects, base library is not rebuilt here')


def proposal(profile, roots=None, base_module=None, base_source=None):
    binding = profile['ast']
    ast = adapter.load_ast(adapter.ROOT / binding['file'])
    found = analyze(ast, roots)
    found['base'] = base_provenance(profile, roots, base_module, base_source)
    return ast, found, render_rhs(binding, ast, found, base_module)


def emit_library(profile, destination, roots=None, check=False, base_module=None, base_source=None):
    _, found, source = proposal(profile, roots, base_module, base_source)
    if found['residuals'] or not found['supported']:
        raise ValueError('unsupported RHS roots: ' + json.dumps(found['residuals']))
    destination = Path(destination)
    if check:
        if not destination.is_file() or destination.read_text() != source:
            raise ValueError('persistent RHS source differs from current generation')
    elif destination.exists():
        raise ValueError('destination exists; use --check-source')
    else:
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(source)
    return dict(source=str(destination), roots=[s['root'] for s in found['supported']],
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        source_matches_generator=True, base=found.get('base'), coq_checked=False)


def check_profile(profile, output, roots=None, timeout=1200, base_module=None, base_source=None):
    output = Path(output)
    if output.exists():
        raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    ast, found, source = proposal(profile, roots, base_module, base_source)
    path = output/'ScalarRHS.v'
    path.write_text(source)
    count = len(found['supported']) if base_module else 3*len(found['analysis']['plans']) + 3*len(found['supported'])
    report = dict(ast_sha256=ast['source_sha256'], actual_program=profile['ast']['program'],
        generated_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        requested_roots=found['requested_roots'], residuals=found['residuals'],
        supported=[dict(root=s['root'], width=s['width'], process=s['process'],
            rhs=adapter.render(s['rhs']), export=f'root_{s["root"]}_rhs_phase')
            for s in found['supported']],
        audited_exports=count, base=found.get('base'), accepted=False, llm_calls=0,
        global_identity_invariant_synthesized=False, token_freshness_proved=False)
    if found['residuals'] or not found['supported']:
        report['status'] = 'unsupported_rhs_selection'
    else:
        flags = list(adapter.framework.FLAGS)
        for extra in profile.get('coq_load_paths', []):
            flags += ['-R', extra['directory'], extra['namespace']]
        flags += ['-R', str(output.resolve()), 'GeneratedScalarRHS']
        start = time.monotonic()
        compiled, timed = run_stage([str(adapter.ROOT/'_opam/bin/coqc'), '-q', *flags,
            str(path.resolve())], output/'coqc.log', timeout)
        report.update(coqc_exit=compiled.returncode, coqc_timed_out=timed,
            coqc_seconds=time.monotonic()-start)
        if compiled.returncode == 0:
            report['assumptions_closed'] = scalar.audit_output(compiled.stdout, count)
            start = time.monotonic()
            kernel, timed = run_stage([str(adapter.ROOT/'_opam/bin/coqchk'), '-silent',
                *flags, '-norec', 'GeneratedScalarRHS.ScalarRHS'], output/'coqchk.log', timeout)
            report.update(coqchk_exit=kernel.returncode, coqchk_timed_out=timed,
                coqchk_seconds=time.monotonic()-start)
            report['accepted'] = report['assumptions_closed'] and kernel.returncode == 0
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', type=Path, required=True)
    parser.add_argument('--roots', nargs='+', type=int)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument('--output', type=Path)
    target.add_argument('--emit-source', type=Path)
    parser.add_argument('--check-source', action='store_true')
    parser.add_argument('--base-module')
    parser.add_argument('--base-source', type=Path)
    parser.add_argument('--timeout', type=float, default=1200)
    args = parser.parse_args()
    if not 0 < args.timeout <= 1200:
        parser.error('timeout must be positive and at most1200 seconds')
    profile = json.loads(args.profile.read_text())
    if args.emit_source:
        report = emit_library(profile, args.emit_source, args.roots, args.check_source,
            args.base_module, args.base_source)
    else:
        if args.check_source:
            parser.error('--check-source requires --emit-source')
        report = check_profile(profile, args.output, args.roots, args.timeout,
            args.base_module, args.base_source)
    print(json.dumps(report, indent=2))
    return 0 if args.emit_source or report['accepted'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
