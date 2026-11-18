"""Generate checked raw RF read sites from real process syntax paths.

No CPU names or architectural signal IDs occur in the matcher.  This proves
physical lane selection and conditional relation transport, NOT instruction
identity, forwarding freshness, a complete read-port output, or ISA refinement.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_auto_adapter as adapter
import cpu_bank_adapter as banks
from cpu_certificate_acceptance import run_stage


def children(kind, term):
    """The independently checked SyntaxNode child convention in BankRead.v."""
    a, name = term.args, term.name
    if kind == 'statement':
        if name == 'SSkip': return []
        if name == 'SAssign': return [('expression', a[1]), ('lvalue', a[2])]
        if name == 'SSeq': return [('statement', s) for s in a[0].args]
        if name == 'SIf': return [('expression', a[0]), ('statement', a[1]), ('statement', a[2])]
        if name == 'SCase': return [('expression', a[0]), *[('arm', s) for s in a[1].args]]
    elif kind == 'arm' and name == 'pair':
        key, body = a
        if key.name == 'None': return [('statement', body)]
        if key.name == 'Some': return [('expression', key.args[0]), ('statement', body)]
    elif kind == 'lvalue':
        if name == 'LVar': return []
        if name == 'LSel': return [('lvalue', a[1]), ('expression', a[2])]
    elif kind == 'expression':
        if name in ('EConst', 'EVar'): return []
        if name in ('ESel', 'EConcat'): return [('expression', a[1]), ('expression', a[2])]
        if name == 'EBinary': return [('expression', a[2]), ('expression', a[3])]
        if name in ('EReplicate', 'EExtend', 'EUnary'): return [('expression', a[2])]
        if name == 'ECond': return [('expression', s) for s in a[1:]]
    raise ValueError('unsupported syntax path node: ' + kind + '/' + name)


def walk_paths(kind, term, path=()):
    yield kind, term, path
    for index, (child_kind, child) in enumerate(children(kind, term)):
        yield from walk_paths(child_kind, child, (*path, index))


def analyze(ast):
    physical = banks.analyze(ast)
    roots = {b['root']: b['total'] for b in physical['banks']}
    sites, residuals = [], list(physical['residuals'])
    references = 0
    supported_bases = set()
    for process_index, proc in enumerate(ast['processes']):
        for kind, term, path in walk_paths('statement', proc['body']):
            if kind != 'expression': continue
            if term.name == 'EVar' and int(term.args[1].name) in roots:
                references += 1
                if (process_index, path) not in supported_bases:
                    residuals.append({'process': proc['name'], 'path': list(path),
                        'reason': 'bank reference not covered by a checked 32-bit lane read'})
            if term.name != 'ESel' or term.args[1].name != 'EVar': continue
            width, base, offset = term.args
            root = int(base.args[1].name)
            if root not in roots: continue
            if (width.name != '32' or int(base.args[0].name) != roots[root]
                    or not banks.bounded32(offset)):
                continue
            supported_bases.add((process_index, (*path, 0)))
            sites.append({'process': proc['name'], 'process_index': process_index,
                'path': list(path), 'root': root, 'total': roots[root], 'offset': offset})
    return {'sites': sites, 'residuals': residuals, 'bank_reference_count': references,
        'physical_bank_count': len(roots)}


def render(binding, ast, analysis):
    imports = [binding['module'], *binding.get('program_imports', [])]
    if not all(adapter.SYMBOL.fullmatch(s) for s in [binding['program'], *imports]):
        raise ValueError('invalid Coq program/import binding')
    mod, program = ast['module'], binding['program']
    lines = ['(** Generated checked read sites; not a complete CPU operand proof. *)',
        'From Coq Require Import List ZArith.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVBankAlignment Lang.ExtendedSVBankRead',
        ' Ex.External.CPURegisterReadRelation coqutil.Map.Interface coqutil.Word.Interface coqutil.Byte',
        ' ' + ' '.join(imports) + '.',
        'Import ListNotations ExtendedSV ExtendedSVBankAlignment ExtendedSVBankRead.']
    audits = []
    for n, site in enumerate(analysis['sites']):
        name = f'read_{n}'
        proc, root, total = f'{mod}.{site["process"]}', site['root'], site['total']
        path = '[' + '; '.join(str(i) + '%nat' for i in site['path']) + ']'
        lines += [f'Definition {name}_path : list nat := {path}.',
            f'Definition {name}_offset : Expr := {adapter.render(site["offset"])}.',
            f'Lemma {name}_registered : nth_error (processes {program}) {site["process_index"]}%nat = Some {proc}.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma {name}_source_checked : expression_at {proc} {name}_path =',
            f' Some (ESel 32 (EVar {total} {root}%nat) {name}_offset).',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma {name}_bounded : bounded32b {name}_offset = true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Definition {name}_physical := checked_bank_read {proc} {name}_path',
            f' {root}%nat {total}%nat {name}_offset {name}_source_checked',
            f' ltac:(lia) {name}_bounded.',
            f'Definition {name}_related := checked_bank_read_related {proc} {name}_path',
            f' {root}%nat {total}%nat {name}_offset {name}_source_checked',
            f' ltac:(lia) {name}_bounded.',
            f'Definition {name}_projected_nonzero := checked_bank_read_projected {proc} {name}_path',
            f' {root}%nat {total}%nat {name}_offset {name}_source_checked',
            f' ltac:(lia) {name}_bounded.']
        for suffix, theorem in [('isa_nonzero', 'actual_checked_read_nonzero'),
                                ('isa_with_zero_evidence', 'actual_checked_read_with_zero')]:
            lines += [f'Definition {name}_{suffix} {{word : Interface.word 32}}',
                ' {Registers : map.map Z word} {Mem : map.map word byte} :=',
                f' @CPURegisterReadRelation.{theorem} word Registers Mem',
                f' {proc} {name}_path {root}%nat {total}%nat {name}_offset',
                f' {name}_source_checked ltac:(lia) {name}_bounded.']
        audits.extend(name + s for s in ('_physical', '_related', '_projected_nonzero',
            '_isa_nonzero', '_isa_with_zero_evidence'))
    # Explicit import keeps the fixed proof tactic available, not LLM-supplied.
    lines[1] = 'From Coq Require Import List ZArith Lia.'
    for n, theorem in enumerate(audits):
        lines += [f'Goal True. idtac "BANK_READ_ASSUMPTIONS_{n}". exact I. Qed.',
            'Print Assumptions ' + theorem + '.']
    return '\n'.join(lines) + '\n'


def audit_output(source, count):
    markers = list(re.finditer(r'^BANK_READ_ASSUMPTIONS_([0-9]+)\s*$', source, re.M))
    if count <= 0 or [int(m.group(1)) for m in markers] != list(range(5*count)):
        return False
    for n, marker in enumerate(markers):
        stop = markers[n+1].start() if n+1 < len(markers) else len(source)
        chunk = source[marker.end():stop]
        if chunk.count('Closed under the global context') != 1 or 'Axioms:' in chunk:
            return False
    return True


def check_profile(profile, output, timeout=1200):
    if output.exists(): raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    binding = profile['ast']
    ast = adapter.load_ast(adapter.ROOT/binding['file'])
    analysis = analyze(ast)
    source = render(binding, ast, analysis)
    path = output/'AutoBankReads.v'
    path.write_text(source)
    report = {'schema_version': 1, 'ast_sha256': ast['source_sha256'],
        'generated_source_sha256': hashlib.sha256(source.encode()).hexdigest(),
        'actual_program': binding['program'], 'accepted': False, 'llm_calls': 0,
        'sites': [{k: v for k, v in site.items() if k != 'offset'} for site in analysis['sites']],
        'bank_reference_count': analysis['bank_reference_count'],
        'residuals': analysis['residuals'],
        'instruction_identity_proved': False, 'operand_freshness_proved': False,
        'conditional_original_isa_read_transport_generated': bool(analysis['sites']),
        'full_read_port_output_proved': False, 'global_invariant_synthesized': False,
        'scope': 'real syntax-bound raw lane reads; related-view transport is conditional'}
    if analysis['sites']:
        flags = list(adapter.framework.FLAGS)
        for extra in profile.get('coq_load_paths', []):
            flags += ['-R', extra['directory'], extra['namespace']]
        flags += ['-R', str(output.resolve()), 'GeneratedBankReads']
        started = time.monotonic()
        compiled, timed = run_stage([str(adapter.ROOT/'_opam/bin/coqc'), '-q', *flags,
            str(path.resolve())], output/'coqc.log', timeout)
        report.update(coqc_exit=compiled.returncode, coqc_timed_out=timed,
            coqc_seconds=time.monotonic()-started)
        if compiled.returncode == 0:
            audited = audit_output(compiled.stdout, len(analysis['sites']))
            started = time.monotonic()
            checked, timed = run_stage([str(adapter.ROOT/'_opam/bin/coqchk'), '-silent',
                *flags, '-norec', 'GeneratedBankReads.AutoBankReads'], output/'coqchk.log', timeout)
            report.update(assumptions_accepted=audited, coqchk_exit=checked.returncode,
                coqchk_timed_out=timed, coqchk_seconds=time.monotonic()-started)
            report['accepted'] = audited and checked.returncode == 0 and not analysis['residuals']
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=1200)
    args = parser.parse_args()
    result = check_profile(json.loads(args.profile.read_text()), args.output, args.timeout)
    print(json.dumps(result, indent=2))
    return 0 if result['accepted'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
