"""Generate checked physical register-bank components from imported RTL AST.

No CPU names, signal IDs, ISA mappings or hand-selected writer lists occur in
the matcher. Coq checks both compiler results and the complete ordered actual
writer set. This does not establish instruction identity or ISA write values.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_auto_adapter as adapter
import cpu_auto_roles as roles
from cpu_certificate_acceptance import run_stage, ALLOWED_AXIOMS


def literal(term):
    if term.name != 'EConst':
        return None
    width, value = (int(t.name) for t in term.args)
    if not 0 <= width <= 4096:
        raise ValueError('literal normalization width exceeds generation budget')
    return value % (1 << width)


def aligned32(term):
    """Propose exactly the structural checker in ExtendedSVBankAlignment."""
    if term.name == 'EConst':
        return literal(term) % 32 == 0
    width = int(term.args[0].name)
    if width < 5:
        return False
    if term.name == 'EBinary':
        _, op, a, b = term.args
        if op.name == 'BMul':
            return literal(a) == 32 or literal(b) == 32
        if op.name == 'BShiftL':
            count = literal(b)
            return count is not None and count >= 5
    if term.name == 'ESel':
        return literal(term.args[2]) == 0 and aligned32(term.args[1])
    if term.name == 'EExtend':
        return term.args[1].name == 'false' and aligned32(term.args[2])
    return False


def bounded32(term):
    if not aligned32(term):
        return False
    if int(term.args[0].name) <= 10:
        return True
    if term.name == 'EBinary' and term.args[1].name == 'BMul':
        a, b = term.args[2:]
        return ((literal(a) == 32 and int(b.args[0].name) <= 5)
            or (literal(b) == 32 and int(a.args[0].name) <= 5))
    return False


def bank_plan_of(plan, root, total):
    """Independent proposal; successful Coq compile_bank equality is mandatory."""
    T = adapter.Term
    if plan.name == 'NEmpty':
        return T('BPEmpty')
    if plan.name == 'NAssign':
        rhs, lhs = plan.args
        if adapter.root_of(lhs) != root:
            return T('BPEmpty')
        if lhs.name == 'LVar' and int(lhs.args[0].name) == total and total >= 1024:
            return T('BPReset', (rhs,))
        if lhs.name == 'LSel':
            width, base, offset = lhs.args
            if (width.name == '32' and base.name == 'LVar'
                    and int(base.args[0].name) == total and bounded32(offset)):
                return T('BPWord', (offset, rhs))
        raise ValueError('unsupported bank slice/layout; no proof or ISA mapping inferred')
    if plan.name == 'NSeq':
        return T('BPSeq', (T('list', tuple(bank_plan_of(p, root, total)
            for p in plan.args[0].args)),))
    if plan.name == 'NIf':
        guard, yes, no = plan.args
        return T('BPIf', (guard, bank_plan_of(yes, root, total),
            bank_plan_of(no, root, total)))
    raise ValueError('unsupported bank plan constructor: ' + plan.name)


def analyze(ast):
    banks, residuals = [], []
    for candidate in roles.derive_candidates(ast)['register_file']:
        root, total = candidate['root'], candidate['root_width']
        try:
            if total != 1024:
                raise ValueError('architectural lane-layout adapter required for non-32-lane bank')
            if any(root in p['writers'] for p in ast['processes'] if p['kind'] == 'Combinational'):
                raise ValueError('bank has combinational writers; phase-frame certificate unavailable')
            writers = [p for p in ast['processes']
                if p['kind'] == 'Sequential' and root in p['writers']]
            plans = []
            for proc in writers:
                nb = adapter.plan_of(proc['body'])
                plans.append((proc, nb, bank_plan_of(nb, root, total)))
            banks.append({'root': root, 'total': total, 'plans': plans})
        except ValueError as exc:
            residuals.append({'candidate': candidate['id'], 'root': root, 'reason': str(exc)})
    return {'banks': banks, 'residuals': residuals,
        'candidate_count': len(banks) + len(residuals)}


def render_bank_adapter(binding, ast, analysis):
    imports = [binding['module'], *binding.get('program_imports', [])]
    program, mod = binding['program'], ast['module']
    if not all(adapter.SYMBOL.fullmatch(s) for s in [program, *imports]):
        raise ValueError('invalid Coq import/program symbol')
    lines = ['(** Generated physical bank component, NOT an ISA correctness claim. *)',
        'From Coq Require Import List ZArith Arith.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection',
        ' Lang.ExtendedSVAutoAdapterPlan Lang.ExtendedSVAutoAdapterPhase',
        ' Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankAlignment Lang.ExtendedSVBankPlan',
        ' Ex.External.CPURegisterEffectRelation coqutil.Map.Interface coqutil.Word.Interface',
        ' coqutil.Word.Bitwidth coqutil.Byte',
        ' ' + ' '.join(imports) + '.',
        'Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVAutoAdapterPlan',
        f' ExtendedSVAutoAdapterPhase ExtendedSVRegisterBank ExtendedSVBankPlan {mod}.']
    audits = []
    for bank in analysis['banks']:
        root, total, plans = bank['root'], bank['total'], bank['plans']
        prefix = f'bank_{root}'
        for proc, nb, bp in plans:
            name = prefix + '_' + proc['name']
            lines += [f'Definition {name}_nb : NbPlan := {adapter.render(nb)}.',
                f'Definition {name}_plan : BankPlan := {adapter.render(bp)}.',
                f'Lemma {name}_nb_checked : compile_nb (statement_fuel {program})',
                f' (process_body {mod}.{proc["name"]}) = Some {name}_nb.',
                'Proof. vm_compute. reflexivity. Qed.',
                f'Lemma {name}_bank_checked : compile_bank (statement_fuel {program})',
                f' {root}%nat {total}%nat {name}_nb = Some {name}_plan.',
                'Proof. vm_compute. reflexivity. Qed.']
        nbs = '[' + '; '.join(f'({mod}.{p["name"]}, {prefix}_{p["name"]}_nb)'
            for p, _, _ in plans) + ']'
        entries = '[' + '; '.join(f'Build_BankEntry {mod}.{p["name"]} '
            f'{prefix}_{p["name"]}_nb {prefix}_{p["name"]}_plan' for p, _, _ in plans) + ']'
        lines += [f'Definition {prefix}_nb_entries : list (Process * NbPlan) := {nbs}.',
            f'Definition {prefix}_entries : list BankEntry := {entries}.',
            f'Lemma {prefix}_nb_certificate : PlanRootCertificate {program} {root}%nat {prefix}_nb_entries.',
            'Proof. constructor.',
            ' - apply Nat.ltb_lt. vm_compute. reflexivity.',
            ' - vm_compute. reflexivity.',
            ' - vm_compute. reflexivity.',
            f' - unfold {prefix}_nb_entries.']
        for proc, _, _ in plans:
            lines += [f'   constructor; [exact {prefix}_{proc["name"]}_nb_checked|].']
        lines += ['   constructor. Qed.',
            f'Lemma {prefix}_certificate : BankRootCertificate {program} {root}%nat {total}%nat {prefix}_entries.',
            'Proof. constructor.',
            f' - exact {prefix}_nb_certificate.',
            f' - unfold {prefix}_entries.']
        for proc, _, _ in plans:
            lines += [f'   constructor; [exact {prefix}_{proc["name"]}_bank_checked|].']
        lines += ['   constructor. Qed.',
            f'Definition {prefix}_physical_relation := bank_phase_related _ _ _ _ {prefix}_certificate.',
            f'Definition {prefix}_isa_relation {{word : Interface.word 32}}',
            ' {Registers : map.map Z word} {Mem : map.map word byte} :=',
            f' @CPURegisterEffectRelation.actual_phase_register_transport word Registers Mem',
            f' {program} {root}%nat {total}%nat {prefix}_entries {prefix}_certificate.',
            f'Definition {prefix}_run1_component {{word : Interface.word 32}} {{BW : Bitwidth 32}}',
            ' {Registers : map.map Z word} {Mem : map.map word byte} :=',
            f' @CPURegisterEffectRelation.actual_phase_run1_register_transport word BW Registers Mem',
            f' {program} {root}%nat {total}%nat {prefix}_entries {prefix}_certificate.']
        audits.extend(prefix + suffix for suffix in ('_physical_relation', '_isa_relation', '_run1_component'))
    for n, name in enumerate(audits):
        lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{n}". exact I. Qed.',
            f'Print Assumptions {name}.']
    return '\n'.join(lines) + '\n'


def audit_bank_output(log, bank_count):
    markers = list(re.finditer(r'^AUTO_ADAPTER_ASSUMPTIONS_([0-9]+)\s*$', log, re.M))
    if bank_count <= 0 or [int(m.group(1)) for m in markers] != list(range(3*bank_count)):
        return False, []
    assumptions = set()
    for index, marker in enumerate(markers):
        stop = markers[index+1].start() if index+1 < len(markers) else len(log)
        chunk = log[marker.end():stop]
        if index % 3 != 2:
            if chunk.count('Closed under the global context') != 1 or 'Axioms:' in chunk:
                return False, sorted(assumptions)
        elif 'Axioms:' in chunk:
            names = set(re.findall(r'^([A-Za-z_][A-Za-z0-9_.]*)\s*:', chunk, re.M)) - {'Axioms'}
            if chunk.count('Axioms:') != 1 or not names or not names <= ALLOWED_AXIOMS:
                return False, sorted(assumptions | names)
            assumptions |= names
        elif chunk.count('Closed under the global context') != 1:
            return False, sorted(assumptions)
    return True, sorted(assumptions)


def check_profile(profile, output, timeout=1200):
    if output.exists():
        raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    binding = profile['ast']
    ast = adapter.load_ast(adapter.ROOT / binding['file'])
    analysis = analyze(ast)
    source = render_bank_adapter(binding, ast, analysis)
    path = output / 'AutoBank.v'
    path.write_text(source)
    report = {'schema_version': 1, 'ast_sha256': ast['source_sha256'],
        'actual_program': binding['program'], 'generated_source_sha256': hashlib.sha256(source.encode()).hexdigest(),
        'candidate_count': analysis['candidate_count'],
        'generated_banks': [{'root': b['root'], 'width': b['total'],
            'writers': [p['name'] for p, _, _ in b['plans']],
            'exports': {role: f'GeneratedBank.AutoBank.bank_{b["root"]}_{suffix}' for role, suffix in (
                ('checked_plan', 'certificate'), ('physical_phase_relation', 'physical_relation'),
                ('conditional_isa_relation', 'isa_relation'), ('conditional_run1_component', 'run1_component'))}}
            for b in analysis['banks']],
        'residuals': analysis['residuals'], 'accepted': False, 'llm_calls': 0,
        'architectural_role_proved': False, 'conditional_isa_component_generated': bool(analysis['banks']),
        'conditional_isa_component_checked': False,
        'isa_register_refinement_proved': False, 'global_invariant_synthesized': False,
        'scope': 'actual physical phase bank relation; ISA values/order/ownership remain obligations'}
    if not analysis['banks']:
        report['status'] = 'no_supported_bank_component'
    else:
        flags = list(adapter.framework.FLAGS)
        for extra in profile.get('coq_load_paths', []):
            flags += ['-R', extra['directory'], extra['namespace']]
        flags += ['-R', str(output.resolve()), 'GeneratedBank']
        started = time.monotonic()
        compiled, timed = run_stage([str(adapter.ROOT/'_opam/bin/coqc'), '-q', *flags,
            str(path.resolve())], output/'coqc.log', timeout)
        report.update(coqc_exit=compiled.returncode, coqc_timed_out=timed,
            coqc_seconds=time.monotonic()-started)
        if compiled.returncode == 0:
            audited, assumptions = audit_bank_output(compiled.stdout, len(analysis['banks']))
            report.update(assumptions_accepted=audited, inherited_assumptions=assumptions)
            started = time.monotonic()
            checked, timed = run_stage([str(adapter.ROOT/'_opam/bin/coqchk'), '-silent',
                *flags, '-norec', 'GeneratedBank.AutoBank'], output/'coqchk.log', timeout)
            report.update(coqchk_exit=checked.returncode, coqchk_timed_out=timed,
                coqchk_seconds=time.monotonic()-started)
            report['accepted'] = audited and checked.returncode == 0 and not analysis['residuals']
            report['conditional_isa_component_checked'] = report['accepted']
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


def emit_library(profile, destination, check=False):
    """Emit the same checked proposal into a persistent, unique Coq library.

    Refuse unsupported candidates and accidental overwrites.  Check mode makes
    regeneration reproducible without touching source or proof objects.
    Emission itself is not evidence of a successful Coq proof.
    """
    binding = profile['ast']
    ast = adapter.load_ast(adapter.ROOT / binding['file'])
    analysis = analyze(ast)
    if not analysis['banks'] or analysis['residuals']:
        raise ValueError('persistent library requires supported candidates without residuals')
    source = render_bank_adapter(binding, ast, analysis)
    destination = Path(destination)
    if check:
        if not destination.is_file() or destination.read_text() != source:
            raise ValueError('persistent bank source differs from current AST generation')
    elif destination.exists():
        raise ValueError('destination exists; use --check-source to verify regeneration')
    else:
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(source)
    return {'source': str(destination), 'source_matches_generator': True,
        'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
        'actual_program': binding['program'], 'coq_checked': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', type=Path, required=True)
    destination = parser.add_mutually_exclusive_group(required=True)
    destination.add_argument('--output', type=Path)
    destination.add_argument('--emit-source', type=Path)
    parser.add_argument('--check-source', action='store_true')
    parser.add_argument('--timeout', type=float, default=1200)
    args = parser.parse_args()
    profile = json.loads(args.profile.read_text())
    if args.emit_source:
        print(json.dumps(emit_library(profile, args.emit_source, args.check_source), indent=2))
        return 0
    if args.check_source:
        parser.error('--check-source requires --emit-source')
    report = check_profile(profile, args.output, args.timeout)
    print(json.dumps(report, indent=2))
    return 0 if report['accepted'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
