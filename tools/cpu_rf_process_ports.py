"""Generate actual process-entry RF equations, not final-LFP equations.

Reuses syntax-checked persistent RF blocks.  Distinguishing these observation
points avoids silently substituting fixed-point inputs for earlier round inputs.
No CPU names, signal IDs, source freshness or global invariant are assumed.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_auto_adapter as adapter
import cpu_rf_read_ports as ports
from cpu_certificate_acceptance import run_stage


def render(profile):
    library = Path(profile['rf_port_library'])
    if library.is_absolute() or '..' in library.parts or library.suffix != '.v':
        raise ValueError('expected a project-relative persistent RF source')
    relative = library.relative_to('src').with_suffix('')
    logical = '.'.join(relative.parts)
    if not adapter.SYMBOL.fullmatch(logical):
        raise ValueError('invalid RF library namespace')
    # Fail closed: the companion must not silently use a stale generated block.
    ports.emit_library(profile, adapter.ROOT/library, check=True)
    binding = profile['ast']
    ast = adapter.load_ast(adapter.ROOT/binding['file'])
    analysis = ports.analyze(ast)
    program, module = binding['program'], ast['module']
    rf = library.stem
    lines = ['(** Generated process-entry equations; no fixed-point premise. *)',
        'From Coq Require Import List ZArith Lia.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVScalarBlockBinding',
        f' {logical} ' + ' '.join([binding['module'], *binding.get('program_imports',[])]) + '.',
        'Import ExtendedSV ExtendedSVScalarBlockBinding.']
    for n, port in enumerate(analysis['ports']):
        b, i = port['block_index'], port['assignment_index']
        block, name = f'{rf}.block_{b}', f'port_{n}'
        w, root = port['width'], port['output_root']
        lines += [f'Lemma {name}_local_checked : scalar_fold_bindingb {block}_order {i}%nat = true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Theorem {name}_process s :',
            f' norm {w} (read_signal (run_process {program} s {module}.{port["process"]}) {root}%nat)',
            f' = norm {w} (eval_expr s {rf}.port_{n}_rhs).',
            'Proof.',
            f' rewrite ({block}_decomposes s).',
            f' exact (checked_scalar_fold_binding {program} {block}_order {i}%nat',
            f' {block}_scalar_{i} false {rf}.port_{n}_rhs {w}%nat {root}%nat',
            f' eq_refl eq_refl {name}_local_checked ltac:(cbn;lia) s).',
            'Qed.']
    for n in range(len(analysis['ports'])):
        lines += [f'Goal True. idtac "RF_PORT_ASSUMPTIONS_{n}". exact I. Qed.',
            f'Print Assumptions port_{n}_process.']
    return '\n'.join(lines)+'\n', analysis


def check_profile(profile, output, timeout=1200):
    output = Path(output)
    if output.exists():
        raise ValueError('output must be fresh; preserve all earlier attempts')
    source, analysis = render(profile)
    output.mkdir(parents=True)
    path = output/'AutoRFProcessPorts.v'
    path.write_text(source)
    flags = list(adapter.framework.FLAGS)
    for extra in profile.get('coq_load_paths',[]):
        flags += ['-R', extra['directory'], extra['namespace']]
    flags += ['-R', str(output.resolve()), 'GeneratedRFProcessPorts']
    report = {'accepted':False, 'ports':len(analysis['ports']), 'llm_calls':0,
        'generated_source_sha256':hashlib.sha256(source.encode()).hexdigest(),
        'residuals':analysis['residuals'], 'observation':'actual process entry/exit',
        'operand_freshness_proved':False, 'global_invariant_synthesized':False}
    started = time.monotonic()
    compiled, timed = run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q','-time',*flags,
        str(path.resolve())],output/'coqc.log',timeout)
    report.update(coqc_exit=compiled.returncode, coqc_timed_out=timed,
        coqc_seconds=time.monotonic()-started)
    if compiled.returncode == 0:
        audited = ports.audit_output(compiled.stdout,len(analysis['ports']))
        started = time.monotonic()
        checked, timed = run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,
            '-norec','GeneratedRFProcessPorts.AutoRFProcessPorts'],output/'coqchk.log',timeout)
        report.update(coqchk_exit=checked.returncode,coqchk_timed_out=timed,
            assumptions_accepted=audited,coqchk_seconds=time.monotonic()-started)
        report['accepted'] = bool(analysis['ports']) and not analysis['residuals'] and audited and checked.returncode == 0
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def emit_library(profile, destination, check=False):
    source, analysis = render(profile)
    if not analysis['ports'] or analysis['residuals']:
        raise ValueError('process library requires supported ports without residuals')
    destination = Path(destination)
    if check:
        if not destination.is_file() or destination.read_text() != source:
            raise ValueError('persistent process source differs from AST generation')
    elif destination.exists():
        raise ValueError('destination exists; use --check-source')
    else:
        destination.parent.mkdir(parents=True,exist_ok=True)
        destination.write_text(source)
    return {'source':str(destination),'source_matches_generator':True,'coq_checked':False,
        'generated_source_sha256':hashlib.sha256(source.encode()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',type=Path,required=True)
    destination = parser.add_mutually_exclusive_group(required=True)
    destination.add_argument('--output',type=Path)
    destination.add_argument('--emit-source',type=Path)
    parser.add_argument('--check-source',action='store_true')
    parser.add_argument('--timeout',type=float,default=1200)
    args = parser.parse_args()
    if not 0 < args.timeout <= 1200:
        parser.error('timeout must be greater than zero and at most 1200 seconds')
    profile = json.loads(args.profile.read_text())
    if args.emit_source:
        print(json.dumps(emit_library(profile,args.emit_source,args.check_source),indent=2))
        return 0
    if args.check_source:
        parser.error('--check-source requires --emit-source')
    report = check_profile(profile,args.output,args.timeout)
    print(json.dumps(report,indent=2))
    return 0 if report['accepted'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
