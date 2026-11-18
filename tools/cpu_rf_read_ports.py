"""Generate actual combinational-LFP output equations for RF reader ports.

Straight-line blocking process decompositions and ordered sampling/frame
checks are independently checked by Coq.  This is not a replacement CPU
scheduler, a forwarding proof or a discovered architectural invariant.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_auto_adapter as adapter
import cpu_bank_reads as reads
from cpu_certificate_acceptance import run_stage


def flatten_blocking(body):
    if body.name == 'SSkip': return []
    if body.name == 'SSeq':
        return [assignment for st in body.args[0].args for assignment in flatten_blocking(st)]
    if body.name == 'SAssign' and body.args[0].name == 'false' and body.args[2].name == 'LVar':
        return [body]
    raise ValueError('reader process is not a straight-line blocking scalar block')


def analyze(ast):
    raw = reads.analyze(ast)
    residuals, blocks, ports = list(raw['residuals']), [], []
    by_name = {p['name']: p for p in ast['processes']}
    combinations = [p for p in ast['processes'] if p['kind'] == 'Combinational']
    for name in dict.fromkeys(site['process'] for site in raw['sites']):
        proc = by_name[name]
        try:
            if proc['kind'] != 'Combinational':
                raise ValueError('raw read site is not in a combinational reader')
            assignments = flatten_blocking(proc['body'])
            block = {'process':name,'comb_index':combinations.index(proc),'assignments':assignments}
            block_index = len(blocks)
            blocks.append(block)
            matching = [s for s in raw['sites'] if s['process'] == name]
            for index, st in enumerate(assignments):
                _, rhs, lhs = st.args
                sites = [s for s in matching if adapter.Term('ESel',
                    (adapter.Term('32'), adapter.Term('EVar',
                        (adapter.Term(str(s['total'])),adapter.Term(str(s['root'])))),s['offset']))
                    in set(adapter.walk(rhs))]
                if sites:
                    ports.append({'block_index':block_index,'assignment_index':index,
                        'process':name,'width':int(lhs.args[0].name),'output_root':int(lhs.args[1].name),
                        'rhs':rhs,'raw_read_sites':len(sites)})
        except ValueError as exc:
            residuals.append({'process':name,'reason':str(exc)})
    return {'blocks':blocks,'ports':ports,'residuals':residuals,'raw_site_count':len(raw['sites'])}


def render(binding, ast, analysis, opaque_single=False):
    imports = [binding['module'], *binding.get('program_imports', [])]
    program, mod = binding['program'], ast['module']
    syntax = binding.get('syntax_program')
    transport = syntax is not None and syntax != program
    if not all(isinstance(s,str) and adapter.SYMBOL.fullmatch(s)
               for s in [program,*imports,*([syntax] if syntax is not None else [])]):
        raise ValueError('invalid program/import binding')
    lines = ['(** Generated actual LFP reader-output equations; no ISA identity assumed. *)',
        'From Coq Require Import List ZArith Lia.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVScalarBlockBinding' +
            (' Lang.ExtendedSVCombConfiguration' if transport else ''),
        ' ' + ' '.join(imports) + '.',
        'Import ListNotations ExtendedSV ExtendedSVScalarBlockBinding.',
        f'Definition actual_combs := filter is_comb (processes {program}).']
    if transport:
        lines += [f'Lemma syntax_processes_checked : processes {syntax} = processes {program}.',
            'Proof. reflexivity. Qed.',
            f'Lemma syntax_fuel_checked : statement_fuel {syntax} = statement_fuel {program}.',
            'Proof. reflexivity. Qed.',
            f'Definition syntax_lfp := ExtendedSVCombConfiguration.configuration_lfp',
            f' {syntax} {program} syntax_processes_checked syntax_fuel_checked.']
    for n, block in enumerate(analysis['blocks']):
        prefix = f'block_{n}'
        for k, st in enumerate(block['assignments']):
            lines += [f'Definition {prefix}_scalar_{k} : Process :=',
                ' {| process_kind := Combinational; process_events := [];',
                f'    process_body := {adapter.render(st)}; process_source_line := 0 |}}.']
        order = '[' + '; '.join(f'{prefix}_scalar_{k}' for k in range(len(block['assignments']))) + ']'
        lines += [f'Definition {prefix}_order : list Process := {order}.',
            f'Lemma {prefix}_registered : nth_error actual_combs {block["comb_index"]}%nat',
            f' = Some {mod}.{block["process"]}.',
            'Proof. vm_compute. reflexivity. Qed.']
        if len(block['assignments']) > 1 or opaque_single:
            lines += ['Local Opaque eval_expr apply_update.']
        lines += [
            f'Lemma {prefix}_decomposes s : run_process {program} s {mod}.{block["process"]} =',
            f' fold_left (run_process {program}) {prefix}_order s.',
            'Proof. reflexivity. Qed.']
        if len(block['assignments']) > 1 or opaque_single:
            lines += ['Local Transparent eval_expr apply_update.']
    for n, port in enumerate(analysis['ports']):
        block = analysis['blocks'][port['block_index']]
        prefix, name = f'block_{port["block_index"]}', f'port_{n}'
        k, pi = port['assignment_index'], block['comb_index']
        proc, scalar = f'{mod}.{block["process"]}', f'{prefix}_scalar_{k}'
        w, root = port['width'], port['output_root']
        lines += [f'Definition {name}_rhs : Expr := {adapter.render(port["rhs"])}.',
            f'Lemma {name}_checked : scalar_block_bindingb actual_combs {pi}%nat',
            f' {prefix}_order {k}%nat = true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Theorem {name}_lfp seed fixed : CombLFP {program} seed fixed ->',
            f' norm {w} (read_signal fixed {root}%nat) = norm {w} (eval_expr fixed {name}_rhs).',
            'Proof.',
            f' exact (checked_scalar_block_binding {program} actual_combs {pi}%nat {proc}',
            f' {prefix}_order {k}%nat {scalar} false {name}_rhs {w}%nat {root}%nat seed fixed',
            f' eq_refl {prefix}_registered eq_refl eq_refl {prefix}_decomposes',
            f' {name}_checked ltac:(cbn;lia)).',
            'Qed.']
        if transport:
            lines += [f'Theorem {name}_syntax_lfp seed fixed : CombLFP {syntax} seed fixed ->',
                f' norm {w} (read_signal fixed {root}%nat) = norm {w} (eval_expr fixed {name}_rhs).',
                f'Proof. intro HL;exact ({name}_lfp seed fixed (syntax_lfp seed fixed HL)). Qed.']
    audits = [f'port_{n}_lfp' for n in range(len(analysis['ports']))]
    if transport:
        audits += [f'port_{n}_syntax_lfp' for n in range(len(analysis['ports']))]
    for n, theorem in enumerate(audits):
        lines += [f'Goal True. idtac "RF_PORT_ASSUMPTIONS_{n}". exact I. Qed.',
            f'Print Assumptions {theorem}.']
    return '\n'.join(lines)+'\n'


def audit_output(log, count):
    markers = list(re.finditer(r'^RF_PORT_ASSUMPTIONS_([0-9]+)\s*$',log,re.M))
    if count <= 0 or [int(m.group(1)) for m in markers] != list(range(count)):
        return False
    for n, marker in enumerate(markers):
        end = markers[n+1].start() if n+1 < len(markers) else len(log)
        chunk = log[marker.end():end]
        if chunk.count('Closed under the global context') != 1 or 'Axioms:' in chunk:
            return False
    return True


def check_profile(profile, output, timeout=1200):
    if output.exists(): raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    binding = profile['ast']
    ast = adapter.load_ast(adapter.ROOT/binding['file'])
    analysis = analyze(ast)
    transport = binding.get('syntax_program') is not None and binding['syntax_program'] != binding['program']
    source = render(binding,ast,analysis)
    path = output/'AutoRFPorts.v'
    path.write_text(source)
    report = {'schema_version':1,'ast_sha256':ast['source_sha256'],
        'generated_source_sha256':hashlib.sha256(source.encode()).hexdigest(),
        'actual_program':binding['program'],'accepted':False,'llm_calls':0,
        'ports':[{k:v for k,v in port.items() if k!='rhs'} for port in analysis['ports']],
        'blocks':len(analysis['blocks']),'raw_site_count':analysis['raw_site_count'],
        'syntax_lfp_transport_generated':transport,
        'audited_exports':len(analysis['ports'])*(2 if transport else 1),
        'residuals':analysis['residuals'],'operand_freshness_proved':False,
        'instruction_identity_proved':False,'global_invariant_synthesized':False,
        'scope':'actual complete combinational reader output equations; ISA/age remain obligations'}
    if analysis['ports']:
        flags = list(adapter.framework.FLAGS)
        for extra in profile.get('coq_load_paths',[]):
            flags += ['-R',extra['directory'],extra['namespace']]
        flags += ['-R',str(output.resolve()),'GeneratedRFPorts']
        started = time.monotonic()
        compiled,timed = run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q','-time',*flags,
            str(path.resolve())],output/'coqc.log',timeout)
        report.update(coqc_exit=compiled.returncode,coqc_timed_out=timed,
            coqc_seconds=time.monotonic()-started)
        if compiled.returncode == 0:
            audited = audit_output(compiled.stdout,report['audited_exports'])
            started = time.monotonic()
            checked,timed = run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,
                '-norec','GeneratedRFPorts.AutoRFPorts'],output/'coqchk.log',timeout)
            report.update(coqchk_exit=checked.returncode,coqchk_timed_out=timed,
                coqchk_seconds=time.monotonic()-started,assumptions_accepted=audited)
            report['accepted'] = audited and checked.returncode == 0 and not analysis['residuals']
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def emit_library(profile, destination, check=False):
    binding = profile['ast']
    ast = adapter.load_ast(adapter.ROOT/binding['file'])
    analysis = analyze(ast)
    if not analysis['ports'] or analysis['residuals']:
        raise ValueError('persistent reader library needs supported ports without residuals')
    source = render(binding,ast,analysis)
    destination = Path(destination)
    if check:
        if not destination.is_file() or destination.read_text() != source:
            raise ValueError('persistent reader source differs from AST generation')
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
    profile = json.loads(args.profile.read_text())
    if args.emit_source:
        print(json.dumps(emit_library(profile,args.emit_source,args.check_source),indent=2))
        return 0
    if args.check_source: parser.error('--check-source requires --emit-source')
    report = check_profile(profile,args.output,args.timeout)
    print(json.dumps(report,indent=2))
    return 0 if report['accepted'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
