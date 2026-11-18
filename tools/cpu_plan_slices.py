"""Generate checked actual-phase root slices, including NBA guards and cases.

The Python slice is an untrusted proposal. Coq checks it against slice_plan,
whose root-projection preservation is proved independently for every plan.
No token identity, architectural mapping or global invariant is inferred.
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


def slice_plan(plan, root, fuel=512):
    T = adapter.Term
    if fuel == 0:
        return plan
    n, a = plan.name, plan.args
    if n == 'NEmpty':
        return plan
    if n == 'NAssign':
        return plan if adapter.root_of(a[1]) == root else T('NEmpty')
    if n == 'NSeq':
        return T(n, (T('list', tuple(slice_plan(p,root,fuel-1) for p in a[0].args)),))
    if n == 'NIf':
        return T(n, (a[0],slice_plan(a[1],root,fuel-1),slice_plan(a[2],root,fuel-1)))
    if n == 'NCase':
        arms = tuple(T('pair',(arm.args[0],slice_plan(arm.args[1],root,fuel-1)))
            for arm in a[1].args)
        return T(n,(a[0],T('list',arms)))
    raise ValueError('unsupported plan constructor: '+n)


def proposal(profile, roots=None):
    binding = profile['ast']
    ast = adapter.load_ast(adapter.ROOT/binding['file'])
    found = scalar.analyze(ast,roots)
    analysis = found['analysis']
    source = adapter.render_adapter(binding['module'],binding['program'],ast,
        analysis,binding.get('program_imports',[]))
    lines = ['Require Import Lang.ExtendedSVPlanRootSlice.',
        'Import ExtendedSVPlanRootSlice.']
    count = 3*len(analysis['plans'])+2*len(analysis['roots'])
    metrics = []
    for root in analysis['roots']:
        entries, checks = [], []
        before = after = 0
        for proc, plan in analysis['plans']:
            if root not in proc['writers']:
                continue
            name = f'root_{root}_{proc["name"]}_slice'
            proposed = slice_plan(plan,root)
            entries.append(f'({ast["module"]}.{proc["name"]}, {name})')
            checks.append(name+'_checked')
            before += sum(n.name=='NAssign' for n in adapter.walk(plan))
            after += sum(n.name=='NAssign' for n in adapter.walk(proposed))
            lines += [f'Definition {name} : NbPlan := {adapter.render(proposed)}.',
                f'Lemma {name}_checked : slice_plan 512 {root}%nat {proc["name"]}_plan = {name}.',
                'Proof. vm_compute. reflexivity. Qed.']
        prefix = f'root_{root}'
        lines += [f'Definition {prefix}_sliced_entries : list (Process * NbPlan) := [{"; ".join(entries)}].',
            f'Lemma {prefix}_sliced_updates old driven :',
            f' sliced_transition_updates 512 {root}%nat old driven {prefix}_plan_entries =',
            f' plan_transition_updates old driven {prefix}_sliced_entries.',
            'Proof.',
            f' unfold sliced_transition_updates, plan_transition_updates, {prefix}_plan_entries, {prefix}_sliced_entries.',
            ' cbn [flat_map fst snd].',
            ' rewrite '+', '.join(checks)+'. reflexivity.',
            'Qed.',
            f'Theorem {prefix}_sliced_phase ev pre : changed_signal ev <> {root}%nat ->',
            f' read_signal (PhaseSemantics {binding["program"]} ev pre) {root}%nat =',
            f' apply_updates_root_value {root}%nat (read_signal pre {root}%nat)',
            f'   (plan_transition_updates pre (phase_driven_state {binding["program"]} ev pre)',
            f'     {prefix}_sliced_entries).',
            'Proof.',
            f' intro HE. rewrite (checked_sliced_phase {binding["program"]} {root}%nat',
            f' {prefix}_plan_entries 512 {prefix}_plan_certificate ev pre HE).',
            f' now rewrite {prefix}_sliced_updates.',
            'Qed.',
            f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
            f'Print Assumptions {prefix}_sliced_phase.']
        count += 1
        metrics.append(dict(root=root,original_assignments=before,sliced_assignments=after,
            export=prefix+'_sliced_phase'))
    return ast,found,source+'\n'.join(lines)+'\n',count,metrics


def emit_library(profile, destination, roots=None, check=False):
    _,found,source,count,metrics=proposal(profile,roots)
    if found['residuals'] or not metrics:
        raise ValueError('unsupported slice selection: '+json.dumps(found['residuals']))
    path=Path(destination)
    if check:
        if not path.is_file() or path.read_text()!=source:
            raise ValueError('persistent slice source differs from current generation')
    elif path.exists():
        raise ValueError('destination exists; use --check-source')
    else:
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(source)
    return dict(source=str(path),source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        source_matches_generator=True,audited_exports=count,projections=metrics,coq_checked=False)


def check_profile(profile, output, roots=None, timeout=1200):
    output = Path(output)
    if output.exists():
        raise ValueError('output must be fresh; retain old evidence')
    output.mkdir(parents=True)
    ast,found,source,count,metrics = proposal(profile,roots)
    path = output/'PlanSlices.v'
    path.write_text(source)
    report = dict(accepted=False,ast_sha256=ast['source_sha256'],
        actual_program=profile['ast']['program'],
        generated_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        requested_roots=found['requested_roots'],residuals=found['residuals'],
        projections=metrics,audited_exports=count,llm_calls=0,
        global_invariant_synthesized=False,token_freshness_proved=False)
    if found['residuals'] or not metrics:
        report['status'] = 'unsupported_scalar_selection'
    else:
        flags = list(adapter.framework.FLAGS)
        for extra in profile.get('coq_load_paths',[]):
            flags += ['-R',extra['directory'],extra['namespace']]
        flags += ['-R',str(output.resolve()),'GeneratedPlanSlices']
        start = time.monotonic()
        compiled,timed = run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,
            str(path.resolve())],output/'coqc.log',timeout)
        report.update(coqc_exit=compiled.returncode,coqc_timed_out=timed,
            coqc_seconds=time.monotonic()-start)
        if compiled.returncode == 0:
            report['assumptions_closed'] = scalar.audit_output(compiled.stdout,count)
            start = time.monotonic()
            kernel,timed = run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',
                *flags,'-norec','GeneratedPlanSlices.PlanSlices'],output/'coqchk.log',timeout)
            report.update(coqchk_exit=kernel.returncode,coqchk_timed_out=timed,
                coqchk_seconds=time.monotonic()-start)
            report['accepted'] = report['assumptions_closed'] and kernel.returncode==0
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile',type=Path,required=True)
    target=p.add_mutually_exclusive_group(required=True)
    target.add_argument('--output',type=Path)
    target.add_argument('--emit-source',type=Path)
    p.add_argument('--check-source',action='store_true')
    p.add_argument('--roots',type=int,nargs='+')
    p.add_argument('--timeout',type=float,default=1200)
    a=p.parse_args()
    if not 0<a.timeout<=1200:
        p.error('timeout must be positive and at most1200 seconds')
    profile=json.loads(a.profile.read_text())
    if a.emit_source:
        result=emit_library(profile,a.emit_source,a.roots,a.check_source)
    else:
        if a.check_source:
            p.error('--check-source requires --emit-source')
        result=check_profile(profile,a.output,a.roots,a.timeout)
    print(json.dumps(result,indent=2))
    return 0 if a.emit_source or result['accepted'] else 1


if __name__=='__main__':
    raise SystemExit(main())
