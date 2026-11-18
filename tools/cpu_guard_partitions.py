"""Check exhaustive sampled guard partitions, not CPU reachability.

Truth tables only propose the partition. Coq proves both implications against
the original expression path for arbitrary State. No architecture role is used.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import time
import cpu_auto_adapter as adapter
import cpu_scalar_guard_bindings as bindings
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage


def proposal(profile,roots=None):
    ast,residuals,rows,source,count=bindings.proposal(profile,roots)
    _,_,expressions,_,_=bindings.paths.expressions.proposal(profile,roots)
    _,_,paths,_,_=bindings.paths.proposal(profile,roots)
    by_root={item['root']:item['expression'] for item in expressions}
    lines=['From Coq Require Import Lia.',
        'Require Import Lang.ExtendedSVBankAlignment.',
        'Import ExtendedSVBankAlignment.',
        'Lemma guard_partition_bit_cases value : norm 1 value = 0%Z \\/ norm 1 value = 1%Z.',
        'Proof. pose proof (norm_bounds 1 value) as H. cbn in H. lia. Qed.',
        f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
        'Print Assumptions guard_partition_bit_cases.']
    count+=1;exports=[]
    for item in paths:
        root,path=item['root'],item['path'];stem=item['theorem'][:-len('_phase')]
        e=by_root[root];inputs=set()
        try:
            for choice in path:
                inputs |= bindings.bit_variables(e.args[1])
                e=e.args[2 if choice else 3]
        except ValueError:continue  # The binding proposal already reports this residual.
        matching=[row for row in rows if row['root']==root and row['path']==path]
        predicates=[row['guard_theorem'][:-len('_guard')] for row in matching]
        disjunction=' \\/ '.join(name+' s' for name in predicates)+(' \\/ False' if predicates else 'False')
        names=[f'Hbit{i}' for i in range(len(inputs))]
        lines += [f'Lemma {stem}_inputs_complete s :',
            f' PathHolds s root_{root}_expression {stem}_choices <-> ({disjunction}).',
            'Proof. split.', ' - intro HP.']
        for name,r in zip(names,sorted(inputs)):
            lines += [f'   all: destruct (guard_partition_bit_cases (read_signal s {r}%nat)) as [{name}|{name}].']
        lines += [f'   all: cbn [PathHolds root_{root}_expression {stem}_choices eval_expr] in HP.']
        if names:lines+=['   all: rewrite '+', '.join(names)+' in HP.']
        lines+=['   all: vm_compute in HP.']
        if predicates:lines+=['   all: unfold '+', '.join(predicates)+'.']
        if names and predicates:lines+=['   all: rewrite '+', '.join(names)+'.']
        lines+=['   all: intuition congruence.', ' - intro HC.']
        for row in matching:
            lines += [f'   destruct HC as [HI|HC]; [exact ({row["guard_theorem"]} s HI)|].']
        lines+=['   contradiction.', 'Qed.',
            f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
            f'Print Assumptions {stem}_inputs_complete.']
        count+=1
        exports.append(dict(root=root,path=path,inputs=sorted(inputs),
            cases=len(matching),theorem=stem+'_inputs_complete'))
    return ast,residuals,exports,source+'\n'.join(lines)+'\n',count


def check_profile(profile,output,roots=None,timeout=1200):
    output=Path(output)
    if output.exists():raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    ast,residuals,exports,source,count=proposal(profile,roots)
    file=output/'GuardPartitions.v';file.write_text(source)
    report=dict(accepted=False,ast_sha256=ast['source_sha256'],
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),actual_program=profile['ast']['program'],
        partitions=exports,residuals=residuals,audited_exports=count,llm_calls=0,
        reachable_inputs_proved=False,global_invariant_synthesized=False,
        binding_coverage_proved=False)
    if residuals or not exports:report['status']='unsupported_guard_partition_selection'
    else:
        flags=list(adapter.framework.FLAGS)
        for extra in profile.get('coq_load_paths',[]):flags+=['-R',extra['directory'],extra['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedGuardPartitions']
        start=time.monotonic()
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(file.resolve())],output/'coqc.log',timeout)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
        if c.returncode==0:
            report['assumptions_closed']=scalar.audit_output(c.stdout,count)
            start=time.monotonic()
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedGuardPartitions.GuardPartitions'],output/'coqchk.log',timeout)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-start)
            report['accepted']=report['assumptions_closed'] and k.returncode==0
            report['binding_coverage_proved']=report['accepted']
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--roots',type=int,nargs='+')
    p.add_argument('--timeout',type=float,default=1200)
    a=p.parse_args()
    if not 0<a.timeout<=1200:p.error('timeout must be positive and at most1200 seconds')
    report=check_profile(json.loads(a.profile.read_text()),a.output,a.roots,a.timeout)
    print(json.dumps(report,indent=2));return 0 if report['accepted'] else 1


if __name__=='__main__':raise SystemExit(main())
