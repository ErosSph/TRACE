"""Propose checked next-value expressions for guarded whole-scalar NBA roots.

Uses a proved compiler, not guard-value guesses. Architectural roles, token
identity and invariant preservation remain separate obligations.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_auto_adapter as adapter
import cpu_scalar_captures as scalar
import cpu_plan_slices as slices
from cpu_certificate_acceptance import run_stage


def empty_plan(plan,fuel):
    if fuel==0:return False
    if plan.name=='NEmpty':return True
    if plan.name=='NAssign':return False
    if plan.name=='NSeq':return all(empty_plan(p,fuel-1) for p in plan.args[0].args)
    if plan.name=='NIf':return all(empty_plan(p,fuel-1) for p in plan.args[1:])
    if plan.name=='NCase':return all(empty_plan(a.args[1],fuel-1) for a in plan.args[1].args)
    raise ValueError('unknown NBA plan constructor')


def case_expression(width,scrutinee,arms,seed):
    if not arms:return seed
    key,body=arms[0]
    if key.name=='None':return case_expression(width,scrutinee,arms[1:],body)
    T=adapter.Term
    guard=T('EBinary',(T('1'),T('BEq'),scrutinee,key.args[0]))
    return T('ECond',(T(str(width)),guard,body,
        case_expression(width,scrutinee,arms[1:],seed)))


def compile_expression(plan,root,width,seed,fuel=512):
    if fuel==0:return None
    if empty_plan(plan,fuel):return seed
    n,a=plan.name,plan.args
    if n=='NEmpty':return seed
    if n=='NAssign':
        rhs,lhs=a
        if adapter.root_of(lhs)!=root:return seed
        return rhs if lhs.name=='LVar' and int(lhs.args[0].name)==width else None
    if n=='NSeq':
        result=seed
        for p in a[0].args:
            result=compile_expression(p,root,width,result,fuel-1)
            if result is None:return None
        return result
    if n=='NIf':
        yes=compile_expression(a[1],root,width,seed,fuel-1)
        no=compile_expression(a[2],root,width,seed,fuel-1)
        if yes is None or no is None:return None
        return adapter.Term('ECond',(adapter.Term(str(width)),a[0],yes,no))
    if n=='NCase':
        arms=[]
        for arm in a[1].args:
            key,body=arm.args
            result=compile_expression(body,root,width,seed,fuel-1)
            if result is None:return None
            arms.append((key,result))
        return case_expression(width,a[0],arms,seed)
    raise ValueError('unknown NBA plan constructor')


def proposal(profile,roots=None):
    binding=profile['ast']
    ast=adapter.load_ast(adapter.ROOT/binding['file'])
    found=scalar.analyze(ast,roots)
    residuals=list(found['residuals']);outputs=[]
    for root in found['analysis']['roots']:
        writers=[(p,plan) for p,plan in found['analysis']['plans'] if root in p['writers']]
        if len(writers)!=1:
            residuals.append(dict(root=root,reason='scalar expression phase needs one actual writer'))
            continue
        proc,plan=writers[0]
        assignment=next(n for n in adapter.walk(proc['body'])
            if n.name=='SAssign' and adapter.root_of(n.args[2])==root)
        width=int(assignment.args[2].args[0].name)
        seed=adapter.Term('EVar',(adapter.Term(str(width)),adapter.Term(str(root))))
        expression=compile_expression(slices.slice_plan(plan,root),root,width,seed)
        if expression is None:
            residuals.append(dict(root=root,reason='guarded scalar expression compilation unsupported'))
        else:outputs.append(dict(root=root,width=width,process=proc['name'],expression=expression))
    selected=[o['root'] for o in outputs]
    analysis=scalar.analyze(ast,selected)['analysis'] if selected else dict(
        plans=[],effects=[],residual=[],roots=[],plan_roots=[])
    source=adapter.render_adapter(binding['module'],binding['program'],ast,analysis,
        binding.get('program_imports',[]))
    lines=['Require Import Lang.ExtendedSVScalarExpression Lang.ExtendedSVPlanRootSlice.',
        'Import ExtendedSVScalarExpression ExtendedSVPlanRootSlice.']
    count=3*len(analysis['plans'])+2*len(analysis['roots'])
    for item in outputs:
        root,width,proc=item['root'],item['width'],item['process']
        stem=f'root_{root}'
        lines += [f'Definition {stem}_expression : Expr := {adapter.render(item["expression"])}.',
            f'Lemma {stem}_expression_checked : compile_scalar 512 {root}%nat {width}',
            f' (slice_plan 512 {root}%nat {proc}_plan)',
            f' (EVar {width} {root}) = Some {stem}_expression.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Definition {stem}_expression_process := checked_sliced_scalar_process',
            f' {binding["program"]} {ast["module"]}.{proc} {proc}_plan {root}%nat {width}',
            f' 512 512 {stem}_expression {proc}_plan_checked {stem}_expression_checked.',
            f'Definition {stem}_expression_phase := checked_sliced_scalar_phase',
            f' {binding["program"]} {root}%nat {ast["module"]}.{proc} {proc}_plan {width}',
            f' 512 512 {stem}_expression {stem}_plan_certificate {stem}_expression_checked.']
        for suffix in ['process','phase']:
            lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
                f'Print Assumptions {stem}_expression_{suffix}.']
            count+=1
    return ast,residuals,outputs,source+'\n'.join(lines)+'\n',count


def emit_library(profile,destination,roots=None,check=False):
    _,residuals,outputs,source,count=proposal(profile,roots)
    if residuals or not outputs:raise ValueError('unsupported expression selection: '+json.dumps(residuals))
    path=Path(destination)
    if check:
        if not path.is_file() or path.read_text()!=source:
            raise ValueError('persistent expression source differs from current generation')
    elif path.exists():raise ValueError('destination exists; use --check-source')
    else:
        path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
    return dict(source=str(path),source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        roots=[o['root'] for o in outputs],audited_exports=count,
        source_matches_generator=True,coq_checked=False)


def check_profile(profile,output,roots=None,timeout=1200):
    output=Path(output)
    if output.exists():raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    ast,residuals,outputs,source,count=proposal(profile,roots)
    path=output/'ScalarExpressions.v';path.write_text(source)
    exports=[]
    for item in outputs:
        inputs=sorted({tuple(int(a.name) for a in n.args) for n in adapter.walk(item['expression']) if n.name=='EVar'})
        exports.append(dict(root=item['root'],width=item['width'],process=item['process'],
            expression=adapter.render(item['expression']),sampled_inputs=inputs))
    report=dict(accepted=False,ast_sha256=ast['source_sha256'],actual_program=profile['ast']['program'],
        generated_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        residuals=residuals,outputs=exports,audited_exports=count,llm_calls=0,
        global_invariant_synthesized=False,token_freshness_proved=False)
    if residuals or not outputs:report['status']='unsupported_scalar_expression_selection'
    else:
        flags=list(adapter.framework.FLAGS)
        for extra in profile.get('coq_load_paths',[]):flags+=['-R',extra['directory'],extra['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedScalarExpressions']
        start=time.monotonic()
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(path.resolve())],output/'coqc.log',timeout)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
        if c.returncode==0:
            report['assumptions_closed']=scalar.audit_output(c.stdout,count)
            start=time.monotonic()
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedScalarExpressions.ScalarExpressions'],output/'coqchk.log',timeout)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-start)
            report['accepted']=report['assumptions_closed'] and k.returncode==0
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile',type=Path,required=True)
    target=p.add_mutually_exclusive_group(required=True)
    target.add_argument('--output',type=Path);target.add_argument('--emit-source',type=Path)
    p.add_argument('--check-source',action='store_true')
    p.add_argument('--roots',type=int,nargs='+');p.add_argument('--timeout',type=float,default=1200)
    a=p.parse_args()
    if not 0<a.timeout<=1200:p.error('timeout must be positive and at most1200 seconds')
    profile=json.loads(a.profile.read_text())
    if a.emit_source:report=emit_library(profile,a.emit_source,a.roots,a.check_source)
    else:
        if a.check_source:p.error('--check-source requires --emit-source')
        report=check_profile(profile,a.output,a.roots,a.timeout)
    print(json.dumps(report,indent=2));return 0 if a.emit_source or report['accepted'] else 1


if __name__=='__main__':raise SystemExit(main())
