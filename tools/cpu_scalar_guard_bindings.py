"""Propose sampled one-bit input bindings and check their phase contracts.

Bindings are sufficient guard conditions, NOT reachable-state invariants.
Unsupported guards fail closed. Python's truth table is untrusted: each
proposed row is proved symbolically by Coq against the actual expression.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import time
import cpu_auto_adapter as adapter
import cpu_scalar_captures as scalar
import cpu_scalar_expression_paths as paths
from cpu_certificate_acceptance import run_stage


def bit_variables(e):
    n,a=e.name,e.args
    if n=='EVar' and a[0].name=='1':return {int(a[1].name)}
    if n=='EConst' and a[0].name=='1':return set()
    if n=='EUnary' and a[0].name=='1' and a[1].name in {'UNot','UNegate','URedOr'}:
        return bit_variables(a[2])
    if n=='EBinary' and a[0].name=='1' and a[1].name in {'BAnd','BOr','BXor','BEq','BNeq'}:
        return bit_variables(a[2]) | bit_variables(a[3])
    raise ValueError('guard outside one-bit binding template')


def eval_bit(e,values):
    n,a=e.name,e.args
    if n=='EVar':return values[int(a[1].name)]
    if n=='EConst':return int(a[1].name)&1
    if n=='EUnary':
        v=eval_bit(a[2],values)
        return {'UNot':1-v,'UNegate':(-v)&1,'URedOr':v}[a[1].name]
    x,y=eval_bit(a[2],values),eval_bit(a[3],values)
    return {'BAnd':x&y,'BOr':x|y,'BXor':x^y,'BEq':int(x==y),'BNeq':int(x!=y)}[a[1].name]


def guard_rows(expression,path,max_bits=8):
    guards=[];e=expression
    for choice in path:
        if e.name!='ECond':raise ValueError('invalid expression path')
        guards.append((e.args[1],choice));e=e.args[2 if choice else 3]
    roots=sorted(set().union(*(bit_variables(g) for g,_ in guards)))
    if len(roots)>max_bits:raise ValueError('guard binding input budget exceeded')
    return [dict(zip(roots,values)) for values in itertools.product((0,1),repeat=len(roots))
        if all(bool(eval_bit(g,dict(zip(roots,values))))==want for g,want in guards)]


def input_formula(values):
    atoms=[f'norm 1 (read_signal s {root}%nat) = {value}%Z'
        for root,value in sorted(values.items())]
    return ' /\\ '.join(atoms) if atoms else 'True'


def proposal(profile,roots=None):
    ast,residuals,outputs,source,count=paths.proposal(profile,roots)
    # Read the SAME structurally proposed expressions; never use role hints.
    _,_,expressions,_,_=paths.expressions.proposal(profile,roots)
    by_root={item['root']:item['expression'] for item in expressions}
    lines=['Require Import Lang.ExtendedSVWordInvariant.',
        'Import ExtendedSVWordInvariant.',
        'Lemma guard_binding_var_value (width root : nat) (s : State) :',
        ' norm width (eval_expr s (EVar width root)) = norm width (read_signal s root).',
        'Proof. change (norm width (norm width (read_signal s root)) =',
        ' norm width (read_signal s root)). apply norm_idempotent. Qed.',
        f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
        'Print Assumptions guard_binding_var_value.',
        'Local Opaque PhaseSemantics phase_driven_state read_signal.']
    count+=1
    exports=[];program=profile['ast']['program']
    residuals=list(residuals)
    for item in outputs:
        root,width,path=item['root'],item['width'],item['path']
        try:rows=guard_rows(by_root[root],path)
        except ValueError as exc:
            residuals.append(dict(root=root,path=path,reason=str(exc)));continue
        path_stem=item['theorem'][:-len('_phase')]
        leaf=adapter.Parser(item['leaf']).complete()
        simple_read=leaf.name=='EVar' and int(leaf.args[0].name)==width
        proc=next(o['process'] for o in expressions if o['root']==root)
        for index,values in enumerate(rows):
            stem=f'{path_stem}_inputs_{index}'
            names=[f'H{i}' for i in range(len(values))]
            intro=('intros ('+' & '.join(names)+').' if len(names)>1 else
                'intro '+(names[0] if names else '_')+'.')
            lines += [f'Definition {stem} (s : State) : Prop := {input_formula(values)}.',
                f'Lemma {stem}_guard s : {stem} s ->',
                f' PathHolds s root_{root}_expression {path_stem}_choices.',
                'Proof.',f' unfold {stem}. {intro}',
                f' cbn [PathHolds root_{root}_expression {path_stem}_choices eval_expr].']
            if names:lines+=[' rewrite '+', '.join(names)+'.']
            lines+=[' vm_compute. repeat split; reflexivity. Qed.',
                f'Lemma {stem}_phase ev pre : changed_signal ev <> {root}%nat ->',
                f' process_matches_states pre (phase_driven_state {program} ev pre)',
                f' {ast["module"]}.{proc} = true ->',
                f' {stem} (phase_driven_state {program} ev pre) ->',
                f' norm {width} (read_signal (PhaseSemantics {program} ev pre) {root}%nat) =']
            if simple_read:
                lines += [f' norm {width} (read_signal (phase_driven_state {program} ev pre) {leaf.args[1].name}%nat).']
            else:
                lines += [f' norm {width} (eval_expr (phase_driven_state {program} ev pre) {path_stem}_leaf).']
            lines += ['Proof. intros HE HS HI.',
                f' pose proof ({path_stem}_phase ev pre HE HS',
                f'   ({stem}_guard (phase_driven_state {program} ev pre) HI)) as H.']
            if simple_read:
                lines += [f' exact (eq_trans H (guard_binding_var_value {width}%nat',
                    f'   {leaf.args[1].name}%nat (phase_driven_state {program} ev pre))). Qed.']
            else:lines+=[' exact H. Qed.']
            for suffix in ['guard','phase']:
                lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
                    f'Print Assumptions {stem}_{suffix}.']
                count+=1
            exports.append(dict(root=root,path=path,inputs=values,
                theorem=stem+'_phase',guard_theorem=stem+'_guard',simple_read=simple_read))
    return ast,residuals,exports,source+'\n'.join(lines)+'\n',count


def emit_library(profile,destination,roots=None,check=False):
    """Persist exact generated text; emission alone is never a proof result."""
    _,residuals,exports,source,count=proposal(profile,roots)
    if residuals or not exports:raise ValueError('unsupported guard binding selection')
    path=Path(destination)
    if check:
        if not path.is_file() or path.read_text()!=source:
            raise ValueError('persistent guard binding source differs from generation')
    elif path.exists():raise ValueError('destination exists; use --check-source')
    else:
        path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
    return dict(source=str(path),source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        bindings=len(exports),audited_exports=count,source_matches_generator=True,
        coq_checked=False,reachable_inputs_proved=False,global_invariant_synthesized=False)


def check_profile(profile,output,roots=None,timeout=1200):
    output=Path(output)
    if output.exists():raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    ast,residuals,exports,source,count=proposal(profile,roots)
    file=output/'ScalarGuardBindings.v';file.write_text(source)
    report=dict(accepted=False,ast_sha256=ast['source_sha256'],
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        actual_program=profile['ast']['program'],bindings=exports,residuals=residuals,
        audited_exports=count,llm_calls=0,reachable_inputs_proved=False,
        binding_coverage_proved=False,global_invariant_synthesized=False)
    if residuals or not exports:report['status']='unsupported_guard_binding_selection'
    else:
        flags=list(adapter.framework.FLAGS)
        for extra in profile.get('coq_load_paths',[]):flags+=['-R',extra['directory'],extra['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedGuardBindings']
        start=time.monotonic()
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(file.resolve())],output/'coqc.log',timeout)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
        if c.returncode==0:
            report['assumptions_closed']=scalar.audit_output(c.stdout,count)
            start=time.monotonic()
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedGuardBindings.ScalarGuardBindings'],output/'coqchk.log',timeout)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-start)
            report['accepted']=report['assumptions_closed'] and k.returncode==0
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile',type=Path,required=True)
    mode=p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--output',type=Path)
    mode.add_argument('--emit-source',type=Path)
    mode.add_argument('--check-source',type=Path)
    p.add_argument('--roots',type=int,nargs='+');p.add_argument('--timeout',type=float,default=1200)
    a=p.parse_args()
    if not 0<a.timeout<=1200:p.error('timeout must be positive and at most1200 seconds')
    profile=json.loads(a.profile.read_text())
    if a.emit_source or a.check_source:
        print(json.dumps(emit_library(profile,a.emit_source or a.check_source,a.roots,
            check=bool(a.check_source)),indent=2));return 0
    result=check_profile(profile,a.output,a.roots,a.timeout)
    print(json.dumps(result,indent=2));return 0 if result['accepted'] else 1


if __name__=='__main__':raise SystemExit(main())
