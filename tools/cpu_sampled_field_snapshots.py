"""Generate same-sample encoding bundles from actual guarded sequential writes.

Keep actual event separation, writer selection and shared sampled path premises.
Do not chase a combinational mux as an unconditional instruction-word alias.
"""
from __future__ import annotations
import argparse,hashlib,json,time
from pathlib import Path
import cpu_auto_adapter as adapter
import cpu_auto_pipeline as pipeline
import cpu_instruction_fields as fields
import cpu_scalar_expression_paths as paths
from cpu_field_snapshots import validate_provider
from cpu_certificate_acceptance import run_stage

def guard_key(expression,choices):
    guards=[]
    for choice in choices:
        if expression.name!='ECond':raise ValueError('invalid sampled branch path')
        guards.append((adapter.render(expression.args[1]),bool(choice)))
        expression=expression.args[2 if choice else 3]
    return tuple(guards)

def plan(profile):
    ast,residuals,outputs,_,_,selected=fields.proposal(profile)
    if not selected['Sequential']:return ast,dict(groups=[],residuals=residuals)
    expr_ast,remaining,expressions,_,_=paths.expressions.proposal(profile,selected['Sequential'])
    if ast['source_sha256']!=expr_ast['source_sha256']:raise ValueError('AST changed during proposal')
    expressions={row['root']:row for row in expressions};groups={};residuals=[*residuals,*remaining]
    for row in outputs:
        if row['kind']!='Sequential':continue
        expression=expressions.get(row['root'])
        writers=[(i,p)for i,p in enumerate(ast['processes'])if row['root']in p['writers']]
        if not expression or len(writers)!=1 or writers[0][1]['kind']!='Sequential':
            residuals.append(dict(root=row['root'],reason='no unique supported sequential writer'));continue
        index,proc=writers[0]
        if proc['name']!=expression['process']:raise ValueError('sampled expression writer mismatch')
        guards=guard_key(expression['expression'],row['path'])
        key=(row['source'],index,guards)
        group=groups.setdefault(key,dict(source=row['source'],process=proc['name'],
            process_index=index,guards=list(guards),bindings=[]))
        group['bindings'].append(row)
    result=[]
    for index,group in enumerate(groups.values()):
        if len({row['root']for row in group['bindings']})!=len(group['bindings']):
            raise ValueError('ambiguous sampled output binding')
        group['id']=index;result.append(group)
    return ast,dict(groups=result,residuals=residuals)

def render(profile,fields_module='GeneratedInstructionFields.InstructionFields'):
    if not adapter.SYMBOL.fullmatch(fields_module):raise ValueError('closed provider module required')
    ast,data=plan(profile);program=profile['ast']['program']
    imports=[profile['ast']['module'],*profile['ast'].get('program_imports',[]),fields_module]
    lines=['From Coq Require Import List ZArith Bool.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVExpressionPath Ex.External.CPUInstructionFields',
        ' Ex.External.CPUInstructionFieldSnapshot Ex.External.CPUSampledInstructionFields '+' '.join(imports)+'.',
        'Import ListNotations ExtendedSV ExtendedSVExpressionPath CPUInstructionFields CPUInstructionFieldSnapshot CPUSampledInstructionFields.',
        'Module F := '+fields_module+'.']
    for group in data['groups']:
        i=group['id'];bindings=group['bindings'];canonical=bindings[0]
        proc=ast['module']+'.'+group['process']
        vals=[f'(Build_Binding {b["root"]}%nat {b["width"]}%nat {b["field"]})'for b in bindings]
        lines += [f'Definition bindings_{i} : list Binding := ['+';'.join(vals)+'].',
            f'Definition capture_path_{i} s := PathHolds s F.{canonical["original"]} F.{canonical["name"]}_choices.',
            f'Lemma writer_{i}_registered : nth_error(processes {program}) {group["process_index"]}%nat=Some {proc}',
            f' /\\ process_kind {proc}=Sequential.',
            'Proof. split;reflexivity. Qed.']
        for b in bindings:
            lines += [f'Lemma path_{i}_{b["root"]} s : capture_path_{i} s ->',
                f' PathHolds s F.{b["original"]} F.{b["name"]}_choices.',
                'Proof. exact(fun H=>H). Qed.']
        lines += [f'Theorem sampled_{i} ev pre : event_disjointb bindings_{i} ev=true ->',
            f' process_matches_states pre (phase_driven_state {program} ev pre) {proc}=true ->',
            f' capture_path_{i}(phase_driven_state {program} ev pre) ->',
            f' Sampled {program} {group["source"]}%nat bindings_{i} ev pre.',
            f'Proof. intros HE HS HP. unfold Sampled,Decoded,bindings_{i}.']
        for b in bindings:
            value=f'(Build_Binding {b["root"]}%nat {b["width"]}%nat {b["field"]})'
            lines += [f' constructor;[exact(F.{b["name"]}_actual ev pre',
                f'  (checked_event_disjoint bindings_{i} ev {value} HE ltac:(simpl;auto)) HS',
                f'  (path_{i}_{b["root"]} _ HP))|].']
        lines += [' constructor. Qed.',f'Print Assumptions writer_{i}_registered.',f'Print Assumptions sampled_{i}.']
        for b in bindings:lines += [f'Print Assumptions path_{i}_{b["root"]}.']
    return ast,data,'\n'.join(lines)+'\n'

def check(profile,provider,output,analyze_only=False):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    ast,data,source=render(profile)
    result=dict(accepted=False,ast_sha256=ast['source_sha256'],actual_program=profile['ast']['program'],
        **data,proof_started=False,analysis_only=analyze_only,reachable_guards_proved=False,
        current_isa_identity_proved=False,global_invariant_synthesized=False,itree_refinement_proved=False,llm_calls=0)
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    if not data['groups']:result['status']='no_supported_sampled_fields'
    elif not analyze_only:
        result['field_provider']=validate_provider(profile,provider,'fields')
        path=output/'SampledFields.v';path.write_text(source)
        flags=list(adapter.framework.FLAGS)
        for row in profile.get('coq_load_paths',[]):flags+=['-R',row['directory'],row['namespace']]
        flags+=['-R',str(Path(provider).resolve()),'GeneratedInstructionFields',
            '-R',str(output.resolve()),'GeneratedSampledFields']
        result.update(proof_started=True,source_sha256=hashlib.sha256(source.encode()).hexdigest())
        start=time.monotonic();deadline=start+1200
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',1200)
        result.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
        if c.returncode==0:
            ok,axioms=pipeline.audit_shared_output(source,c.stdout);result.update(assumptions_accepted=ok,assumptions=axioms)
            if ok and time.monotonic()<deadline:
                ks=time.monotonic();k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                    'GeneratedSampledFields.SampledFields'],output/'coqchk.log',deadline-ks)
                result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,accepted=k.returncode==0)
        result['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--fields',type=Path);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--analyze-only',action='store_true');a=p.parse_args()
    result=check(json.loads(a.profile.read_text()),a.fields,a.output,a.analyze_only)
    print(json.dumps({k:v for k,v in result.items()if k not in ('groups','residuals')},indent=2))
    raise SystemExit(0 if a.analyze_only or result['accepted']else 1)
