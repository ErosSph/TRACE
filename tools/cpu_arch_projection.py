"""Synthesize a structural Physical -> architectural relation proof.

No old architecture witness is used. The initial conservative strategy only
destructs the supplied physical evidence and assembles logical conjunctions.
Unknown operands, reachability, history or temporal facts are not invented.
"""
from __future__ import annotations
import argparse,copy,hashlib,json,time,re
from pathlib import Path
import cpu_auto_pipeline as pipeline
from cpu_certificate_acceptance import render_proof_argument,run_stage
from cpu_joint_synthesis import render as validate_header,PROOFS,BOUNDARY_PROOFS
from cpu_local_evidence_catalog import commands,declarations


def projection_helpers(binding):
    """Untrusted head-directed lookup, excluding whole Physical implications."""
    sources={};owners={}
    for module in binding['imports']:
        path=pipeline.adapter.ROOT/'src'/Path(*module.split('.')).with_suffix('.v')
        if not path.is_file():raise ValueError('projection helper needs an explicit project source owner')
        sources[path]=path.read_text();owners[str(path.relative_to(pipeline.adapter.ROOT))]=hashlib.sha256(path.read_bytes()).hexdigest()
    target=binding['target']['symbol'].split('.')[-1];heads=set()
    for source in sources.values():
        for command in commands(source):
            if not re.match(r'Definition\s+'+re.escape(target)+r'\b',command):continue
            field=re.search(r'\btarget_arch_relation\s*:=\s*([A-Za-z_][A-Za-z0-9_.]*)',command)
            if field and field.group(1) not in ('fun','match') and field.group(1).split('.')[-1]!='target_arch_relation':
                heads.add(field.group(1))
    if len(heads)>1:raise ValueError('ambiguous target relation head')
    if not heads:return dict(relation_head=None,candidates=[],source_sha256=owners)
    head=next(iter(heads));physical=binding['physical']['symbol'].split('.')[-1];candidates=[]
    def term_head(text):
        match=re.match(r'\s*([A-Za-z_][A-Za-z0-9_.]*)\b',text)
        return match.group(1)if match else None
    for path,source in sources.items():
        for row in declarations(source):
            statement=row['statement']
            if re.search(r'\b'+re.escape(physical)+r'\b',statement):continue
            tail=statement.rsplit('->',1)[-1]
            if '<->'in statement:
                # rsplit on -> also splits <->; use the explicit iff separately.
                left,right=statement.rsplit('<->',1)
                left=left.rsplit(':',1)[-1]
                direction='proj1'if term_head(right)==head else('proj2'if term_head(left)==head else None)
            else:direction='direct'if '->'in statement and term_head(tail)==head else None
            if direction:candidates.append(dict(symbol=row['symbol'],direction=direction,source=str(path.relative_to(pipeline.adapter.ROOT))))
    if len(candidates)>16:raise ValueError('projection helper budget exceeded; no silent truncation')
    return dict(relation_head=head,candidates=candidates,source_sha256=owners)


def render(binding,use_projection_helpers=False):
    if type(use_projection_helpers)is not bool:raise ValueError('projection helper switch must be boolean')
    normalized=copy.deepcopy(binding)
    required=BOUNDARY_PROOFS if binding.get('transfer_mode')=='boundary_entry' else PROOFS
    for key in ('proofs','proof_candidates','lemma_candidates'):normalized.pop(key,None)
    normalized['proofs']={role:{'symbol':'eq_refl'}for role in required}
    # Reuse header validation only; do not retain the dummy certificate/body.
    source=validate_header(normalized).split('Module GeneratedJointContract.')[0]
    term=lambda node:render_proof_argument(node,binding['arguments'])
    target,physical=[term(binding[key])for key in ('target','physical')]
    used=set(binding['arguments']);names=[]
    for base in ('runtime','retired','frontier','physical_evidence'):
        name=base
        while name in used:
            name += '_'
        names.append(name);used.add(name)
    s,a,f,h=names
    helper_lines=[]
    if use_projection_helpers:
        candidates=projection_helpers(binding)['candidates'];branches=[]
        for candidate in candidates:
            symbol=candidate['symbol'];direction=candidate['direction']
            applications=[symbol]if direction=='direct'else[
                '('+direction+' ('+symbol+' '+' '.join('_'for _ in range(arity))+'))'for arity in range(9)]
            for application in applications:
                branches.append('match goal with |- ?G => let witness := fresh "auto_projection" in '
                    'assert (witness : G) by (solve [ eapply '+application+'; eassumption ]); '
                    'idtac "ARCH_PROJECTION_HELPER_USED" "'+symbol+'"; exact witness end')
        if branches:helper_lines=[' all: first [ '+' | '.join(branches)+' | idtac ].']
    source+='\n'.join([
        'Module GeneratedArchitecturalProjection.',
        'Theorem structural_architecture '+binding['binders']+' :',
        f' forall {s} {a} {f}, ({physical}) {s} {a} {f} ->',
        f' CPUDesignTarget.CPUDesignTarget.target_arch_relation ({target}) {s} {a}.',
        'Proof.',f' intros {s} {a} {f} {h}.',
        f' destruct {h}.',
        ' repeat first [ assumption | split ].',
        *helper_lines,
        ' all: match goal with |- ?G => idtac "ARCH_PROJECTION_RESIDUAL" G end.',
        'Qed.',
        'End GeneratedArchitecturalProjection.',
        'Print Assumptions GeneratedArchitecturalProjection.structural_architecture.', ''])
    return source


def check(profile,output,timeout=1200,use_projection_helpers=False):
    output=Path(output);source=render(profile['joint_binding'],use_projection_helpers);output.mkdir(parents=True,exist_ok=False)
    path=output/'ArchitecturalProjection.v';path.write_text(source)
    flags=list(pipeline.adapter.framework.FLAGS)
    for item in profile.get('coq_load_paths',[]):flags+=['-R',item['directory'],item['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedArchitecturalProjection']
    report=dict(accepted=False,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                old_architecture_witness_used=False,manual_role_map_read=False,llm_calls=0,
                physical_relation_discovered=False,itree_refinement_proved=False,
                inference_kind='record_projection_and_conjunction_construction',
                projection_helpers_enabled=use_projection_helpers)
    if use_projection_helpers:
        report['helper_catalog']=projection_helpers(profile['joint_binding'])
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(pipeline.adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],
                  output/'coqc.log',timeout)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        ok,axioms=pipeline.audit_shared_output(source,c.stdout)
        report.update(assumptions_accepted=ok,assumptions=axioms)
        remaining=deadline-time.monotonic()
        if ok and remaining>0:
            ks=time.monotonic()
            k,t=run_stage([str(pipeline.adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedArchitecturalProjection.ArchitecturalProjection'],output/'coqchk.log',remaining)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,
                          accepted=k.returncode==0)
    report['structural_architecture_proved']=report['accepted']
    report['residual_goals_observed']='ARCH_PROJECTION_RESIDUAL'in c.stdout
    report['existing_lower_projection_helper_used']='ARCH_PROJECTION_HELPER_USED'in c.stdout
    report['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--projection-helpers',action='store_true');a=p.parse_args()
    result=check(json.loads(a.profile.read_text()),a.output,use_projection_helpers=a.projection_helpers)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted'] else 1)
