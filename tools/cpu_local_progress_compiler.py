"""Rebuild bounded progress with the current generated cycle safety.

Ranks and their bounds remain checked lower semantic evidence, not invented
by this compiler. It never selects an old bounded-progress or safety wrapper.
"""
from __future__ import annotations
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_arch_projection as architecture
import cpu_local_cycle_compiler as cycle
import cpu_relation_projection_graph as graph
from cpu_local_evidence_catalog import declarations
from cpu_record_evidence import definitions
from cpu_certificate_acceptance import render_proof_argument,run_stage


def catalog(binding):
    if binding.get('transfer_mode','queue') not in ('queue','streaming'):
        raise ValueError('segment mode has its own first-visible progress; no rank fallback')
    architecture.render(binding)
    root=architecture.pipeline.adapter.ROOT;sources={};frontier=list(binding['imports'])
    for depth in range(3):
        following=[]
        for module in frontier:
            if module in sources:continue
            path=root/'src'/Path(*module.split('.')).with_suffix('.v')
            if not path.is_file():
                if depth==0:raise ValueError('missing explicit progress source owner')
                continue
            if len(sources)>=512:raise ValueError('progress source budget exceeded')
            sources[module]=path.read_text();following.extend(graph.dependencies(sources[module]))
        frontier=following
    decreases=[];bounds=[]
    computed_ranks={row['symbol'].split('.')[-1]for source in sources.values()
        for row in definitions(source)if re.search(r'\b(?:search_rank|first_commit)\b',row['command'])}
    for module,source in sources.items():
        for row in declarations(source):
            body=graph.type_body(row['statement'])
            if not body:continue
            if re.match(r'\s*OrderedWaitDecreases\b',body):
                rank=cycle.atoms(body)[-1]
                rank_names={name.split('.')[-1]for name in re.findall(r'[A-Za-z_][A-Za-z0-9_.]*',rank)}
                if not rank_names&computed_ranks:
                    decreases.append(dict(module=module,rank_names=sorted(rank_names),**row))
            # The full rank expression is deliberately not reconstructed from
            # strings; Coq matches the actual bound to the selected rank.
            if '<=' in body and 'BoundedProgress'not in body:
                bounds.append(dict(module=module,**row))
    # Prefer owners explicitly requested by the binding, never a CPU name.
    direct=[r for r in decreases if r['module']in binding['imports']]
    if len(direct)!=1:raise ValueError('exactly one direct lower decrease proof required')
    rank_names=set(direct[0]['rank_names'])-{'fun','_','s','o',*binding['arguments']}
    bounds=[r for r in bounds if any(re.search(r'\b'+re.escape(name)+r'\b',r['statement'])
        for name in rank_names)]
    if not bounds or len(bounds)>32:raise ValueError('bounded rank evidence missing or ambiguous')
    return dict(decrease=direct[0],bounds=bounds,
        source_sha256={m:hashlib.sha256(s.encode()).hexdigest()for m,s in sources.items()},
        rank_discovered=False,old_bounded_progress_witness_used=False)


def render(binding):
    data=catalog(binding);source=architecture.render(binding).split('Module GeneratedArchitecturalProjection.')[0]
    owners=sorted({data['decrease']['module'],*[r['module']for r in data['bounds']]})
    source+='Require Import Ex.External.CPUGeneratedLocalProgress GeneratedLocalTransfer.LocalTransfer '+' '.join(owners)+'.\n'
    term=lambda n:render_proof_argument(n,binding['arguments'])
    target,pending,physical=[term(binding[k])for k in ('target','pending','physical')]
    scope='CPUGeneratedJointITree.CPUGeneratedJointITree'
    joint=f'({scope}.GeneratedJoint ({target}) ({pending}) ({physical}))'
    step=f'(CPUDesignTarget.CPUDesignTarget.target_cycle ({target}))'
    observe=f'(CPUDesignTarget.CPUDesignTarget.target_commits ({target}))'
    fuel=binding['search_fuel'];args=binding['arguments']
    transfer='(GeneratedLocalTransfer.LocalTransfer.GeneratedLocalCycle.actual_local_transfer '+' '.join(args)+')'
    safety='generated_ordered_cycle_safety'if binding.get('transfer_mode','queue')=='queue'else'generated_streaming_cycle_safety'
    safe=f'({scope}.{safety} ({target}) ({pending}) ({physical}) {transfer})'
    source+='Module GeneratedLocalProgress.\nTheorem actual_bounded_progress '+binding['binders']+' :\n'
    source+=f' CPUGeneratedProgress.CPUGeneratedProgress.BoundedProgress {step} {observe} {fuel} {joint}.\nProof.\n'
    alternatives=[]
    for count in range(len(args)+1):
        application='('+data['decrease']['symbol']+' '+' '.join(args[:count])+')'
        bounds=' | '.join('solve [eapply '+r['symbol']+']'for r in data['bounds'])
        alternatives.append('let HD := constr:('+application+') in let signature := type of HD in '
          'lazymatch signature with\n'
          ' | CV32E40PTwoCommitITreeInterface.CV32E40PTwoCommitITreeInterface.OrderedWaitDecreases ?st ?ob ?rel ?rank =>\n'
          f' refine (CPUGeneratedLocalProgress.CPUGeneratedLocalProgress.bounded_from_current_safety {step} {observe} {joint} {fuel} rank _ HD _);\n'
          ' [ exact '+safe+' | intros runtime isa Hjoint; first [ '+bounds+' ] ]\n end')
    source+=' first [ '+' | '.join(alternatives)+' ].\nQed.\nEnd GeneratedLocalProgress.\n'
    source+='Print Assumptions GeneratedLocalProgress.actual_bounded_progress.\n'
    return data,source


def checked_provider(binding,directory,current_transfer):
    """Fail closed before ITree compilation on stale or mismatched providers."""
    directory=Path(directory);report=json.loads((directory/'report.json').read_text())
    data,expected=render(binding);source=directory/'LocalProgress.v'
    plan=json.loads((directory/'progress-plan.json').read_text())
    if not(report.get('accepted')is True and report.get('old_bounded_progress_witness_used')is False
        and report.get('coqchk_exit')==0 and report.get('assumptions_accepted')is True
        and source.read_text()==expected
        and report['source_sha256']==hashlib.sha256(expected.encode()).hexdigest()
        and report['current_local_transfer_source_sha256']==current_transfer['source_sha256']
        and report['current_local_transfer_object_sha256']==current_transfer['object_sha256']
        and plan.get('source_sha256')==data['source_sha256']
        and source.with_suffix('.vo').is_file()):
        raise ValueError('exact checked progress with matching current local-transfer object and source owners required')
    return dict(source_sha256=report['source_sha256'],
        object_sha256=hashlib.sha256(source.with_suffix('.vo').read_bytes()).hexdigest(),
        old_bounded_progress_witness_used=False,rank_discovered=False)


def check(profile,transfer,output):
    binding=profile['joint_binding'];output=Path(output);output.mkdir(parents=True,exist_ok=False)
    transfer=Path(transfer);report=json.loads((transfer/'report.json').read_text())
    _,expected=cycle.render(binding);path=transfer/'LocalTransfer.v'
    if not(report.get('accepted')is True and report.get('old_local_transfer_witness_used')is False
      and report.get('coqchk_exit')==0 and report.get('assumptions_accepted')is True
      and path.read_text()==expected and path.with_suffix('.vo').is_file()
      and report['source_sha256']==hashlib.sha256(expected.encode()).hexdigest()):
        raise ValueError('exact checked current local-transfer provider required')
    data,source=render(binding);sourcepath=output/'LocalProgress.v';sourcepath.write_text(source)
    (output/'progress-plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(architecture.pipeline.adapter.framework.FLAGS)
    for row in profile.get('coq_load_paths',[]):flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(transfer.resolve()),'GeneratedLocalTransfer','-R',str(output.resolve()),'GeneratedLocalProgress']
    result=dict(accepted=False,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
      current_local_transfer_source_sha256=report['source_sha256'],
      current_local_transfer_object_sha256=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest(),
      old_bounded_progress_witness_used=False,rank_discovered=False,
      itree_refinement_proved=False,llm_calls=0)
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(architecture.pipeline.adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(sourcepath.resolve())],output/'coqc.log',1200)
    result.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        ok,axioms=architecture.pipeline.audit_shared_output(source,c.stdout);result.update(assumptions_accepted=ok,assumptions=axioms)
        if ok and time.monotonic()<deadline:
            ks=time.monotonic();k,t=run_stage([str(architecture.pipeline.adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedLocalProgress.LocalProgress'],output/'coqchk.log',deadline-ks)
            result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,accepted=k.returncode==0)
    result['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--local-transfer',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    result=check(json.loads(a.profile.read_text()),a.local_transfer,a.output)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
