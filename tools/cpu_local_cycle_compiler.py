"""Compile cycle-post or actual run1 segment components into original transfers.

This discovers existing lower semantic cycle components, not their proofs or
the invariant itself. It does not select an old LocalStreamingTransfers witness.
"""
from __future__ import annotations
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_arch_projection as architecture
import cpu_relation_projection_graph as graph
from cpu_local_evidence_catalog import declarations
from cpu_record_evidence import definitions
from cpu_certificate_acceptance import render_proof_argument,run_stage


def atoms(expression):
    result=[];depth=0;start=None
    for index,char in enumerate(expression):
        if start is None:
            if char.isspace():continue
            start=index
        if char in '([{':depth+=1
        elif char in ')]}':depth-=1
        if depth<0:raise ValueError('unbalanced application')
        if depth==0 and char.isspace():result.append(expression[start:index]);start=None
    if depth:raise ValueError('unbalanced application')
    if start is not None:result.append(expression[start:])
    return result


def catalog(binding):
    if binding.get('transfer_mode')!='streaming':
        raise ValueError('requires empty-pending cycle streaming; no old-transfer fallback')
    architecture.render(binding);root=architecture.pipeline.adapter.ROOT
    sources={};frontier=list(binding['imports'])
    # Cycle-post aliases may live one level deeper than architecture heads.
    # Bound the dependency traversal explicitly; do not search unrelated files.
    for depth in range(3):
        following=[]
        for module in frontier:
            if module in sources:continue
            path=root/'src'/Path(*module.split('.')).with_suffix('.v')
            if not path.is_file():
                if depth==0:raise ValueError('missing explicit cycle source owner')
                continue
            if len(sources)>=512:raise ValueError('cycle source budget exceeded')
            sources[module]=path.read_text()
            following.extend(graph.dependencies(sources[module]))
        frontier=following
    defs=[dict(module=module,**row)for module,source in sources.items()for row in definitions(source)]
    physical=binding['physical']['symbol'].split('.')[-1]
    candidates=[]
    for module in binding['imports']:
        for row in declarations(sources[module]):
            body=graph.type_body(row['statement']);parts=graph.implication_parts(body)if body else None
            if not parts or len(parts)!=2:continue
            result=parts[-1];head=graph.predicate_head(result)
            aliases=[d for d in defs if d['symbol'].split('.')[-1]==head]if head else []
            if result.startswith('match '):post_body=result;owner=module;post_scope=row['symbol'].rsplit('.',1)[0]
            elif len(aliases)==1:
                alias=aliases[0];post_body=alias['command'].split(':=',1)[-1];owner=alias['module']
                post_scope=alias['symbol'].rsplit('.',1)[0]
            else:continue
            # This exact syntax is an untrusted proposal, not a proof of the
            # observer or state connections. Those must unify and close in Coq.
            if 'VisibleISASteps'not in post_body or 'SilentCycle'not in post_body:continue
            branch=re.search(r'\bSilentCycle\s*=>\s*(.*?)(?:\||\bend\b)',post_body,re.S)
            if not branch:continue
            pre_atoms=atoms(parts[0]);post_atoms=atoms(branch.group(1).strip())
            if not pre_atoms or not post_atoms:continue
            if pre_atoms[0].split('.')[-1]==physical:
                if post_atoms[0].split('.')[-1]!=physical:continue
                pre=post=None;diagonal=True
            else:
                diagonal=False
                if len(pre_atoms)<3 or len(post_atoms)<3:continue
                def close_prefix(items,scope):
                    prefix=items[:-2]
                    if any(not architecture.pipeline.adapter.SYMBOL.fullmatch(t)for t in prefix):
                        raise ValueError('unsupported relation-prefix syntax')
                    if '.'not in prefix[0]:prefix[0]=scope+'.'+prefix[0]
                    if any(t not in binding['arguments']for t in prefix[1:]):
                        raise ValueError('relation parameters are not original global binders')
                    return ' '.join(prefix)
                pre=close_prefix(pre_atoms,row['symbol'].rsplit('.',1)[0])
                post=close_prefix(post_atoms,post_scope)
            connection_opaque=[];connection_owners=[]
            if not diagonal:
                observer=re.match(r'\s*match\s+([A-Za-z_][A-Za-z0-9_.]*)',post_body)
                successor=atoms(post_atoms[-2].strip('()'))
                names={observer.group(1).split('.')[-1]if observer else None,
                       successor[0].split('.')[-1]if successor else None}
                for name in sorted(n for n in names if n):
                    resolved=[d for d in defs if d['symbol'].split('.')[-1]==name]
                    if len(resolved)!=1:raise ValueError('ambiguous cycle connection constant')
                    connection_opaque.append(resolved[0]['symbol'])
                    connection_owners.append(resolved[0]['module'])
            candidates.append(dict(**row,module=module,post_owner=owner,post_scope=post_scope,
                                   pre=pre,post=post,diagonal=diagonal,
                                   connection_opaque=connection_opaque,
                                   connection_owners=connection_owners,
                                   post_alias=head if aliases else None))
    if len(candidates)!=1:raise ValueError('exactly one supported lower cycle-post component required; no old-transfer fallback')
    helpers=[]
    for module,source in sources.items():
        for row in declarations(source):
            if '<->'not in row['statement']:continue
            if re.search(r'\b'+re.escape(physical)+r'\b',row['statement']):continue
            if candidates[0]['pre']and all(re.search(r'\b'+re.escape(term.split('.')[-1])+r'\b',row['statement'])
                                           for term in (candidates[0]['pre'].split()[0],candidates[0]['post'].split()[0])):
                helpers.append(dict(module=module,**row))
    if len(helpers)>16:raise ValueError('cycle relation-conversion budget exceeded')
    return dict(component=candidates[0],helpers=helpers,
                source_sha256={m:hashlib.sha256(s.encode()).hexdigest()for m,s in sources.items()},
                old_local_transfer_witness_used=False,physical_relation_discovered=False)


def render(binding):
    if binding.get('transfer_mode','queue')=='queue':
        from cpu_local_queue_compiler import render as render_queues
        return render_queues(binding)
    if binding.get('transfer_mode')=='boundary_entry':
        from cpu_local_segment_compiler import render as render_segments
        return render_segments(binding)
    data=catalog(binding);candidate=data['component']
    source=architecture.render(binding).split('Module GeneratedArchitecturalProjection.')[0]
    owners={candidate['module'],candidate['post_owner'],*candidate['connection_owners'],*[r['module']for r in data['helpers']]}
    source+='Require Import Ex.External.CPUGeneratedLocalCycle '+' '.join(sorted(owners))+'.\n'
    term=lambda node:render_proof_argument(node,binding['arguments'])
    target,pending,physical=[term(binding[key])for key in ('target','pending','physical')]
    diagonal='(fun s a => ('+physical+') s a a)'
    pre=diagonal if candidate['diagonal']else '('+candidate['pre']+')'
    post=diagonal if candidate['diagonal']else '('+candidate['post']+')'
    conversions=[]
    for helper in data['helpers']:
        for direction in ('proj1','proj2'):
            for arity in range(9):
                application='('+direction+' ('+helper['symbol']+' '+' '.join('_'for _ in range(arity))+'))'
                conversions.append('solve [eapply '+application+';eassumption]')
    logic=['eassumption','reflexivity',*conversions,
           'match goal with H : _ /\\ _ |- _ => destruct H; cycle_logic end',
           'match goal with |- _ /\\ _ => split; cycle_logic end']
    source+='Module GeneratedLocalCycle.\nLtac cycle_logic := first [ '+' | '.join(logic)+' ].\n'
    if candidate['connection_opaque']:
        source+='Local Opaque '+' '.join(candidate['connection_opaque'])+'.\n'
    source+='Theorem actual_local_transfer '+binding['binders']+' :\n'
    source+=' CPUGeneratedJointITree.CPUGeneratedJointITree.LocalStreamingTransfers ('+target+') ('+pending+') ('+physical+').\nProof.\n'
    source+=' eapply (CPUGeneratedLocalCycle.CPUGeneratedLocalCycle.cycle_post_to_streaming ('+target+') ('+pending+') ('+physical+') '+pre+' '+post+').\n'
    source+=' - intro runtime; reflexivity.\n'
    source+=' - intros runtime retired physical_evidence. '+('exact physical_evidence.'if candidate['diagonal']else 'destruct physical_evidence; cycle_logic.')+'\n'
    source+=' - intros runtime retired post_evidence. '+('exact post_evidence.'if candidate['diagonal']else 'split; [reflexivity | cycle_logic].')+'\n'
    source+=' - intros runtime retired component_evidence.\n'
    source+='   unfold CPUGeneratedLocalCycle.CPUGeneratedLocalCycle.CyclePost.\n'
    # The component goal pins the state, observer and successor through the
    # original Target; Coq must check every definitional connection.
    source+='   solve [eapply '+candidate['symbol']+';eassumption].\nQed.\n'
    source+='End GeneratedLocalCycle.\nPrint Assumptions GeneratedLocalCycle.actual_local_transfer.\n'
    return data,source


def check(profile,output,timeout=1200):
    if not 0 < timeout <= 1200:raise ValueError('native shared budget must be in (0,1200] seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(profile['joint_binding'])
    except ValueError as error:
        report=dict(accepted=False,proposal_rejected=str(error),native_check_started=False,llm_calls=0)
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    path=output/'LocalTransfer.v';path.write_text(source)
    (output/'cycle-plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(architecture.pipeline.adapter.framework.FLAGS)
    for row in profile.get('coq_load_paths',[]):flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedLocalTransfer']
    report=dict(accepted=False,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
      old_local_transfer_witness_used=False,physical_relation_discovered=False,
      lower_semantic_cycle_component_reused=True,
      transfer_kind=data.get('transfer_kind','actual_cycle_post'),itree_refinement_proved=False,llm_calls=0)
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(architecture.pipeline.adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        ok,axioms=architecture.pipeline.audit_shared_output(source,c.stdout);report.update(assumptions_accepted=ok,assumptions=axioms)
        if ok and time.monotonic()<deadline:
            ks=time.monotonic();k,t=run_stage([str(architecture.pipeline.adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedLocalTransfer.LocalTransfer'],output/'coqchk.log',deadline-ks)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--timeout',type=float,default=1200,help='shared compile and kernel-check seconds, at most 1200')
    a=p.parse_args()
    report=check(json.loads(a.profile.read_text()),a.output,a.timeout)
    print(json.dumps(report,indent=2));raise SystemExit(0 if report['accepted']else 1)
