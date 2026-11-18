"""Connect a generated continuation dispatcher to the original cycle and ITree.

Structural relation conversion and lower phase continuations remain explicit
reused evidence. Whole old cycle/transfer/bounded-progress proofs are excluded.
"""
import argparse,copy,hashlib,json,re,time
from pathlib import Path
import cpu_continuation_dispatch as compiler
import cpu_local_cycle_compiler as cycles
import cpu_local_progress_compiler as progress
import cpu_local_evidence_catalog as catalog
from cpu_record_evidence import definitions,scoped_commands
from cpu_local_evidence_catalog import declarations
from cpu_relation_projection_graph import type_body,implication_parts,predicate_head
from cpu_joint_synthesis import render as render_joint
from cpu_certificate_acceptance import run_stage

def provider(profile,folder,kernel_recheck=None):
    folder=Path(folder);data,source=compiler.render(profile);report=json.loads((folder/'report.json').read_text())
    path=folder/'Phases.v';obj=path.with_suffix('.vo')
    digest=hashlib.sha256(obj.read_bytes()).hexdigest()
    kernel_ok=report.get('accepted')is True and report.get('coqchk_exit')==0 and report.get('object_sha256')==digest
    receipt_digest=None
    if kernel_recheck is not None:
        receipt_path=Path(kernel_recheck)/'report.json';receipt=json.loads(receipt_path.read_text())
        actual={name:hashlib.sha256((folder/name).read_bytes()).hexdigest()
            for name in ('Phases.v','Phases.vo','plan.json','report.json')}
        expected_command=[str(compiler.a.ROOT/'_opam/bin/coqchk'),'-silent',*compiler.a.framework.FLAGS,
            '-R',str(folder.resolve()),'GeneratedPhases','-norec','GeneratedPhases.Phases']
        kernel_ok=(receipt.get('accepted')is True and receipt.get('coqchk_exit')==0
            and receipt.get('coqchk_timed_out')is False and receipt.get('unchanged')is True
            and receipt.get('recompiled')is False and receipt.get('command')==expected_command
            and receipt.get('hashes_before')==actual and receipt.get('hashes_after')==actual
            and receipt.get('source_sha256')==actual['Phases.v'] and receipt.get('object_sha256')==digest
            and (compiler.a.ROOT/receipt.get('provider','')).resolve()==folder.resolve()
            and 0<receipt.get('coqchk_seconds',0)<=1201 and receipt.get('timeout_seconds')==1200)
        receipt_digest=hashlib.sha256(receipt_path.read_bytes()).hexdigest()
    if not(kernel_ok and report.get('coqc_exit')==0
        and report.get('assumptions_accepted')is True and report.get('original_dispatch_proof_used')is False
        and path.read_text()==source and json.loads((folder/'plan.json').read_text())==data
        and report.get('source_sha256')==hashlib.sha256(source.encode()).hexdigest()):
        raise ValueError('exact checked generated continuation provider required')
    result=dict(source_sha256=report['source_sha256'],object_sha256=digest)
    if receipt_digest:result['independent_kernel_receipt_sha256']=receipt_digest
    return result

def render(profile):
    b=profile['joint_binding']
    if b.get('transfer_mode')!='streaming':raise ValueError('empty-pending cycle interface required')
    data,_=compiler.render(profile);root=data['goal']['owner']
    sources={owner:(compiler.a.ROOT/'src'/Path(*owner.split('.')).with_suffix('.v')).read_text()for owner in data['source_sha256']}
    defs=[dict(owner=owner,**row)for owner,source in sources.items()for row in definitions(source)]
    type_names=[]
    for owner,source in sources.items():
        for scope,command in scoped_commands(source):
            match=re.match(r'(?:Record|Inductive)\s+(\w+)\b',command)
            if match:type_names.append((match[1],owner+'.'+(scope+'.'if scope else'')+match[1]))
    def qualify(head):
        options=[row['owner']+'.'+row['symbol']for row in defs if row['symbol'].split('.')[-1]==head]
        options.extend(symbol for name,symbol in type_names if name==head)
        if len(options)!=1:raise ValueError('unique relation owner required: '+str(head))
        return options[0]
    cycle_data,cycle_source=cycles.render(b);component=cycle_data['component']
    pre=cycles.atoms(implication_parts(type_body(component['statement']))[0])[0].split('.')[-1]
    post_head=component['post_alias']
    wanted={post_head};rows=[];broad=set()
    for row in defs:
        if (chr(92)+'/')in row['command'].split(':=',1)[-1]:broad.add(row['symbol'].split('.')[-1])
    for source in sources.values():
        for _,command in scoped_commands(source):
            m=re.match(r'Inductive\s+(\w+)\b.*?:\s*Prop\s*:=',command,re.S)
            if m and command.count('|')>0:broad.add(m[1])
    frontier={predicate_head(p)for h in data['goal']['handlers']for p in h['parts'][:-1]}-{data['goal']['post_head']}
    continuations=[];iff=[]
    for owner,source in sources.items():
        for row in declarations(source):
            body=type_body(row['statement'])
            if not body:continue
            if owner==root:
                if '<->'in body:
                    left,right=body.split('<->',1)
                    if predicate_head(left)==pre:iff.append(dict(owner=owner,**row))
                continue
            parts=implication_parts(compiler.without_forall(body))
            if not parts:continue
            header=row['statement'][:row['statement'].rfind(body)];result=predicate_head(parts[-1])
            binders={m[1]:m[2]for g in compiler.groups(header)if(m:=re.fullmatch(r'\s*(\w+)\s*:\s*(.*)',g,re.S))}
            if result in binders and binders[result].strip().endswith('Prop')and predicate_head(parts[0])in frontier:
                args=cycles.atoms(parts[0])
                if len(args)<3:raise ValueError('two-state continuation gate required')
                continuations.append(dict(symbol=owner+'.'+row['symbol'],post_parameter=result,
                    gate=' '.join([qualify(args[0].split('.')[-1]),*args[1:-2]])))
            heads=[predicate_head(p)for p in parts[:-1]]
            if any(h in broad for h in heads)or re.search(r'\b(?:OrderedCycleSafety|BoundedProgress|Certificate)\b|eutt|≈',row['statement']):continue
            rows.append(dict(symbol=owner+'.'+row['symbol'],result=result,premises=heads))
    if len(iff)!=1:raise ValueError('unique original component-to-history equivalence required')
    equivalence_args=cycles.atoms(type_body(iff[0]['statement']).split('<->',1)[0])[1:]
    for _ in range(6):
        before=set(wanted)
        for row in rows:
            if row['result']in wanted:
                wanted.update(h for h in row['premises']if h and h.endswith('CyclePost'))
        if wanted==before:break
    else:raise ValueError('cycle-post connection depth exceeded')
    chosen=[row for row in rows if row['result']in wanted]
    if len(chosen)>128 or len(continuations)>16:raise ValueError('cycle component rule budget exceeded')
    original_root=data['goal']['root_head']
    end=implication_parts(compiler.without_forall(type_body(data['goal']['statement'])))[0]
    args=cycles.atoms(end)
    continuations.insert(0,dict(symbol='GeneratedPhases.Phases.checked_dispatch',post_parameter=data['goal']['result_head'],
        gate=' '.join([qualify(args[0].split('.')[-1]),*args[1:-2]])))
    right=iff[0]['statement'].split('<->',1)[1].strip();top=predicate_head(right)
    # Keep the newly proved root atomic: it must be consumed, not re-expanded
    # and silently replaced by another whole-cycle proof search.
    logical={};sums={}
    for row in defs:
        body=row['command'].split(':=',1)[-1].strip()
        if ('/'+chr(92))in body or(chr(92)+'/')in body or body.startswith('exists '):logical.setdefault(row['symbol'].split('.')[-1],[]).append((row,body))
    for owner,source in sources.items():
        for scope,command in scoped_commands(source):
            m=re.match(r'Inductive\s+(\w+)\b.*?:\s*Prop\s*:=',command,re.S)
            if m and command.count('|')>0:sums.setdefault(m[1],[]).append(owner+'.'+(scope+'.'if scope else'')+m[1])
    todo=[top];seen=set();decompose=[]
    while todo:
        head=todo.pop()
        if not head or head in seen or head==original_root or head in frontier:continue
        seen.add(head)
        found=logical.get(head,[])
        if len(found)>1:raise ValueError('ambiguous component structural alias')
        if found:
            row,body=found[0];decompose.append(row['owner']+'.'+row['symbol'])
            todo.extend(t.split('.')[-1]for t in re.findall(r'[A-Za-z_][\w.]*',body))
        if head in sums:
            if len(sums[head])!=1:raise ValueError('ambiguous component sum')
            decompose.extend(sums[head])
    evidence,components,api=catalog.render_components(b,omit_roles=('local_transfer','bounded_progress'))
    _,progress_source=progress.render(b)
    progress_source=progress_source.replace(' GeneratedLocalTransfer.LocalTransfer ',' ')
    progress_source=progress_source.replace('GeneratedLocalTransfer.LocalTransfer.GeneratedLocalCycle.','GeneratedLocalCycle.')
    old='eapply '+component['symbol']
    if cycle_source.count(old)!=1:raise ValueError('unique component consumer application required')
    cycle_source=cycle_source.replace(old,'eapply InferredContinuationCycle.checked_component')
    new=copy.deepcopy(api);new['imports']=list(b['imports'])
    for row in new['proofs'].values():row['symbol']=row['symbol'].replace('GeneratedLocalCatalog.AutoLocalContract.','')
    for role,symbol in [('local_transfer','GeneratedLocalCycle.actual_local_transfer'),('bounded_progress','GeneratedLocalProgress.actual_bounded_progress')]:
        new['proofs'][role]=dict(symbol=symbol,arguments=[dict(binder=name)for name in b['arguments']])
    parameters=' '.join(b['arguments']);groups={}
    for row in chosen:groups.setdefault(row['result'],[]).append(row['symbol'])
    alternatives=[]
    for head,symbols in groups.items():
        alternatives.append('lazymatch goal with|-?G=>let h:=phase_head G in let wanted:=constr:(@'+qualify(head)+')in constr_eq h wanted;first['+
            ' | '.join('solve[eapply '+s+';current_solve '+parameters+' rest]'for s in symbols)+']end')
    for row in continuations:
        alternatives.append('lazymatch goal with|-?P ?o ?isa=>let needed:=constr:('+row['gate']+' o isa)in match goal with _:needed|-_=>idtac end;'+
            'solve[eapply '+row['symbol']+' with('+row['post_parameter']+':=P);current_solve '+parameters+' rest]end')
    unpackers=' | '.join('multimatch goal with H:?T|-_=>let h:=phase_head T in let wanted:=constr:(@'+s+')in constr_eq h wanted;phase_once H end'for s in decompose)or'fail 0'
    opaque=cycle_data['component']['connection_opaque']
    lines=[components,'Require Import GeneratedPhases.Phases.',
        'Import GeneratedPhases.Phases.GeneratedRecordRules.',*[command+'.'for command in data['require_commands']],
        'Import '+' '.join(data['opens']+[root+'.'+data['goal']['symbol'].rsplit('.',1)[0]])+'.',
        *(['Local Opaque '+' '.join(opaque)+'.']if opaque else[]),
        'Module InferredContinuationCycle.',
        'Ltac current_solve '+parameters+' fuel:=first[phase_logic 8%nat|lazymatch fuel with S ?rest=>first[',
        'progress phase_conjunction;current_solve '+parameters+' rest | match goal with|-forall x:_,_=>intro;current_solve '+parameters+' rest end | '+' | '.join(alternatives)+']end].',
        'Ltac current_project rule H fuel:=lazymatch fuel with S ?rest=>let T:=type of rule in lazymatch T with',
        ' |forall x:?A,_=>multimatch goal with argument:A|-_=>let next:=constr:(rule argument)in current_project next H rest end',
        ' |_=>let value:=constr:(proj1 rule H)in fresh_fact value end end.',
        'Ltac current_decompose:=first[match goal with H:or _ _|-_=>phase_once H|H:exists _,_|-_=>phase_once H end | '+unpackers+'].',
        'Ltac current_close '+parameters+' fuel:=lazymatch fuel with O=>phase_dump;fail 1000 "component cycle depth exhausted"|S ?rest=>first[',
        ' solve[current_solve '+parameters+' 32%nat]|progress phase_conjunction;current_close '+parameters+' rest',
        ' |current_decompose;current_close '+parameters+' rest|phase_dump;fail 1000 "component cycle residual"]end.',
        'Lemma actual_component '+component['statement']+'.',
        'Proof. intros. multimatch goal with H:?T|-_=>let h:=phase_head T in let wanted:=constr:(@'+qualify(pre)+')in constr_eq h wanted;',
        ' let value:=constr:(proj1 (@'+root+'.'+iff[0]['symbol']+' '+' '.join(equivalence_args)+') H)in fresh_fact value end.',
        ' current_close '+parameters+' 256%nat. Qed.',
        'Definition checked_component : ltac:(let T:=type of(@'+component['module']+'.'+component['symbol']+')in exact T) := @actual_component.',
        'End InferredContinuationCycle.',cycle_source,progress_source,render_joint(new)]
    return dict(dispatch=data,component=component,continuations=continuations,rules=chosen,
        structural_equivalence=iff[0],decomposition=decompose,current_progress_rebuilt=True,
        old_component_cycle_proof_used=False,old_local_transfer_proof_used=False,
        old_bounded_progress_proof_used=False,local_slots=evidence,
        architecture_startup_initialization_reused=True),'\n'.join(lines)+'\n'

def proposal(profile,output):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:
        data,source=render(profile);(output/'Consumer.v').write_text(source)
        (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
        report=dict(accepted=False,native_started=False,source_generation_succeeded=True,whole_goal_complete=False)
    except ValueError as error:
        report=dict(accepted=False,native_started=False,source_generation_succeeded=False,residual=str(error),whole_goal_complete=False)
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

def check(profile,dispatch_provider,output,timeout=1200,kernel_recheck=None):
    dp=provider(profile,dispatch_provider,kernel_recheck);output=Path(output);output.mkdir(parents=True,exist_ok=False)
    if not 0<timeout<=1200:raise ValueError('native budget must be within 1200 seconds')
    try:data,source=render(profile)
    except ValueError as error:
        report=dict(accepted=False,native_started=False,residual=str(error),whole_goal_complete=False)
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    path=output/'Consumer.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(compiler.a.framework.FLAGS)
    for row in profile.get('coq_load_paths',[]):flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(Path(dispatch_provider).resolve()),'GeneratedPhases','-R',str(output.resolve()),'GeneratedContinuationCycle']
    result=dict(accepted=False,whole_goal_complete=False,llm_calls=0,dispatcher_provider=dp,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),old_component_cycle_proof_used=False,
        old_local_transfer_proof_used=False,old_bounded_progress_proof_used=False)
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(compiler.a.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    result.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        ok,axioms=compiler.pipeline.audit_shared_output(source,c.stdout);result.update(assumptions_accepted=ok,assumptions=axioms)
        if ok and time.monotonic()<deadline:
            ks=time.monotonic();k,t=run_stage([str(compiler.a.ROOT/'_opam/bin/coqchk'),'-silent',*flags,
                '-norec','GeneratedPhases.Phases','-norec','GeneratedContinuationCycle.Consumer'],output/'coqchk.log',deadline-ks)
            result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,accepted=k.returncode==0)
    result['overall_seconds']=time.monotonic()-start
    result['dispatcher_unchanged']=provider(profile,dispatch_provider,kernel_recheck)==dp
    result['accepted']=result['accepted'] and result['dispatcher_unchanged']
    if result['accepted']:result.update(object_sha256=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest(),itree_refinement_proved=True)
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--dispatcher',type=Path);p.add_argument('--kernel-recheck',type=Path)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--plan-only',action='store_true');x=p.parse_args()
    if not x.plan_only and x.dispatcher is None:p.error('--dispatcher is required for native verification')
    profile=json.loads(x.profile.read_text())
    result=proposal(profile,x.output)if x.plan_only else check(profile,x.dispatcher,x.output,kernel_recheck=x.kernel_recheck)
    ok=result.get('source_generation_succeeded')if x.plan_only else result['accepted']
    print(json.dumps(result,indent=2));raise SystemExit(0 if ok else 1)
