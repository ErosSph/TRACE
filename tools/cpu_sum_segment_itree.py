"""Consume a newly generated sum dispatcher in the original infinite target.

Reconstructs physical post-state packaging, then uses the common actual-run1
segment compiler. Existing architecture/startup/boot and one local cut adapter
are explicit dependencies; old whole segment and ITree proofs are not used.
"""
import argparse,copy,hashlib,json,re,time
from pathlib import Path
import cpu_sum_segment_dispatch as dispatch
import cpu_local_evidence_catalog as catalog
from cpu_record_evidence import definitions,scoped_commands
from cpu_local_evidence_catalog import declarations
from cpu_relation_projection_graph import type_body,implication_parts,predicate_head
from cpu_certificate_acceptance import render_proof_argument,run_stage
from cpu_joint_synthesis import render as render_joint

def kernel_command(flags):
    # -norec takes exactly ONE library argument, not the remaining list.
    return [str(dispatch.a.ROOT/'_opam/bin/coqchk'),'-silent',*flags,
        '-norec','GeneratedSegments.Segments','-norec','GeneratedSegmentConsumer.Consumer']

def unparen(text):
    text=text.strip()
    while text.startswith('(')and text.endswith(')'):
        depth=0
        for index,char in enumerate(text):
            if char=='(':depth+=1
            elif char==')':depth-=1
            if depth==0:break
        if index!=len(text)-1:break
        text=text[1:-1].strip()
    return text

def leading_relation_heads(body):
    parts=[];depth=0;start=0;index=0;separator='/'+chr(92)
    while index<len(body):
        char=body[index]
        if char in '([{':depth+=1
        elif char in ')]}':depth-=1
        elif depth==0 and body.startswith(separator,index):
            parts.append(body[start:index].strip());start=index+2;index+=1
        index+=1
    parts.append(body[start:].strip());heads=set()
    for part in parts:
        if part.startswith(('exists ','forall ')):break
        head=predicate_head(part)
        if head:heads.add(head)
    return heads

def provider(profile,directory):
    directory=Path(directory);data,source=dispatch.render(profile)
    report=json.loads((directory/'report.json').read_text())
    path=directory/'Segments.v';obj=path.with_suffix('.vo')
    if not(report.get('accepted')is True and report.get('coqc_exit')==report.get('coqchk_exit')==0
           and report.get('assumptions_accepted')is True
           and report.get('original_dispatch_proof_used')is False
           and report.get('whole_current_preservation_used')is False
           and path.read_text()==source and report.get('source_sha256')==hashlib.sha256(source.encode()).hexdigest()
           and json.loads((directory/'plan.json').read_text())==data and obj.is_file()):
        raise ValueError('exact checked current sum-dispatch provider required')
    digest=hashlib.sha256(obj.read_bytes()).hexdigest()
    if report.get('object_sha256',digest)!=digest:raise ValueError('sum-dispatch object changed')
    return dict(source_sha256=report['source_sha256'],object_sha256=digest)

def render(profile):
    b=profile['joint_binding']
    if b.get('transfer_mode')!='boundary_entry':raise ValueError('actual boundary-entry interface required')
    data,_=dispatch.render(profile);sources={name:(dispatch.a.ROOT/'src'/Path(*name.split('.')).with_suffix('.v')).read_text()
        for name in data['source_sha256']}
    owner=data['goal']['owner'];root=sources[owner];physical=b['physical']['symbol'];physical_name=physical.split('.')[-1]
    goals=[row for row in declarations(root)if all(word in row['statement']for word in('FirstVisibleCycle','FormalSpec.run1',physical_name,'exists'))
        and not any(word in row['statement']for word in('StreamingTransfer','eutt','≈'))]
    if len(goals)!=1:raise ValueError('unique original physical-segment interface required')
    defs=[dict(owner=name,**row)for name,source in sources.items()for row in definitions(source)]
    physical_defs=[row for row in defs if row['owner']==owner and row['symbol']==physical]
    if len(physical_defs)!=1:raise ValueError('explicit original physical definition required')
    body=physical_defs[0]['command'].split(':=',1)[-1]
    heads=leading_relation_heads(body)
    reach=[]
    for name,source in sources.items():
        for scope,command in scoped_commands(source):
            match=re.match(r'Inductive\s+(\w+)\b',command)
            if match and match[1]in heads:reach.append(name+'.'+(scope+'.'if scope else'')+match[1])
    if len(reach)!=1:raise ValueError('unique top-level ISA reachability component required')
    binder_tokens={token.split('.')[-1]for token in re.findall(r'[A-Za-z_][\w.]*',b['binders'])}
    domains=[row['owner']+'.'+row['symbol']for row in defs if row['symbol'].split('.')[-1]in binder_tokens
        and reach[0].split('.')[-1]in row['command']]
    if len(domains)!=1:raise ValueError('unique ISA-only program closure definition required')
    parts=implication_parts(type_body(data['goal']['statement']))
    closures=[row for row in defs if dispatch.compact(unparen(row['command'].split(':=',1)[-1]))==dispatch.compact(unparen(parts[-2]))]
    if len(closures)!=1:raise ValueError('unique exact successor closure alias required')
    closure=closures[0]['owner']+'.'+closures[0]['symbol']
    sum_name=data['sum_symbol'].split('.')[-1];restorers=[]
    for row in declarations(root):
        p=implication_parts(type_body(row['statement'])or'')
        if p and len(p)==2 and predicate_head(p[-1])==sum_name:restorers.append(owner+'.'+row['symbol'])
    if len(restorers)!=1:raise ValueError('unique structural successor-cut adapter required')
    evidence,components,api=catalog.render_components(b,omit_roles=('local_transfer',))
    # These four slots are discovered by their original API types. No old
    # local-transfer witness is available in this partial catalog.
    new=copy.deepcopy(api);new['imports']=list(b['imports'])
    for row in new['proofs'].values():row['symbol']=row['symbol'].replace('GeneratedLocalCatalog.AutoLocalContract.','')
    new['proofs']['local_transfer']=dict(symbol='InferredSegmentConsumer.actual_local_transfer',
        arguments=[dict(binder=name)for name in b['arguments']])
    term=lambda key:render_proof_argument(b[key],b['arguments'])
    target,pending,phys=[term(key)for key in('target','pending','physical')]
    physical_goal=goals[0]
    lines=[components,
        'Require Import GeneratedSegments.Segments Ex.External.CPUGeneratedLocalSegment.',
        *[command+'.'for command in data['require_commands']],
        'Import '+' '.join(data['opens']+[owner+'.'+data['goal']['symbol'].rsplit('.',1)[0]])+'.',
        'Create HintDb segment_post.',
        '#[local] Hint Constructors '+reach[0]+' : segment_post.',
        '#[local] Hint Resolve '+restorers[0]+' : segment_post.',
        'Module InferredSegmentConsumer.',
        'Ltac unpack:=repeat first[match goal with H:_/\\_|-_=>destruct H end|match goal with H:exists _,_|-_=>destruct H end].',
        'Ltac pack:=first[eassumption|reflexivity|match goal with|-_/\\_=>split;pack| |-exists _,_=>eexists;pack end|solve[eauto 4 with segment_post nocore]].',
        'Ltac instantiate term use fuel:=lazymatch fuel with O=>fail 0 "application depth"| S ?rest=>',
        ' let T:=type of term in lazymatch T with',
        ' |forall x:?A,_=>first[multimatch goal with argument:A|-_=>let next:=constr:(term argument)in instantiate next use rest end',
        ' |let argument:=constr:(ltac:(eassumption):A)in let next:=constr:(term argument)in instantiate next use rest]',
        ' |_=>tryif has_evar term then fail 0 "open application"else use term end end.',
        'Ltac establish T:=let H:=fresh "successor_closed"in assert(T)as H by(unfold '+closure+';intros;unfold '+' '.join(domains)+' in *;eauto 4 with segment_post nocore).',
        'Ltac closure_type term fuel:=let T:=type of term in lazymatch T with',
        ' |forall x:?A,_=>lazymatch fuel with S ?rest=>multimatch goal with argument:A|-_=>let next:=constr:(term argument)in closure_type next rest end end',
        ' |Prop=>establish term end.',
        'Lemma actual_physical_segments '+physical_goal['statement']+'.',
        'Proof. intros. unfold '+physical+' in *. unpack.',
        ' repeat match goal with H:?x = ?v|-_=>is_var x;subst x end.',
        ' closure_type constr:(@'+closure+') 16%nat.',
        ' let use term:=let H:=fresh "new_segment"in pose proof term as H in',
        ' instantiate constr:(@GeneratedSegments.Segments.checked_segments) use 24%nat.',
        ' unpack. pack. Qed.',
        'Definition checked_physical_segments : ltac:(let T:=type of(@'+owner+'.'+physical_goal['symbol']+')in exact T) := @actual_physical_segments.',
        'Theorem actual_local_transfer '+b['binders']+' : CPUGeneratedBoundary.CPUGeneratedBoundary.LocalSegmentStreamingTransfers ('+target+') ('+pending+') ('+phys+').',
        'Proof. eapply(CPUGeneratedLocalSegment.CPUGeneratedLocalSegment.run1_segments_to_streaming ('+target+') ('+pending+') ('+phys+')).',
        ' - intro runtime;reflexivity.',
        ' - intros runtime retired Hphysical.',
        '   let use term:=let H:=fresh "physical_segment"in pose proof term as H in',
        '   instantiate constr:(@checked_physical_segments) use 24%nat.',
        '   unpack. pack.',
        'Qed. End InferredSegmentConsumer.',
        render_joint(new)]
    return dict(dispatch=data,physical_goal=physical_goal,reachability=reach[0],domain_definitions=domains,
        successor_cut_adapter=restorers[0],local_catalog=evidence,
        old_physical_segment_proof_used=False,old_local_transfer_proof_used=False,
        architecture_startup_boot_reused=True,physical_relation_discovered=False),'\n'.join(lines)+'\n'

def check(profile,dispatch_provider,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be within 1200 seconds')
    dp=provider(profile,dispatch_provider);output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(profile)
    except ValueError as error:
        report=dict(accepted=False,native_started=False,residual=str(error),whole_goal_complete=False)
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    path=output/'Consumer.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(dispatch.a.framework.FLAGS)
    for row in profile.get('coq_load_paths',[]):flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(Path(dispatch_provider).resolve()),'GeneratedSegments','-R',str(output.resolve()),'GeneratedSegmentConsumer']
    report=dict(accepted=False,whole_goal_complete=False,llm_calls=0,dispatcher_provider=dp,
        old_dispatch_proof_used=False,old_physical_segment_proof_used=False,
        old_local_transfer_proof_used=False,architecture_startup_boot_reused=True,
        source_sha256=hashlib.sha256(source.encode()).hexdigest())
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(dispatch.a.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        ok,axioms=dispatch.pipeline.audit_shared_output(source,c.stdout);report.update(assumptions_accepted=ok,assumptions=axioms)
        if ok and time.monotonic()<deadline:
            ks=time.monotonic();k,t=run_stage(kernel_command(flags),output/'coqchk.log',deadline-ks)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,accepted=k.returncode==0)
    if hashlib.sha256((Path(dispatch_provider)/'Segments.vo').read_bytes()).hexdigest()!=dp['object_sha256']:
        report.update(accepted=False,residual='dispatcher object changed during check')
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:report.update(object_sha256=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest(),itree_refinement_proved=True)
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

def checked_consumer(profile,dispatch_provider,output):
    """Read back the exact current source and both independently checked objects."""
    dp=provider(profile,dispatch_provider);output=Path(output);data,source=render(profile)
    report=json.loads((output/'report.json').read_text());path=output/'Consumer.v'
    if not(report.get('accepted')is True and report.get('itree_refinement_proved')is True
           and report.get('coqc_exit')==report.get('coqchk_exit')==0
           and report.get('assumptions_accepted')is True
           and report.get('old_dispatch_proof_used')is False
           and report.get('old_physical_segment_proof_used')is False
           and report.get('old_local_transfer_proof_used')is False
           and path.read_text()==source and json.loads((output/'plan.json').read_text())==data
           and report.get('source_sha256')==hashlib.sha256(source.encode()).hexdigest()
           and report.get('object_sha256')==hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
           and report.get('dispatcher_provider')==dp):
        raise ValueError('exact checked current ITree consumer with frozen dispatcher required')
    return dict(accepted=True,whole_goal_complete=False,design=profile.get('design','profile'),
        itree_refinement_proved=True,dispatcher_provider=dp,object_sha256=report['object_sha256'],
        source_sha256=report['source_sha256'],architecture_startup_boot_reused=True,
        all_unknown_cpu_obligations_generated=False)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--dispatcher',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--verify-only',action='store_true');x=p.parse_args()
    function=checked_consumer if x.verify_only else check
    result=function(json.loads(x.profile.read_text()),x.dispatcher,x.output);print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
