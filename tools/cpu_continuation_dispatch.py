"""Generate structural phase dispatch from a continuation interface.

Only declaration types, logical aliases and constructor headers are used.
Leaf phase preservation is reused; the old whole dispatcher is excluded.
"""
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_auto_adapter as a
import cpu_auto_pipeline as pipeline
from cpu_certificate_acceptance import run_stage
from cpu_local_evidence_catalog import declarations
from cpu_record_evidence import definitions,scoped_commands,COQ_RULES
from cpu_relation_projection_graph import dependencies,type_body,implication_parts,predicate_head

def groups(header):
    depth=0;start=None
    for index,char in enumerate(header):
        if char=='(':
            if depth==0:start=index+1
            depth+=1
        elif char==')':
            depth-=1
            if depth==0:yield header[start:index]

def without_forall(body):
    body=body.strip()
    if not body.startswith('forall '):return body
    depth=0
    for index,char in enumerate(body):
        if char in '([{':depth+=1
        elif char in ')]}':depth-=1
        elif char==','and depth==0:return body[index+1:].strip()
    raise ValueError('explicit forall separator required')

def plan(profile):
    b=profile['joint_binding'];sources={};roots=[]
    for value in b.get('coq_sources',[]):
        path=(a.ROOT/value).resolve()
        if not path.is_relative_to(a.ROOT/'src')or path.suffix!='.v':raise ValueError('project semantic source required')
        owner='.'.join(path.relative_to(a.ROOT/'src').with_suffix('').parts)
        sources[owner]=path.read_text();roots.append(owner)
    goals=[]
    for owner in roots:
        for row in declarations(sources[owner]):
            body=type_body(row['statement'])
            if not body:continue
            parts=implication_parts(without_forall(body))
            if not parts:continue
            result=predicate_head(parts[-1]);header=row['statement'][:row['statement'].rfind(body)]
            binders={match[1]:match[2]for g in groups(header)if(match:=re.fullmatch(r'\s*(\w+)\s*:\s*(.*)',g,re.S))}
            if result not in binders or not binders[result].strip().endswith('Prop'):continue
            handlers=[]
            for name,typ in binders.items():
                p=implication_parts(without_forall(typ))
                if p and predicate_head(p[-1])==result:handlers.append(dict(name=name,parts=p))
            inject=[row for row in handlers if len(row['parts'])==2]
            if len(handlers)>1 and len(inject)==1:
                goals.append(dict(owner=owner,**row,result_head=result,root_head=predicate_head(parts[0]),
                    handlers=handlers,post_head=predicate_head(inject[0]['parts'][0])))
    if len(goals)!=1:raise ValueError('unique continuation phase-dispatch interface required')
    goal=goals[0]
    requested=set(dependencies(sources[goal['owner']]))
    parent=goal['owner'].rsplit('.',1)[0]
    for _,command in scoped_commands(sources[goal['owner']]):
        match=re.fullmatch(r'Import\s+(.+)',command,re.S)
        if match:requested.update(parent+'.'+name.split('.')[0]for name in match[1].split())
    for dep in sorted(requested):
        if dep in sources:continue
        path=a.ROOT/'src'/Path(*dep.split('.')).with_suffix('.v')
        if not path.is_file():continue
        if len(sources)>=512:raise ValueError('phase source budget exceeded')
        sources[dep]=path.read_text()
    defs=[dict(owner=owner,**row)for owner,source in sources.items()for row in definitions(source)]
    logical={};sums={};sum_commands={};broad=set()
    for row in defs:
        body=row['command'].split(':=',1)[-1].strip()
        if ('/'+chr(92))in body or (chr(92)+'/')in body or body.startswith('exists '):
            logical.setdefault(row['symbol'].split('.')[-1],[]).append(dict(**row,body=body))
            if (chr(92)+'/')in body:broad.add(row['symbol'].split('.')[-1])
    for owner,source in sources.items():
        for scope,command in scoped_commands(source):
            match=re.match(r'Inductive\s+(\w+)\b.*?:\s*Prop\s*:=',command,re.S)
            if match and command.count('|')>0:
                sums.setdefault(match[1],[]).append(owner+'.'+(scope+'.'if scope else'')+match[1])
                sum_commands.setdefault(match[1],[]).append(command)
    # Only sums that classify the outer invariant are whole dispatchers.
    # An atomic constructor field can itself be an inductive phase contract;
    # its lower preservation theorem is a legitimate reusable component.
    handler_heads={predicate_head(p)for h in goal['handlers']for p in h['parts'][:-1]}-{goal['post_head']}
    classification_todo=[goal['root_head']];classification_seen=set()
    while classification_todo:
        head=classification_todo.pop()
        if not head or head in classification_seen or head in handler_heads:continue
        classification_seen.add(head)
        if head in sums and any(re.search(r'\b'+re.escape(dependency)+r'\b',command)
            for dependency in handler_heads if dependency for command in sum_commands[head]):broad.add(head)
        found=logical.get(head,[])
        if len(found)>1:raise ValueError('ambiguous structural phase alias')
        if found:classification_todo.extend(t.split('.')[-1]for t in re.findall(r'[A-Za-z_][\w.]*',found[0]['body']))
    rows=[];excluded=[]
    for owner,source in sources.items():
        for row in declarations(source):
            symbol=owner+'.'+row['symbol'];text=row['statement'];body=type_body(text)
            parts=implication_parts(without_forall(body))if body else None
            if not parts:continue
            heads=[predicate_head(p)for p in parts[:-1]];result=predicate_head(parts[-1])
            if (owner==goal['owner']or goal['root_head']in heads or any(head in broad for head in heads)
                    or re.search(r'\b(?:Physical|OrderedCycleSafety|OrderedWaitDecreases|BoundedProgress|Certificate)\b|eutt|≈',text)):
                excluded.append(symbol);continue
            rows.append(dict(symbol=symbol,result=result,premises=heads,statement=text))
    wanted={goal['post_head']};chosen={}
    for _ in range(5):
        before=set(wanted)
        for row in rows:
            if row['result']not in wanted:continue
            chosen[row['symbol']]=row
            for head in row['premises']:
                if head and head.endswith('CyclePost'):wanted.add(head)
        if wanted==before:break
    else:raise ValueError('phase-post connection depth exceeded')
    if not chosen or len(chosen)>96:raise ValueError('local phase-rule budget exceeded')
    runtime_names=set()
    for row in defs:
        if row['symbol'].split('.')[-1]not in wanted:continue
        body=row['command'].split(':=',1)[-1]
        observer=re.match(r'\s*match\s+([\w.]+)\b',body)
        if observer:runtime_names.add(observer[1])
        runtime_names.update(re.findall(r'\(\s*([A-Za-z_][\w.]*)\s+',body))
    opaque=[]
    for name in sorted(runtime_names):
        matches=[row['owner']+'.'+row['symbol']for row in defs if row['symbol']==name or row['symbol'].endswith('.'+name)]
        if len(matches)!=1:raise ValueError('unique post-runtime interface owner required: '+name)
        opaque.extend(matches)
    # Discover only structural descendants of the original classification.
    stop={predicate_head(p)for h in goal['handlers']for p in h['parts'][:-1]}-{goal['post_head']}
    todo=[goal['root_head']];seen=set();aliases=[];sum_types=[]
    while todo:
        head=todo.pop()
        if not head or head in seen or head in stop:continue
        seen.add(head)
        found=logical.get(head,[])
        if len(found)>1:raise ValueError('ambiguous structural phase alias')
        if found:
            row=found[0];aliases.append(row['owner']+'.'+row['symbol'])
            todo.extend(token.split('.')[-1]for token in re.findall(r'[A-Za-z_][\w.]*',row['body']))
        if head in sums:
            if len(sums[head])!=1:raise ValueError('ambiguous phase classification')
            sum_types.extend(sums[head])
    if len(aliases)>96 or len(sum_types)>16:raise ValueError('structural decomposition budget exceeded')
    opens=[];scope=goal['symbol'].rsplit('.',1)[0]
    for where,command in scoped_commands(sources[goal['owner']]):
        match=re.fullmatch(r'Import\s+(.+)',command,re.S)
        if match and where in('',scope):opens.extend(match[1].split())
    if not all(a.SYMBOL.fullmatch(name)for name in opens):raise ValueError('closed import names required')
    side_conditions=sorted({predicate_head(h['parts'][-2])for h in goal['handlers']if len(h['parts'])>2}-{None})
    return dict(goal=goal,rules=sorted(chosen.values(),key=lambda row:row['symbol']),aliases=sorted(set(aliases)),
        projection_side_conditions=side_conditions,
        post_runtime_opaque=sorted(set(opaque)),
        sum_types=sorted(set(sum_types)),opens=opens,excluded=sorted(set(excluded)),
        require_commands=[command for _,command in scoped_commands(sources[goal['owner']])if re.match(r'(?:From\s+[\w.]+\s+)?Require\b',command)],
        source_sha256={owner:hashlib.sha256(source.encode()).hexdigest()for owner,source in sources.items()},
        original_dispatch_proof_used=False,existing_local_phase_proofs_reused=True)

RULES=r'''
Import GeneratedRecordRules.
Inductive PhaseDecomposed(P:Prop):Prop:=phase_mark:PhaseDecomposed P.
Inductive PhaseBoolSplit(b:bool):Prop:=phase_bool_mark:PhaseBoolSplit b.
Ltac phase_head T:=lazymatch T with ?f ?x=>phase_head f|_=>T end.
Ltac phase_once H:=let T:=type of H in
 let h:=phase_head T in idtac "PHASE_DECOMPOSE_TRY" h;
 tryif(match goal with _:PhaseDecomposed T|-_=>idtac end)then fail 0 else idtac;
 let marked:=fresh in assert(PhaseDecomposed T)as marked by constructor;
 let copy:=fresh in pose proof H as copy;destruct copy.
Ltac phase_conjunction_when allowed:=multimatch goal with H:?T|-_=>let head:=phase_head T in allowed head;
 idtac "PHASE_PROJECT_TRY" head;
 let shape:=eval hnf in T in
 lazymatch shape with and _ _=>first[
 let value:=constr:(proj1 H)in fresh_fact value|let value:=constr:(proj2 H)in fresh_fact value]end end.
Ltac phase_assumption:=lazymatch goal with|-?G=>multimatch goal with H:?T|-_=>constr_eq T G;exact H end end.
Ltac phase_logic_when allowed fuel:=first[phase_assumption|lazymatch fuel with S ?rest=>
 match goal with|-?T=>let head:=phase_head T in allowed head;
 first[multimatch goal with H:?U|-_=>let h:=phase_head U in constr_eq h head;exact H end|
 let shape:=eval hnf in T in lazymatch shape with
 |and _ _=>change shape;split;phase_logic_when allowed rest
 |or _ _=>change shape;first[left;phase_logic_when allowed rest|right;phase_logic_when allowed rest]
 |@eq _ _ _=>change shape;first[phase_assumption|reflexivity]end]end end].
Ltac phase_guard logic rule fuel:=lazymatch fuel with S ?rest=>let T:=type of rule in lazymatch T with
 |forall x:?A,_=>first[
   lazymatch A with ?b = true=>let kind:=type of b in constr_eq kind bool;
     tryif has_evar b then fail 0 else idtac;
     tryif(match goal with _:PhaseBoolSplit b|-_=>idtac end)then fail 0 else idtac;
     let marked:=fresh in assert(PhaseBoolSplit b)as marked by constructor;
     let E:=fresh "phase_boolean"in destruct b eqn:E
   end
  |multimatch goal with argument:A|-_=>let next:=constr:(rule argument)in phase_guard logic next rest end
  |let kind:=type of A in tryif constr_eq kind Prop then fail 0 else
   multimatch goal with argument:?B|-_=>let sort:=type of B in
   tryif constr_eq sort Prop then fail 0 else idtac;
   let next:=constr:(rule argument)in phase_guard logic next rest end
  |let argument:=constr:(ltac:(logic 8%nat):A)in let next:=constr:(rule argument)in phase_guard logic next rest]
 end end.
Ltac phase_dump:=try(multimatch goal with H:?T|-_=>idtac "PHASE_HYP" H ":" T;fail 0 end).
'''

def render(profile):
    data=plan(profile);goal=data['goal'];grouped={}
    for row in data['rules']:grouped.setdefault(row['result'],[]).append(row['symbol'])
    branches=[];semantic_heads=[]
    for head,symbols in grouped.items():
        # Resolve the predicate in its declaration owner namespace through its
        # full definition name, not through a possibly shadowed basename.
        owners=[]
        for owner in data['source_sha256']:
            path=a.ROOT/'src'/Path(*owner.split('.')).with_suffix('.v')
            owners.extend(owner+'.'+row['symbol']for row in definitions(path.read_text())if row['symbol'].split('.')[-1]==head)
        if len(owners)!=1:raise ValueError('unique phase-post predicate owner required')
        semantic_heads.extend(owners)
        branches.append('lazymatch goal with|-?G=>let h:=phase_head G in let wanted:=constr:(@'+owners[0]+')in constr_eq h wanted;first['+
            ' | '.join('idtac "PHASE_RULE '+symbol+'";solve[eapply '+symbol+';phase_solve rest]'for symbol in symbols)+']end')
    ordered=sorted(goal['handlers'],key=lambda row:len(row['parts'])==2)
    handlers=' | '.join('idtac "PHASE_HANDLER '+row['name']+'";solve[eapply '+row['name']+';phase_solve rest]'for row in ordered)
    parameters=' '.join(row['name']for row in goal['handlers'])
    decomposers=[]
    for symbol in data['aliases']:
        decomposers.append('multimatch goal with H:?T|-_=>let h:=phase_head T in let wanted:=constr:(@'+symbol+')in constr_eq h wanted;phase_once H end')
    for symbol in data['sum_types']:
        decomposers.append('multimatch goal with H:?T|-_=>let h:=phase_head T in let wanted:=constr:(@'+symbol+')in constr_eq h wanted;phase_once H end')
    guards=' | '.join('phase_guard phase_logic '+row['symbol']+' 32%nat'for row in data['rules']if '=true'in row['statement'].replace(' ',''))or'fail 0'
    projection_heads=['Coq.Init.Logic.and',*data['aliases'],*data['projection_side_conditions']]
    lines=['From Coq Require Import List ZArith Bool Lia.',
        'Require Import '+' '.join(sorted(data['source_sha256']))+'.',
        *[command+'.'for command in data['require_commands']],
        'Import '+' '.join(data['opens']+[goal['owner']+'.'+goal['symbol'].rsplit('.',1)[0]])+'.',
        *(['Local Opaque '+' '.join(data['post_runtime_opaque'])+'.']if data['post_runtime_opaque']else[]),COQ_RULES,RULES,
        'Ltac phase_projection_head h:=first['+' | '.join('let wanted:=constr:(@'+symbol+')in constr_eq h wanted'for symbol in projection_heads)+'].',
        'Ltac phase_conjunction:=phase_conjunction_when phase_projection_head.',
        'Ltac phase_logic_head h:=tryif(first['+' | '.join('let wanted:=constr:(@'+s+')in constr_eq h wanted'for s in semantic_heads)+'])then fail 0 else idtac.',
        'Ltac phase_logic fuel:=phase_logic_when phase_logic_head fuel.',
        'Ltac phase_solve fuel:=lazymatch goal with|-?G=>let h:=phase_head G in idtac "PHASE_SOLVE" h end;first[phase_logic 8%nat|lazymatch fuel with S ?rest=>first['+' | '.join(branches)+']end].',
        'Ltac phase_handlers '+parameters+' fuel:=lazymatch fuel with S ?rest=>first['+handlers+']end.',
        'Ltac phase_decompose:=first[match goal with H:or _ _|-_=>phase_once H|H:exists _,_|-_=>phase_once H end | '+' | '.join(decomposers)+'].',
        'Ltac phase_boolean:=first['+guards+'].',
        'Ltac phase_close '+parameters+' fuel:=lazymatch fuel with',
        '|O=>phase_dump;fail 1000 "phase dispatch structural budget exhausted"',
        '|S ?rest=>first[progress phase_conjunction;phase_close '+parameters+' rest',
        ' |phase_decompose;idtac "PHASE_STRUCTURAL_SPLIT";phase_close '+parameters+' rest',
        ' |solve[phase_handlers '+parameters+' 5%nat]',
        ' |phase_boolean;idtac "PHASE_BOOLEAN_SPLIT";phase_close '+parameters+' rest',
        ' |phase_dump;fail 1000 "phase dispatch residual"]end.',
        'Lemma generated_dispatch '+goal['statement']+'.',
        'Proof. intros. phase_close '+parameters+' 256%nat. Qed.',
        'Definition checked_dispatch : ltac:(let T:=type of(@'+goal['owner']+'.'+goal['symbol']+')in exact T) := @generated_dispatch.',
        'Print Assumptions checked_dispatch.']
    return data,'\n'.join(lines)+'\n'

def check(profile,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be within 1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(profile)
    except ValueError as error:
        report=dict(accepted=False,native_started=False,residual=str(error),whole_goal_complete=False)
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    path=output/'Phases.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(a.framework.FLAGS)
    for row in profile.get('coq_load_paths',[]):flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedPhases']
    report=dict(accepted=False,whole_goal_complete=False,llm_calls=0,original_dispatch_proof_used=False,
        existing_local_phase_proofs_reused=True,source_sha256=hashlib.sha256(source.encode()).hexdigest())
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(a.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        ok,axioms=pipeline.audit_shared_output(source,c.stdout);report.update(assumptions_accepted=ok,assumptions=axioms)
        if ok and time.monotonic()<deadline:
            ks=time.monotonic();k,t=run_stage([str(a.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedPhases.Phases'],output/'coqchk.log',deadline-ks)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--profile',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    x=p.parse_args();report=check(json.loads(x.profile.read_text()),x.output);print(json.dumps(report,indent=2));raise SystemExit(0 if report['accepted']else 1)
