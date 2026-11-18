"""Compose finite instruction-cut cases from lower segment preservation rules.

Source declarations propose the exact goal, aliases, conversions and finite
constructor applications. Coq checks all applications and the original type.
No original dispatch body or whole-current preservation theorem is applied.
"""
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_auto_adapter as a
import cpu_auto_pipeline as pipeline
from cpu_certificate_acceptance import run_stage
from cpu_local_evidence_catalog import declarations
from cpu_record_evidence import definitions,records,scoped_commands
from cpu_relation_projection_graph import dependencies,type_body,implication_parts,predicate_head

def compact(text):return re.sub(r'\s+','',text)

def finite_types(sources,demanded_predicates):
    found={}
    for owner,source in sources.items():
        for scope,command in scoped_commands(source):
            match=re.fullmatch(r'Inductive\s+(\w+)\s*(?::\s*(?:Set|Type))?\s*:=\s*(.*)',command,re.S)
            if not match:continue
            constructors=[]
            for entry in match[2].strip().lstrip('|').split('|'):
                node=re.fullmatch(r'\s*(\w+)\s*((?:\([^()]*\)\s*)*)',entry,re.S)
                if not node:break
                args=[]
                for binder in re.findall(r'\(([^()]*)\)',node[2]):
                    b=re.fullmatch(r'\s*([\w\s]+)\s*:\s*([\w.]+)\s*',binder)
                    if not b:break
                    args.extend([b[2]]*len(b[1].split()))
                else:
                    if len(args)>4:break
                    constructors.append(dict(symbol=owner+'.'+(scope+'.'if scope else'')+node[1],arguments=args));continue
                break
            else:
                if constructors and len(constructors)<=16:
                    symbol=owner+'.'+(scope+'.'if scope else'')+match[1]
                    found[symbol]=constructors
    if len(found)>128:raise ValueError('finite-type source budget exceeded')
    def resolve(name):
        options=[key for key in found if key==name or key.endswith('.'+name)]
        return options[0]if len(options)==1 else None
    def patterns(name,depth):
        out=[]
        for ctor in found[name]:
            out.append('('+ctor['symbol']+(' '+' '.join('_'for _ in ctor['arguments'])if ctor['arguments']else'')+')')
            variants=[[]]
            for argument in ctor['arguments']:
                child=resolve(argument)
                choices=patterns(child,depth-1)if child and depth else ['_']
                variants=[old+[new]for old in variants for new in choices]
                if len(variants)>128:raise ValueError('constructor product budget exceeded')
            out.extend('('+ctor['symbol']+(' '+' '.join(args)if args else'')+')'for args in variants)
        return list(dict.fromkeys(out))
    selected=set()
    for source in sources.values():
        for row in definitions(source):
            if row['symbol'].split('.')[-1]not in demanded_predicates:continue
            body=row['command'].split(':=',1)[-1]
            match=re.match(r'\s*match\s+\w+\s+with\s*\|?\s*([\w.]+)',body)
            if not match:continue
            owners=[key for key,constructors in found.items()if any(
                ctor['symbol']==match[1]or ctor['symbol'].endswith('.'+match[1])for ctor in constructors)]
            if len(owners)!=1:raise ValueError('unique finite discriminator type required')
            selected.add(owners[0])
    result={key:patterns(key,1)for key in sorted(selected)}
    if sum(map(len,result.values()))>512:raise ValueError('constructor application budget exceeded')
    return result

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
            text=row['statement']
            if all(word in text for word in('FirstVisibleCycle','FormalSpec.run1','CurrentInstructionCut','exists'))and not re.search(r'\bPhysical\b|StreamingTransfer|eutt|≈',text):
                goals.append(dict(owner=owner,**row))
    if len(goals)!=1:raise ValueError('unique instruction-cut segment dispatch interface required')
    goal=goals[0];body=type_body(goal['statement']);parts=implication_parts(body)
    if not parts:raise ValueError('explicit dispatch premises required')
    for owner in list(dependencies(sources[goal['owner']])):
        path=a.ROOT/'src'/Path(*owner.split('.')).with_suffix('.v')
        if path.is_file():sources.setdefault(owner,path.read_text())
    if len(sources)>256:raise ValueError('segment source budget exceeded')
    aliases=[]
    for owner,source in sources.items():
        for row in definitions(source):
            result=row['command'].split(':=',1)[-1].strip()
            if compact(result)==compact(parts[-1]):aliases.append(dict(owner=owner,**row))
    if len(aliases)!=1:raise ValueError('unique exact segment-result alias required')
    alias=aliases[0];alias_name=alias['symbol'].split('.')[-1]
    sum_head=next((predicate_head(p)for p in parts[:-1]if predicate_head(p)and predicate_head(p)not in('Z','forall')),None)
    if not sum_head:raise ValueError('instruction sum premise required')
    sum_symbol=goal['owner']+'.'+goal['symbol'].rsplit('.',1)[0]+'.'+sum_head
    preservers=[];conversions=[];excluded=[];demanded=set();unary=[]
    local_records={row['symbol'].split('.')[-1]for row in records(sources[goal['owner']])}
    for owner,source in sources.items():
        for row in declarations(source):
            text=row['statement'];p=implication_parts(type_body(text)or'')
            symbol=owner+'.'+row['symbol']
            if symbol==goal['owner']+'.'+goal['symbol']or not p:excluded.append(symbol);continue
            if (any(word in text for word in('FirstVisibleCycle','Certificate','StreamingTransfer','OrderedCycleSafety','BoundedProgress','≈','eutt'))):
                excluded.append(symbol);continue
            if predicate_head(p[-1])==alias_name:
                preservers.append(symbol)
                demanded.update(head for term in p[:-1]if (head:=predicate_head(term))is not None)
            elif len(p)==2:
                unary.append((symbol,predicate_head(p[0]),predicate_head(p[-1])))
    conversions=[symbol for symbol,pre,post in unary if pre in local_records or post in demanded]
    if not preservers:raise ValueError('lower segment preservation rules required')
    if len(preservers)>24 or len(conversions)>48:raise ValueError('local segment-rule budget exceeded')
    goal_scope=goal['symbol'].rsplit('.',1)[0];opens=[]
    for scope,command in scoped_commands(sources[goal['owner']]):
        match=re.fullmatch(r'Import\s+(.+)',command,re.S)
        if match and scope in('',goal_scope):opens.extend(match[1].split())
    if not all(a.SYMBOL.fullmatch(name)for name in opens):raise ValueError('closed module imports required')
    return dict(goal=goal,alias=alias,sum_symbol=sum_symbol,opens=opens,
        direct_imports=sorted(set(dependencies(sources[goal['owner']]))),
        require_commands=[command for _,command in scoped_commands(sources[goal['owner']])
            if re.match(r'(?:From\s+[\w.]+\s+)?Require\b',command)],
        preservers=sorted(set(preservers)),conversions=sorted(set(conversions)),
        constructors=finite_types(sources,demanded),excluded=sorted(set(excluded)),
        source_sha256={name:hashlib.sha256(source.encode()).hexdigest()for name,source in sources.items()},
        original_dispatch_proof_used=False,whole_current_preservation_used=False,
        existing_instruction_preservation_proofs_reused=True)

def render(profile):
    data=plan(profile);goal=data['goal'];alias=data['alias']
    imports=sorted(set(data['source_sha256'])|set(profile['joint_binding']['imports']))
    scope=goal['owner']+'.'+goal['symbol'].rsplit('.',1)[0]
    alias_term=alias['owner']+'.'+alias['symbol']
    lines=['From Coq Require Import ZArith List Lia.',
        'Require Import '+' '.join(imports)+'.',
        *[command+'.'for command in data['require_commands']],
        'Import '+' '.join(data['opens']+[scope])+'.',
        'Create HintDb segment_bridge.',
        '#[local] Hint Resolve '+' '.join(data['conversions'])+' : segment_bridge.',
        'Ltac segment_dump:=try(multimatch goal with H:?T|-_=>idtac "SEGMENT_HYP" H ":" T;fail 0 end).',
        'Ltac segment_finish fuel:=first[eassumption|reflexivity|lazymatch fuel with S ?rest=>first['+
         ' | '.join('solve[eapply '+symbol+';segment_finish rest]'for symbol in data['conversions'])+']end].',
        'Ltac segment_specialize rule :=first[solve[eapply rule;segment_finish 4%nat]']
    for typ,patterns in data['constructors'].items():
        branches=' | '.join('solve[eapply(rule '+p+');segment_finish 4%nat]'for p in patterns)
        lines.append('|let T:=type of rule in lazymatch T with forall x:?A,_=>let wanted:=constr:(@'+typ+')in unify A wanted;first['+branches+']end')
    lines+= ['].',
        'Ltac segment_alias term fuel:=let T:=type of term in lazymatch T with',
        ' | forall x:?A,_=>lazymatch fuel with S ?rest=>multimatch goal with argument:A|-_=>let next:=constr:(term argument)in segment_alias next rest end end',
        ' | Prop=>change term end.',
        'Lemma generated_segments '+goal['statement']+'.',
        'Proof. intros.',
        ' segment_alias constr:(@'+alias_term+') 16%nat.',
        ' match goal with H:?T|-_=>let rec head t:=lazymatch t with ?f ?x=>head f|_=>t end in',
        ' let h:=head T in constr_eq h constr:(@'+data['sum_symbol']+');destruct H end.',
        ' all:first['+' | '.join('segment_specialize '+symbol for symbol in data['preservers'])+' |segment_dump;fail 1000 "local segment synthesis residual"].',
        ' Unshelve. all:first[exact 0%Z|exact 0%nat|exact true].',
        'Qed.',
        'Definition checked_segments : ltac:(let T:=type of(@'+goal['owner']+'.'+goal['symbol']+')in exact T) := @generated_segments.',
        'Print Assumptions checked_segments.']
    return data,'\n'.join(lines)+'\n'

def check(profile,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be within 1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(profile)
    except ValueError as error:
        report=dict(accepted=False,native_started=False,residual=str(error),whole_goal_complete=False)
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    path=output/'Segments.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(a.framework.FLAGS)
    for row in profile.get('coq_load_paths',[]):flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedSegments']
    report=dict(accepted=False,whole_goal_complete=False,llm_calls=0,
        original_dispatch_proof_used=False,whole_current_preservation_used=False,
        source_sha256=hashlib.sha256(source.encode()).hexdigest())
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(a.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        ok,axioms=pipeline.audit_shared_output(source,c.stdout);report.update(assumptions_accepted=ok,assumptions=axioms)
        if ok and time.monotonic()<deadline:
            ks=time.monotonic();k,t=run_stage([str(a.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedSegments.Segments'],output/'coqchk.log',deadline-ks)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--profile',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    x=p.parse_args();report=check(json.loads(x.profile.read_text()),x.output);print(json.dumps(report,indent=2));raise SystemExit(0 if report['accepted']else 1)
