"""Bounded relation-implication composition for architectural projections.

Only already imported project sources and their immediate Require dependencies
are indexed. Coq, not this textual graph, proves the implication. Whole Physical
bridges are excluded. This does not discover Physical or temporal invariants.
"""
from __future__ import annotations
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_arch_projection as projection
from cpu_local_evidence_catalog import commands,declarations
from cpu_certificate_acceptance import run_stage

ROOT=projection.pipeline.adapter.ROOT
MAX_SOURCES=256
MAX_HELPERS=32


def dependencies(source):
    for command in commands(source):
        match=re.fullmatch(r'(?:From\s+([A-Za-z_][A-Za-z0-9_.]*)\s+)?Require\s+(?:(?:Import|Export)\s+)?(.+)',command,re.S)
        if not match:continue
        prefix,modules=match.groups()
        for module in modules.split():
            name=(prefix+'.'if prefix else '')+module
            if projection.pipeline.adapter.SYMBOL.fullmatch(name):yield name


def type_body(statement):
    depth=0
    for i,c in enumerate(statement):
        if c in '([{':depth+=1
        elif c in ')]}':depth-=1
        elif c==':'and depth==0:return statement[i+1:].strip()
    return None


def implication_parts(body):
    if '<->'in body:return None  # iff conversion has a separately checked strategy
    parts=[];depth=0;start=0;i=0
    while i<len(body):
        c=body[i]
        if c in '([{':depth+=1
        elif c in ')]}':depth-=1
        elif depth==0 and body[i:i+2]=='->':parts.append(body[start:i].strip());start=i+2;i+=1
        i+=1
    parts.append(body[start:].strip())
    return parts if len(parts)>1 else None


def predicate_head(term):
    term=term.strip()
    match=re.match(r'([A-Za-z_][A-Za-z0-9_.]*)\b',term)
    if not match or match.group(1)in {'forall','exists','fun','match','True','False','if','let'}:return None
    return match.group(1).split('.')[-1]


def catalog(binding,root=None):
    # Validate the fixed header without consulting any proof-role annotation.
    projection.render(binding)
    root=ROOT if root is None else Path(root)
    sources={};missing=[]
    def load(module,required=False):
        if module in sources:return
        path=root/'src'/Path(*module.split('.')).with_suffix('.v')
        if not path.is_file():
            if required:raise ValueError('missing explicit relation source owner: '+module)
            missing.append(module);return
        if len(sources)>=MAX_SOURCES:raise ValueError('relation source budget exceeded; no truncation')
        sources[module]=path.read_text()
    for module in binding['imports']:load(module,True)
    roots=dict(sources)
    for source in roots.values():
        for module in dependencies(source):load(module)
    target=binding['target']['symbol'].split('.')[-1]
    physical=binding['physical']['symbol'].split('.')[-1]
    goal_heads=set();available=set()
    for source in roots.values():
        for command in commands(source):
            if re.match(r'Definition\s+'+re.escape(target)+r'\b',command):
                field=re.search(r'\btarget_arch_relation\s*:=\s*(.*?)(?:;|\|\})',command,re.S)
                if field:
                    term=field.group(1);head=predicate_head(term)
                    if head and head!='target_arch_relation':goal_heads.add(head)
                    else:
                        for match in re.finditer(r'(?:=>|\bthen|\belse)\s*([A-Za-z_][A-Za-z0-9_.]*)',term):
                            head=predicate_head(match.group(1))
                            if head:goal_heads.add(head)
            if re.match(r'(?:Definition|Record|Inductive)\s+'+re.escape(physical)+r'\b',command):
                available.update(token.split('.')[-1]for token in re.findall(r'[A-Za-z_][A-Za-z0-9_.]*',command))
    if not goal_heads:raise ValueError('no supported target-relation heads; no guessed projection')
    edges=[]
    for module,source in sources.items():
        for row in declarations(source):
            if re.search(r'\b'+re.escape(physical)+r'\b',row['statement']):continue
            body=type_body(row['statement']);parts=implication_parts(body)if body else None
            if not parts:continue
            conclusion=predicate_head(parts[-1]);premises=[predicate_head(p)for p in parts[:-1]]
            if not conclusion or any(p is None for p in premises):continue
            edges.append(dict(symbol=row['symbol'],premises=premises,conclusion=conclusion,module=module))
    # Backward reachability is a proposal: same basename/shape is not evidence.
    selected={}
    def merge(destination,evidence):
        for symbol,edge in evidence.items():
            if symbol in destination and destination[symbol]!=edge:
                raise ValueError('ambiguous selected helper symbol')
            destination[symbol]=edge
    def paths(goal,depth,visiting):
        if goal in available:return {}
        if not depth or goal in visiting:return None
        found=None
        for edge in edges:
            if edge['conclusion']!=goal:continue
            branch={}
            for premise in edge['premises']:
                evidence=paths(premise,depth-1,visiting|{goal})
                if evidence is None:break
                merge(branch,evidence)
            else:
                branch[edge['symbol']]=edge
                if found is None:found={}
                merge(found,branch)
        return found
    for head in sorted(goal_heads):
        evidence=paths(head,3,set())
        if evidence:merge(selected,evidence)
    if len(selected)>MAX_HELPERS:raise ValueError('relation helper budget exceeded; no truncation')
    return dict(goal_heads=sorted(goal_heads),available_predicate_tokens=sorted(available),
                candidates=[selected[k]for k in sorted(selected)],
                source_sha256={m:hashlib.sha256(s.encode()).hexdigest()for m,s in sources.items()},
                missing_optional_source_owners=sorted(set(missing)),
                graph_depth=3,proof_composition_depth=3,
                whole_physical_bridge_selected=False,physical_relation_discovered=False)


def render(binding,root=None):
    data=catalog(binding,root);source=projection.render(binding)
    match=re.search(r'\n intros (\w+) (\w+) (\w+) (\w+)\.',source)
    if not match:raise ValueError('unexpected structural header')
    runtime,_,frontier,_=match.groups()
    extra=[' do 64 (try match goal with',
           ' | H : _ /\\ _ |- _ => destruct H',
           ' | H : exists _, _ |- _ => destruct H',
           ' end).',f' try subst {runtime}.',f' try subst {frontier}.']
    selected=data['candidates']
    if selected:
        source=source.replace('Module GeneratedArchitecturalProjection.',
            'Require Import '+' '.join(sorted({r['module']for r in selected}))+'.\nModule GeneratedArchitecturalProjection.',1)
    marker=' repeat first [ assumption | split ].'
    tactic=''
    if selected:
        available=set(data['available_predicate_tokens'])
        def compose(goal,depth):
            if goal in available:return 'eassumption'
            if not depth:return None
            branches=[]
            for edge in selected:
                if edge['conclusion']!=goal:continue
                children=[compose(p,depth-1)for p in edge['premises']]
                if any(child is None for child in children):continue
                branches.append('solve [ eapply '+edge['symbol']+'; [ '+' | '.join(children)+' ] ]')
            return 'first [ '+' | '.join(branches)+' ]'if branches else None
        derivations=[d for head in data['goal_heads'] if (d:=compose(head,3))is not None]
        if not derivations:raise ValueError('selected graph has no bounded application tree')
        script='first [ '+' | '.join('solve [ '+d+' ]'for d in derivations)+' ]'
        tactic=' all: first [ match goal with |- ?G => let witness := fresh "auto_projection" in '+\
            'assert (witness : G) by ('+script+'); '+\
            'idtac "ARCH_RELATION_GRAPH_USED"; exact witness end | idtac ].\n'
    # Preserve the relational goal head for backward chaining. Splitting it
    # first loses the exact conclusion of the available conversion lemma.
    source=source.replace(marker,'\n'.join(extra)+'\n'+tactic+
                          ' all: repeat first [ assumption | split ].',1)
    return data,source


def check(profile,output):
    data,source=render(profile['joint_binding']);output=Path(output);output.mkdir(parents=True,exist_ok=False)
    path=output/'ArchitecturalProjection.v';path.write_text(source)
    (output/'relation-graph.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(projection.pipeline.adapter.framework.FLAGS)
    for item in profile.get('coq_load_paths',[]):flags+=['-R',item['directory'],item['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedArchitecturalProjection']
    report=dict(accepted=False,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        projection_strategy='bounded_relation_graph',old_architecture_witness_used=False,
        manual_role_map_read=False,physical_relation_discovered=False,itree_refinement_proved=False,
        llm_calls=0,candidate_count=len(data['candidates']))
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(projection.pipeline.adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',1200)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        ok,axioms=projection.pipeline.audit_shared_output(source,c.stdout)
        report.update(assumptions_accepted=ok,assumptions=axioms)
        if ok and deadline>time.monotonic():
            ks=time.monotonic()
            k,t=run_stage([str(projection.pipeline.adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedArchitecturalProjection.ArchitecturalProjection'],output/'coqchk.log',deadline-ks)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,accepted=k.returncode==0)
    report.update(structural_architecture_proved=report['accepted'],
        existing_lower_projection_helper_used='ARCH_RELATION_GRAPH_USED'in c.stdout,
        residual_goals_observed='ARCH_PROJECTION_RESIDUAL'in c.stdout,overall_seconds=time.monotonic()-start)
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    result=check(json.loads(a.profile.read_text()),a.output)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted'] else 1)
