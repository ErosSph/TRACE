"""Compile record evidence and relation-local facts into an architecture proof.

The catalogue proposes projections/one-premise rules, never proof assumptions.
Every fact is an actual closed Coq application of an existing projection or
lemma. Failure to close the original architectural implication remains failure.
"""
from __future__ import annotations
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_arch_projection as projection
import cpu_relation_projection_graph as graph
from cpu_record_evidence import records,definitions,COQ_RULES
from cpu_local_evidence_catalog import commands,declarations
from cpu_certificate_acceptance import run_stage


def split_conjunction(body):
    out=[];depth=0;start=0;i=0
    while i<len(body):
        if body[i]in '([{':depth+=1
        elif body[i]in ')]}':depth-=1
        elif depth==0 and body[i:i+2]=='/\\':out.append(body[start:i].strip());start=i+2;i+=1
        i+=1
    out.append(body[start:].strip());return out


def signature(body):
    depth=0
    for i,c in enumerate(body):
        if c in '([{':depth+=1
        elif c in ')]}':depth-=1
        elif c=='='and depth==0:
            return ('equality',graph.predicate_head(body[:i]),graph.predicate_head(body[i+1:]))
    return ('predicate',graph.predicate_head(body))


def plan(binding):
    base=graph.catalog(binding);root=projection.pipeline.adapter.ROOT
    sources={m:(root/'src'/Path(*m.split('.')).with_suffix('.v')).read_text()for m in base['source_sha256']}
    rows=[];theorems=[];residuals=[]
    for module,source in sources.items():
        for row in records(source):
            if row.get('residual'):residuals.append(dict(module=module,**row));continue
            rows.append(dict(module=module,**row))
        for row in declarations(source):theorems.append(dict(module=module,**row))
    names={row['symbol'].split('.')[-1]for row in rows}
    physical=binding['physical']['symbol'].split('.')[-1]
    unary=[]
    for row in theorems:
        if re.search(r'\b'+re.escape(physical)+r'\b',row['statement']):continue
        body=graph.type_body(row['statement']);parts=graph.implication_parts(body)if body else None
        if parts and len(parts)==2 and graph.predicate_head(parts[0])in names and '='not in parts[1]:
            result=graph.predicate_head(parts[1])
            if result:unary.append(dict(premise=graph.predicate_head(parts[0]),result=result,**row))
    reachable=set(base['available_predicate_tokens'])&names
    for _ in range(4):
        before=set(reachable)
        for row in rows:
            if row['symbol'].split('.')[-1]in reachable:
                for field in row['fields']:
                    head=graph.predicate_head(field['type'])
                    if head in names:reachable.add(head)
        for row in unary:
            if row['premise']in reachable and row['result']in names:reachable.add(row['result'])
        if reachable==before:break
    chosen=[r for r in rows if r['symbol'].split('.')[-1]in reachable]
    rules=[r for r in unary if r['premise']in reachable]
    if len(chosen)>32 or len(rules)>64:raise ValueError('record evidence catalogue budget exceeded')
    leaf_signatures=set()
    for source in sources.values():
        for command in commands(source):
            if any(re.match(r'Definition\s+'+re.escape(head)+r'\b',command)for head in base['goal_heads']):
                body=command.split(':=',1)[-1]
                leaf_signatures.update(signature(p)for p in split_conjunction(body))
    facts=[]
    for row in theorems:
        if re.search(r'\b'+re.escape(physical)+r'\b',row['statement']):continue
        body=graph.type_body(row['statement'])
        if not body or '<->'in body:continue
        parts=graph.implication_parts(body);result=parts[-1]if parts else body
        if signature(result)in leaf_signatures:facts.append(row)
    if len(facts)>32:raise ValueError('architectural leaf fact budget exceeded')
    opaque=set()
    for source in sources.values():
        for command in commands(source):
            if re.match(r'Definition\s+'+re.escape(physical)+r'\b',command):
                for match in re.finditer(r'Nat\.iter\s+\w+\s+([A-Za-z_][A-Za-z0-9_.]*)\s*\(\s*([A-Za-z_][A-Za-z0-9_.]*)',command):
                    opaque.update(match.groups())
    qualified_opaque=sorted({row['symbol']for source in sources.values()for row in definitions(source)
                             if row['symbol'].split('.')[-1]in opaque})
    conjunction_aliases=[dict(module=module,**row)for module,source in sources.items()
        for row in definitions(source)
        if ':='in row['command']and len(split_conjunction(row['command'].split(':=',1)[1]))>1]
    if len(conjunction_aliases)>128:raise ValueError('conjunction alias catalogue budget exceeded')
    return dict(records=chosen,unary_rules=rules,leaf_facts=facts,
                conjunction_aliases=conjunction_aliases,
                leaf_signatures=sorted([list(s)for s in leaf_signatures],key=str),
                runtime_functions_opaque=qualified_opaque,source_sha256=base['source_sha256'],
                unsupported_records=residuals,physical_relation_discovered=False)


WORD_RULE=r'''
Require Import Lang.ExtendedSV Ex.External.CPUByteBankWord coqutil.Word.Interface coqutil.Word.Properties.
Module GeneratedWordProjection.
Local Open Scope Z_scope.
Section Rule.
Context {word:Interface.word 32}{word_ok:word.ok word}.
Lemma nextpc (pc next:word) (physical_pc:Z) :
 next=word.add pc(word.of_Z 4) ->physical_pc=word.unsigned pc ->
 word.unsigned next=ExtendedSV.ExtendedSV.norm 32(physical_pc+4).
Proof.
 intros -> ->. rewrite word.unsigned_add,word.unsigned_of_Z.
 unfold word.wrap. rewrite CPUByteBankWord.CPUByteBankWord.norm_mod.
 change(Z.of_nat 32)with 32. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.
End Rule.
End GeneratedWordProjection.
'''


def render(binding):
    data=plan(binding);source=projection.render(binding)
    match=re.search(r'\n intros (\w+) (\w+) (\w+) (\w+)\.',source)
    runtime,_,frontier,_=match.groups()
    owners={r['module']for r in data['records']+data['unary_rules']+data['leaf_facts']+data['conjunction_aliases']}
    header='From Coq Require Import Lia.\nRequire Import '+' '.join(sorted(owners))+'.\n'+COQ_RULES+WORD_RULE
    core=['Ltac record_head term := lazymatch term with ?f ?x => record_head f | _ => term end.',
          'Ltac record_projection_step := first [']
    branches=[]
    for row in data['records']:
        fields=' | '.join('GeneratedRecordRules.apply_to_fact constr:(@'+f['symbol']+') H'for f in row['fields'])
        branches.append('match goal with H : ?T |- _ => let head := record_head T in '
                        'let wanted := constr:(@'+row['symbol']+') in unify head wanted; first [ '+fields+' ] end')
    core+=[' | '.join(branches)+'].']
    aliases=[]
    for row in data['conjunction_aliases']:
        aliases.append('match goal with H : ?T |- _ => let head := record_head T in '
            'let wanted := constr:(@'+row['symbol']+') in unify head wanted; '
            'first [let value := constr:(proj1 H) in GeneratedRecordRules.fresh_fact value | '
            'let value := constr:(proj2 H) in GeneratedRecordRules.fresh_fact value] end')
    core+=['Ltac record_conjunction_alias := first [ '+' | '.join(aliases)+' ].'if aliases else
           'Ltac record_conjunction_alias := fail 0 "no conjunction alias".']
    branches=[]
    for rule in data['unary_rules']:
        types=[r['symbol']for r in data['records']if r['symbol'].split('.')[-1]==rule['premise']]
        guards=' | '.join('let wanted := constr:(@'+t+') in unify head wanted'for t in types)
        branches.append('match goal with H : ?T |- _ => let head := record_head T in '
                        'first [ '+guards+' ]; GeneratedRecordRules.apply_to_fact constr:(@'+rule['symbol']+') H end')
    core+=['Ltac record_unary_step := first [ '+' | '.join(branches)+' ].'if branches else
           'Ltac record_unary_step := fail 0 "no unary rule".']
    leaf=['solve [eapply GeneratedWordProjection.nextpc; eassumption]']
    leaf+=['solve [eapply '+r['symbol']+'; repeat first [eassumption | split]]'for r in data['leaf_facts']]
    core+=['Ltac record_leaf := first [eassumption | '+' | '.join(leaf)+' ].',
      'Ltac record_finish := let rec finish := first [record_leaf |',
      ' let expanded := match goal with |- ?G => eval hnf in G end in change expanded;',
      ' match goal with |- and ?A ?B => let left_fact := fresh "arch_left" in',
      ' assert (left_fact:A) by finish; split; [exact left_fact | finish] end] in finish.']
    source=source.replace('Module GeneratedArchitecturalProjection.',header+'\nModule GeneratedArchitecturalProjection.\n'+'\n'.join(core)+'\n',1)
    old=' repeat first [ assumption | split ].'
    opaque='Local Opaque Lang.ExtendedSV.ExtendedSV.PhaseSemantics Lang.ExtendedSV.ExtendedSV.phase_driven_state '+\
        'Lang.ExtendedSV.ExtendedSV.read_signal Lang.ExtendedSV.ExtendedSV.norm Nat.iter '+\
        ' '.join(data['runtime_functions_opaque'])+'.\n'
    # Runtime symbols may be visible only after their original module Import.
    # Their names are source-derived, and Coq checks they are actual constants.
    source=source.replace('Theorem structural_architecture',opaque+'Theorem structural_architecture',1)
    steps=[' do 64 (try match goal with H : and _ _ |- _ => destruct H | H : exists _, _ |- _ => destruct H end).',
           f' try subst {runtime}.',f' try subst {frontier}.',
           ' do 128 (try first [GeneratedRecordRules.conjunction_fact | record_conjunction_alias | record_projection_step | record_unary_step | GeneratedRecordRules.local_implication_fact]).',
           ' all: try record_finish.',
           ' all: repeat split.',
           ' all: try record_leaf.']
    source=source.replace(old,'\n'.join(steps),1)
    return data,source


def check(profile,output):
    data,source=render(profile['joint_binding']);output=Path(output);output.mkdir(parents=True,exist_ok=False)
    path=output/'ArchitecturalProjection.v';path.write_text(source)
    (output/'record-plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(projection.pipeline.adapter.framework.FLAGS)
    for row in profile.get('coq_load_paths',[]):flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedArchitecturalProjection']
    report=dict(accepted=False,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
      projection_strategy='record_evidence_saturation',old_architecture_witness_used=False,
      manual_role_map_read=False,physical_relation_discovered=False,itree_refinement_proved=False,llm_calls=0,
      records=len(data['records']),unary_rules=len(data['unary_rules']),leaf_facts=len(data['leaf_facts']))
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(projection.pipeline.adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',1200)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
      ok,axioms=projection.pipeline.audit_shared_output(source,c.stdout);report.update(assumptions_accepted=ok,assumptions=axioms)
      if ok and deadline>time.monotonic():
       ks=time.monotonic()
       k,t=run_stage([str(projection.pipeline.adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
        'GeneratedArchitecturalProjection.ArchitecturalProjection'],output/'coqchk.log',deadline-ks)
       report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,accepted=k.returncode==0)
    count=c.stdout.count('RECORD_FACT_ADDED')
    report.update(structural_architecture_proved=report['accepted'],
                  record_fact_applications_checked=count,
                  existing_lower_projection_helper_used=report['accepted']and count>0,
                  residual_goals_observed='ARCH_PROJECTION_RESIDUAL'in c.stdout,overall_seconds=time.monotonic()-start)
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    result=check(json.loads(a.profile.read_text()),a.output)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted'] else 1)
