"""Compile nonempty queue cuts using typed records and lower cycle evidence.

The parser proposes rules, never assumptions. Every field, transition and
queue equation must close in Coq against the unchanged original target.
"""
from __future__ import annotations
import re
from pathlib import Path
import cpu_record_arch_projection as records
import cpu_relation_projection_graph as relations
from cpu_record_evidence import definitions
from cpu_local_evidence_catalog import declarations
from cpu_certificate_acceptance import render_proof_argument

SATURATION_RULES=r'''
Module GeneratedQueueSearch.
Ltac saturate limit step :=
 let rec run fuel := lazymatch fuel with
 | O => idtac "QUEUE_SATURATION_BUDGET"
 | S ?remaining => idtac "QUEUE_SATURATION_PROBE";
   tryif step constr:(tt) then run remaining else idtac "QUEUE_SATURATION_FIXED_POINT"
 end in run limit.
End GeneratedQueueSearch.
'''


def without_leading_lets(body):
    for _ in range(16):
        if not body.lstrip().startswith('let '):return body.strip()
        brackets=0;nested=0;end=None
        for token in re.finditer(r'\blet\b|\bin\b|[()\[\]{}]',body):
            value=token.group()
            if value in '([{':brackets+=1
            elif value in ')]}':brackets-=1
            elif brackets==0:
                if value=='let':nested+=1
                else:
                    nested-=1
                    if nested==0:end=token.end();break
        if end is None:raise ValueError('unsupported top-level let scope')
        body=body[end:].strip()
    raise ValueError('queue type let budget exceeded')


def observation_equality(statement,observer):
    body=relations.type_body(statement)
    if body is None:return False
    body=without_leading_lets(body)
    parts=relations.implication_parts(body)
    conclusion=without_leading_lets(parts[-1]if parts else body)
    depth=0;equality=False
    for index,char in enumerate(conclusion):
        if char in '([{':depth+=1
        elif char in ')]}':depth-=1
        elif char=='='and depth==0:
            before=conclusion[index-1]if index else ''
            after=conclusion[index+1]if index+1<len(conclusion)else ''
            if before not in '<>!:'and after not in '=>?':equality=True
    return equality and bool(re.search(r'\b'+re.escape(observer)+r'\b',conclusion))


def plan(binding):
    if binding.get('transfer_mode','queue')!='queue':raise ValueError('nonempty queue mode required')
    data=records.plan(binding);root=records.projection.pipeline.adapter.ROOT
    sources={m:(root/'src'/Path(*m.split('.')).with_suffix('.v')).read_text()for m in data['source_sha256']}
    defs=[dict(module=m,**d)for m,s in sources.items()for d in definitions(s)]
    rows=[dict(module=m,**r)for m,s in sources.items()for r in declarations(s)]
    record_names={r['symbol'].split('.')[-1]for r in data['records']}
    domains=record_names&set(re.findall(r'[A-Za-z_][A-Za-z0-9_]*',binding['binders']))
    physical=binding['physical']['symbol'].split('.')[-1]
    excluded=lambda r:bool(re.search(r'\b'+re.escape(physical)+r'\b',r['statement']))or any(
        t in r['statement']for t in ('QueueTransfer','LocalCycleTransfers','Certificate','OrderedCycleSafety'))
    advance=[r for r in rows if not excluded(r)and 'exists'in r['statement']and
             any(re.search(r'\b'+name+r'\b',r['statement'])for name in domains)and
             any(len(re.findall(r'\b'+name+r'\b',r['statement']))>=2 for name in record_names-domains)]
    if len(advance)!=1:raise ValueError('exactly one lower record frontier transition required; no old-transfer fallback')
    target_name=binding['target']['symbol'].split('.')[-1]
    target=[d for d in defs if d['symbol'].split('.')[-1]==target_name]
    if len(target)!=1:raise ValueError('ambiguous original target definition')
    observer=re.search(r'\btarget_commits\s*:=\s*([A-Za-z_][A-Za-z0-9_.]*)',target[0]['command'])
    step=re.search(r'\btarget_cycle\s*:=\s*([A-Za-z_][A-Za-z0-9_.]*)',target[0]['command'])
    if not observer or not step:raise ValueError('unsupported original queue target shape')
    observer=observer.group(1).split('.')[-1];step=step.group(1).split('.')[-1]
    observations=[r for r in rows if not excluded(r)and observation_equality(r['statement'],observer)]
    erasers=[r for r in rows if not excluded(r)and r['statement'].count('EffectChain')>=2 and
             'checked_pc_effect'in r['statement']]
    if len(observations)>24 or len(erasers)>16:raise ValueError('queue helper budget exceeded')
    opaque_names={observer}
    for row in data['records']:
        for field in row['fields']:
            if not re.search(r'\bmap\s+fst\b',field['type']):continue
            match=re.search(r'=\s*([A-Za-z_][A-Za-z0-9_.]*)\s+\w+\s*$',field['type'])
            if match:opaque_names.add(match.group(1).split('.')[-1])
    opaque=[d for d in defs if d['symbol'].split('.')[-1]in opaque_names]
    pending_name=binding['pending']['symbol'].split('.')[-1]
    pending=[d for d in defs if d['symbol'].split('.')[-1]==pending_name]
    for row in list(pending):
        body=row['command'].split(':=',1)[-1]
        pending += [d for d in defs if '++'in d['command']and re.search(r'\b'+d['symbol'].split('.')[-1]+r'\b',body)]
    step_defs=[d for d in defs if d['symbol'].split('.')[-1]==step]
    mappers=[d for d in defs if 'SilentCycle'in d['command']and 'OneCommit'in d['command']and 'TwoCommits'in d['command']
             and ':='in d['command']and 'target_'not in d['command']]
    reductions={d['symbol']:d for d in [*target,*pending,*step_defs,*mappers]}
    return dict(records=data,advance=advance,observations=observations,erasers=erasers,
                opaque=opaque,reductions=list(reductions.values()),old_local_transfer_witness_used=False)


def render(binding):
    data=plan(binding);_,source=records.render(binding)
    source=source.split('Theorem structural_architecture')[0]
    owners={r['module']for r in data['advance']+data['observations']+data['erasers']+data['opaque']+data['reductions']}
    source=source.replace('Module GeneratedArchitecturalProjection.',
        'Require Import Ex.External.CPUGeneratedQueueCut '+' '.join(sorted(owners))+'.\nModule GeneratedLocalCycle.',1)
    term=lambda node:render_proof_argument(node,binding['arguments'])
    target,pending,physical=[term(binding[key])for key in ('target','pending','physical')]
    used=set(binding['arguments']);names=[]
    for base in ('runtime','retired','frontier','physical_evidence','whole_chain'):
        name=base
        while name in used:
            name = '{}_'.format(name)
        used.add(name);names.append(name)
    runtime,retired,frontier,hp,hc=names
    source+=SATURATION_RULES
    rules={'advance':[], 'observation':[], 'erase':[]}
    for kind,group in (('advance',data['advance']),('observation',data['observations']),('erase',data['erasers'])):
      for row in group:
        wanted=None
        if kind!='observation':
            body=without_leading_lets(relations.type_body(row['statement']))
            premise=relations.implication_parts(body)[0].split()[0]
            if '.'in premise:wanted=row['symbol'].rsplit('.',1)[0]+'.'+premise
            else:
                matches=[r['symbol']for r in data['records']['records']if r['symbol'].split('.')[-1]==premise]
                if len(matches)!=1:raise ValueError('ambiguous queue rule premise head')
                wanted=matches[0]
        for count in range(len(binding['arguments'])+1):
            application=row['symbol']+' '+' '.join(binding['arguments'][:count])
            if kind=='observation':
                branch='let rule := constr:('+application+') in let signature := type of rule in '
                branch+='lazymatch signature with forall _ : ?Expected, _ => match goal with H : ?Actual |- _ => '
                branch+='constr_eq Expected Actual; GeneratedRecordRules.apply_to_fact rule H end end'
            else:
                branch='match goal with H : ?T |- _ => let head := record_head T in '
                branch+='let wanted := constr:(@'+wanted+') in constr_eq head wanted; '
                branch+='GeneratedRecordRules.apply_to_fact constr:('+application+') H end'
            rules[kind].append(branch)
    parameters=' '.join(binding['arguments'])
    # Advancing a real cycle is NOT a saturation rule. In particular the
    # post-state invariant must never be fed back into the cycle theorem.
    for kind in ('advance','observation','erase'):
        source+='Ltac queue_'+kind+' '+parameters+' := first [ '+' | '.join(rules[kind])+' ].\n'
    source+='Ltac queue_fields := GeneratedQueueSearch.saturate constr:(128%nat) ltac:(fun _ => first [GeneratedRecordRules.conjunction_fact | record_conjunction_alias | record_projection_step | record_unary_step]).\n'
    source+='Ltac queue_chains '+parameters+' := GeneratedQueueSearch.saturate constr:(32%nat) ltac:(fun _ => queue_erase '+parameters+').\n'
    source+='Local Opaque '+' '.join(r['symbol']for r in data['opaque'])+'.\n'
    reductions=' '.join(r['symbol']for r in data['reductions'])
    source+='Ltac queue_eq := cbv beta iota zeta delta ['+reductions+' CPUGeneratedJointITree.CPUGeneratedJointITree.committed_pcs CPUDesignTarget.CPUDesignTarget.target_commits CPUDesignTarget.CPUDesignTarget.target_cycle] in *; repeat rewrite map_app in *; match goal with |- ?G => idtac "QUEUE_EQUALITY" G end; congruence.\n'
    chain='CPUGeneratedJointTemplate.CPUGeneratedJointTemplate.EffectChain'
    effect='CPUGeneratedJointITree.CPUGeneratedJointITree.checked_pc_effect'
    source+='Ltac queue_retired_chain := match goal with H : '+chain+' '+effect+' ?a ?xs ?b |- '+chain+' '+effect+' ?a0 ?ys ?b0 =>\n'
    source+=' unify a a0; unify b b0; eapply (@CPUGeneratedQueueCut.CPUGeneratedQueueCut.chain_on_equal_tokens _ _ _ a xs _ b); [queue_eq |exact H] end.\n'
    source+='Ltac queue_pack fuel := lazymatch fuel with O => fail 0 "queue packing depth" | S ?remaining =>\n'
    source+=' match goal with |- ?G => idtac "QUEUE_PACK_GOAL" G end; lazymatch goal with\n'
    source+=' | |- ex (fun _ : nat => _) => match goal with n:nat |- _ => exists (S n);queue_pack remaining end\n'
    source+=' | |- ex _ => eexists;queue_pack remaining\n'
    source+=' | |- _ /\\ _ => split;queue_pack remaining\n'
    source+=' | |- _ => first [solve [rewrite Nat.iter_succ; first [eassumption | reflexivity]] | eassumption | reflexivity] end end.\n'
    source+='Theorem actual_local_transfer '+binding['binders']+' : CPUGeneratedJointITree.CPUGeneratedJointITree.LocalCycleTransfers ('+target+') ('+pending+') ('+physical+').\nProof.\n'
    source+=' intros '+' '.join(names)+'. destruct '+hp+'.\n'
    unpack='do 64 (try match goal with H : and _ _ |- _ => destruct H | H : exists _, _ |- _ => destruct H end).'
    source+=' '+unpack+'\n try subst '+runtime+'. queue_fields.\n'
    source+=' queue_advance '+parameters+'.\n GeneratedRecordRules.local_implication_fact.\n '+unpack+'\n queue_fields.\n queue_chains '+parameters+'.\n'
    # Observation helpers are closed at the existing cycle witness; no
    # backwards inference of n through Nat.iter is performed.
    for row in data['observations']:
        for count in range(len(binding['arguments'])+1):
            application=row['symbol']+' '+' '.join(binding['arguments'][:count])
            source+=' try match goal with cycle_index : nat |- _ => let value := constr:('+application+' cycle_index) in GeneratedRecordRules.fresh_fact value end.\n'
    source+=' Show.\n'
    source+=' lazymatch goal with HR : '+chain+' '+effect+' '+retired+' ?tokens ?middle |- _ =>\n'
    source+=' lazymatch goal with HK : '+chain+' '+effect+' middle ?kept '+frontier+' |- _ =>\n'
    source+=' lazymatch goal with HA : '+chain+' '+effect+' '+frontier+' ?admitted ?next |- _ =>\n'
    source+=' exists kept,admitted,next; eapply (@CPUGeneratedQueueCut.CPUGeneratedQueueCut.transfer_from_three_cuts _ _ _ _ _ _ _ _ _ _ _ _ _ middle _);\n'
    source+=' [eapply (@CPUGeneratedQueueCut.CPUGeneratedQueueCut.chain_on_equal_tokens _ _ _ '+retired+' tokens _ middle); [queue_eq|exact HR] |exact HK|exact HA|queue_eq|queue_eq|unfold '+binding['physical']['symbol']+';queue_pack constr:(32%nat)] end end end.\n'
    source+='Qed.\nEnd GeneratedLocalCycle.\nPrint Assumptions GeneratedLocalCycle.actual_local_transfer.\n'
    return dict(**data,transfer_kind='actual_nonempty_queue'),source
