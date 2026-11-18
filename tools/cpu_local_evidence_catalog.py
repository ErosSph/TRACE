"""Discover local certificate witnesses from declaration types, not role maps.

This is checked evidence reuse, NOT invention of architectural invariants or
proofs from RTL. Only explicitly imported source modules are searched. A fixed
type vocabulary selects candidate declarations; Coq must discharge every slot.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import re
from pathlib import Path
import cpu_auto_adapter as adapter
from cpu_joint_search import render_search, MAX_CANDIDATES
from cpu_joint_synthesis import render as render_joint
from cpu_certificate_acceptance import render_proof_argument


def commands(source):
    """Split Coq commands, ignoring nested comments and quoted punctuation."""
    clean=[]; depth=0; quoted=False; i=0
    while i<len(source):
        pair=source[i:i+2]; c=source[i]
        if depth:
            if pair=='(*': depth+=1; i+=2; continue
            if pair=='*)': depth-=1; i+=2; clean.append(' '); continue
            if c=='\n': clean.append('\n')
            i+=1; continue
        if quoted:
            if pair=='""': i+=2; continue
            if c=='"': quoted=False
            clean.append(' '); i+=1; continue
        if pair=='(*': depth=1; clean.append(' '); i+=2; continue
        if c=='"': quoted=True; clean.append(' '); i+=1; continue
        clean.append(c); i+=1
    if depth or quoted: raise ValueError('unterminated Coq comment/string')
    text=''.join(clean); start=0
    for match in re.finditer(r'\.(?=\s|$)',text):
        yield text[start:match.start()].strip(); start=match.end()
    if text[start:].strip(): raise ValueError('unterminated Coq command')


def declarations(source):
    scopes=[]
    for command in commands(source):
        command=re.sub(r'^#\[[^]]*\]\s*','',command)
        opened=re.fullmatch(r'(Module(?:\s+Type)?|Section)\s+([A-Za-z_][A-Za-z0-9_]*)',command)
        if opened:
            scopes.append((opened.group(2),opened.group(1).startswith('Module'))); continue
        closed=re.fullmatch(r'End\s+([A-Za-z_][A-Za-z0-9_]*)',command)
        if closed:
            if not scopes or scopes[-1][0]!=closed.group(1): raise ValueError('unbalanced Coq scope')
            scopes.pop(); continue
        # Definitions/global certificates are deliberately not witness candidates.
        match=re.match(r'(?:(?:Global|Local)\s+)?(Lemma|Theorem|Corollary|Proposition)\s+'
                       r'([A-Za-z_][A-Za-z0-9_]*)\b(.*)',command,re.S)
        if match:
            modules=[name for name,is_module in scopes if is_module]
            yield dict(symbol='.'.join(modules+[match.group(2)]), statement=match.group(3).strip())


def categories(statement,physical_name='Physical'):
    # Selection is only an untrusted proposal. Exact types are checked in Coq.
    kinds=[]
    has_physical=re.search(r'\b'+re.escape(physical_name)+r'\b',statement)
    if re.search(r'\btarget_arch_relation\b',statement) and has_physical:
        kinds.append('architecture')
    if (re.search(r'\bLocal(?:Cycle|Streaming|SegmentStreaming)Transfers\b',statement) or
            (re.search(r'\bEffectChain\b',statement) and
             re.search(r'\b(?:QueueTransfer|StreamingTransfer|SegmentStreamingTransfer)\b',statement))):
        kinds.append('local_transfer')
    if re.search(r'\bBoundedProgress\b',statement): kinds.append('bounded_progress')
    if has_physical and not kinds: kinds.append('physical_boundary')
    if (('≈' in statement or re.search(r'\beutt\b',statement)) and
            not re.search(r'\b(?:riscv_itree|riscv_itree_with_state|isa_itree|reference_itree|emit_visible)\b',statement)):
        kinds.append('startup_candidate')
    if re.search(r'=\s*(?:\[\s*\]|nil\b)',statement): kinds.append('empty_queue_candidate')
    return kinds


def direct_target_step(sources,binding):
    """A rigid head hint only; unsupported wrappers stay unclassified."""
    target=binding.get('target',{}).get('symbol')
    if not isinstance(target,str) or not adapter.SYMBOL.fullmatch(target): return None
    heads=set()
    for source in sources:
        for command in commands(source):
            if not re.match(r'Definition\s+'+re.escape(target.split('.')[-1])+r'\b',command):continue
            field=re.search(r'\btarget_cycle\s*:=\s*\(?\s*([A-Za-z_][A-Za-z0-9_.]*)',command)
            if field and field.group(1).split('.')[-1]!='target_cycle':heads.add(field.group(1))
    if len(heads)>1:raise ValueError('ambiguous target cycle head; refusing a guessed adapter')
    return next(iter(heads))if heads else None


def discover(binding,root=None,omit_roles=()):
    root=adapter.ROOT if root is None else Path(root)
    imports=binding.get('imports')
    if not isinstance(imports,list) or not imports or not all(
            isinstance(m,str) and adapter.SYMBOL.fullmatch(m) for m in imports):
        raise ValueError('explicit closed imported-module scope required')
    selected={}; owners={}; excluded=[];sources={}
    physical=binding.get('physical',{}).get('symbol','Physical')
    if not isinstance(physical,str) or not adapter.SYMBOL.fullmatch(physical):
        raise ValueError('closed physical-predicate symbol required')
    for module in imports:
        path=root/'src'/Path(*module.split('.')).with_suffix('.v')
        if not path.is_file(): raise ValueError('import has no supported project source owner: '+module)
        source=path.read_text();sources[path]=source
        owners[str(path.relative_to(root))]=hashlib.sha256(source.encode()).hexdigest()
    step_head=direct_target_step(sources.values(),binding)
    for path,source in sources.items():
        for declaration in declarations(source):
            kinds=categories(declaration['statement'],physical.split('.')[-1])
            if 'startup_candidate'in kinds and step_head:
                actual_heads=re.findall(r'\bordered_scheduler\s*\(?\s*([A-Za-z_][A-Za-z0-9_.]*)',
                                        declaration['statement'])
                if actual_heads and any(head!=step_head for head in actual_heads):
                    kinds.remove('startup_candidate')
                    excluded.append(dict(symbol=declaration['symbol'],reason='different_rigid_scheduler_step_head'))
            if not kinds: continue
            # No wrapper around an existing whole certificate/refinement is indexed.
            if re.search(r'\b(?:Certificate|EntryCertificate|OrderedCycleSafety|OrderedWaitDecreases)\b',
                         declaration['statement']):
                excluded.append(dict(symbol=declaration['symbol'],reason='whole_contract_or_global_safety_progress'));continue
            if binding.get('transfer_mode')=='boundary_entry' and kinds==['bounded_progress']: continue
            symbol=declaration['symbol']
            if symbol in selected and selected[symbol]['statement']!=declaration['statement']:
                raise ValueError('ambiguous exported lemma symbol')
            selected[symbol]=dict(**declaration,categories=kinds,source=str(path.relative_to(root)))
    pool=['eq_refl',*sorted(selected)]
    if len(pool)>MAX_CANDIDATES:
        raise ValueError('automatic witness pool exceeds fixed search budget; no truncation')
    if len(pool)==1: raise ValueError('no local component witnesses discovered')
    slot_kinds={'architecture':'architecture','startup':'startup_candidate',
                'empty_queue':'empty_queue_candidate','boot':'physical_boundary',
                'local_transfer':'local_transfer','bounded_progress':'bounded_progress'}
    if binding.get('transfer_mode')=='boundary_entry':slot_kinds.pop('bounded_progress')
    if not isinstance(omit_roles,(tuple,list))or len(set(omit_roles))!=len(omit_roles)or any(
            role not in {'architecture','local_transfer','bounded_progress'}for role in omit_roles):
        raise ValueError('only separately generated architecture/local_transfer/bounded_progress roles may be omitted')
    for role in omit_roles:
        if role not in slot_kinds:raise ValueError('cannot omit a role absent from this interface')
        slot_kinds.pop(role)
    slots={slot:[k for k in sorted(selected)if kind in selected[k]['categories']]
           for slot,kind in slot_kinds.items()}
    slots['empty_queue'].append('eq_refl')
    return dict(candidates=pool,slot_candidates=slots,inferred_step_head=step_head,
                declarations=[selected[k]for k in sorted(selected)],
                source_sha256=owners,excluded=excluded,manual_role_map_read=False,
                architectural_joint_discovered=False,proofs_created_from_rtl=False)


def render(binding,root=None):
    catalog=discover(binding,root); normalized=copy.deepcopy(binding)
    if any(not symbols for symbols in catalog['slot_candidates'].values()):
        raise ValueError('no discovered witness for required local slot')
    for key in ('proofs','proof_candidates','lemma_candidates'): normalized.pop(key,None)
    normalized['lemma_candidates']=catalog['candidates']
    source=render_search(normalized)
    slots=iter(catalog['slot_candidates'].values());lines=[]
    for line in source.splitlines():
        if 'first [ ' in line:
            symbols=next(slots)
            branches=[branch for symbol in symbols for branch in (
                'solve [ eapply '+symbol+'; eassumption ]',
                'solve [ repeat intro; eapply '+symbol+'; eassumption ]')]
            # Only search order/pool pruning changes; public goals and constructor
            # are the original renderer's exact declarations.
            prefix=line[:line.index('first [ ')]
            line=prefix+'first [ '+' | '.join(branches)+' ].'
        lines.append(line)
    try:next(slots)
    except StopIteration:pass
    else:raise ValueError('not all original slots emitted')
    return catalog,'\n'.join(lines)+'\n'


def component_binding(binding,omit_roles=()):
    """Closed downstream API: every local proof now comes from our checked file."""
    result=copy.deepcopy(binding)
    for key in ('proofs','proof_candidates','lemma_candidates'):result.pop(key,None)
    result['proof_selection']='explicit'
    result['coq_sources']=[]
    result['imports']=[*binding['imports'],'GeneratedLocalCatalog.AutoLocalContract']
    roles=['architecture','startup','empty_queue','boot','local_transfer']
    if binding.get('transfer_mode')!='boundary_entry':roles.append('bounded_progress')
    result['proofs']={role:{'symbol':'GeneratedLocalCatalog.AutoLocalContract.LocalComponentEvidence.component_'+role,
        'arguments':[{'binder':arg}for arg in binding['arguments']]}for role in roles}
    for role in omit_roles:result['proofs'].pop(role)
    return result


def render_components(binding,root=None,omit_roles=()):
    """Generate individually typed reusable witnesses before the ITree assembly."""
    catalog=discover(binding,root,omit_roles)
    if any(not names for names in catalog['slot_candidates'].values()):
        raise ValueError('missing local witness; cannot export an incomplete component API')
    api=component_binding(binding,omit_roles)
    # The file cannot Require itself; its public module is defined immediately
    # before the unchanged certificate constructor consumes these witnesses.
    normalized=copy.deepcopy(api)
    normalized['imports']=binding['imports']
    for proof in normalized['proofs'].values():
        proof['symbol']=proof['symbol'].replace('GeneratedLocalCatalog.AutoLocalContract.','')
    if omit_roles:
        # Reuse only header validation; the partial API intentionally cannot
        # assemble a certificate until the independent providers fill its slots.
        header_binding=copy.deepcopy(normalized)
        for role in omit_roles:header_binding['proofs'][role]={'symbol':'eq_refl'}
        source=render_joint(header_binding).split('Module GeneratedJointContract.')[0]
    else:source=render_joint(normalized)
    term=lambda node:render_proof_argument(node,binding['arguments'])
    target,pending,physical=[term(binding[k])for k in ('target','pending','physical')]
    t='CPUDesignTarget.CPUDesignTarget.'
    scope='CPUGeneratedJointITree.CPUGeneratedJointITree.'
    boundary='CPUGeneratedBoundary.CPUGeneratedBoundary.'
    scheduler='CV32E40PTwoCommitITreeInterface.CV32E40PTwoCommitITreeInterface.ordered_scheduler'
    mode=binding.get('transfer_mode','queue')
    checkpoint=term(binding['entry'])if mode=='boundary_entry'else t+'target_boot ('+target+')'
    used=set(binding['arguments']);fresh=[]
    for base in ('runtime','retired','frontier'):
        name=base
        while name in used:
            name += '_'
        used.add(name);fresh.append(name)
    s,a,f=fresh
    step=t+'target_cycle ('+target+')';observe=t+'target_commits ('+target+')'
    types={
        'architecture':f'forall {s} {a} {f}, ({physical}) {s} {a} {f} -> {t}target_arch_relation ({target}) {s} {a}',
        'startup':f'eutt eq ({scheduler} ({step}) ({observe}) ({t}target_reset ({target}))) '
                  f'({scheduler} ({step}) ({observe}) ({checkpoint}))',
        'empty_queue':f'({pending}) ({checkpoint}) = nil',
        'boot':f'({physical}) ({checkpoint}) ({t}target_isa_initial ({target})) ({t}target_isa_initial ({target}))',
        'local_transfer':(boundary+'LocalSegmentStreamingTransfers'if mode=='boundary_entry'else
                          scope+('LocalStreamingTransfers'if mode=='streaming'else'LocalCycleTransfers'))+
                          f' ({target}) ({pending}) ({physical})'}
    if mode!='boundary_entry':
        types['bounded_progress']='CPUGeneratedProgress.CPUGeneratedProgress.BoundedProgress '+\
            f'({step}) ({observe}) {binding["search_fuel"]} ({scope}GeneratedJoint ({target}) ({pending}) ({physical}))'
    lines=['From ITree Require Import ITree ITreeFacts.',
           'Require Import Ex.External.CPUGeneratedProgress Ex.External.CV32E40PTwoCommitITreeInterface.',
           'Module LocalComponentEvidence.']
    for role,statement in types.items():
        if role in omit_roles:continue
        branches=[branch for symbol in catalog['slot_candidates'][role] for branch in (
            'solve [ eapply '+symbol+'; eassumption ]',
            'solve [ repeat intro; eapply '+symbol+'; eassumption ]')]
        lines += ['Lemma component_'+role+' '+binding['binders']+' : '+statement+'.',
                  'Proof. first [ '+' | '.join(branches)+' ]. Qed.']
    lines+=['End LocalComponentEvidence.']
    marker='Module GeneratedJointContract.'
    if omit_roles:
        source+='\n'.join(lines)+'\n'
        for role in types:
            if role not in omit_roles:
                source+='Print Assumptions LocalComponentEvidence.component_'+role+'.\n'
    else:source=source.replace(marker,'\n'.join(lines)+'\n'+marker,1)
    return catalog,source,api


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True); a=p.parse_args()
    profile=json.loads(a.profile.read_text()); catalog,source=render(profile['joint_binding'])
    a.output.mkdir(parents=True,exist_ok=False)
    (a.output/'AutoLocalContract.v').write_text(source)
    (a.output/'catalog.json').write_text(json.dumps(catalog,indent=2)+'\n')
    print(json.dumps(dict(candidates=len(catalog['candidates']),coq_checked=False)))
