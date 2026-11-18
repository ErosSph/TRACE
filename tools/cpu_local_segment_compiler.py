"""Discover actual run1 segments and compile the original boundary interface."""
from __future__ import annotations
import hashlib,re
from pathlib import Path
import cpu_arch_projection as architecture
from cpu_local_evidence_catalog import declarations
from cpu_certificate_acceptance import render_proof_argument


def render(binding):
    if binding.get('transfer_mode')!='boundary_entry':
        raise ValueError('requires actual boundary-entry segments; no old-transfer fallback')
    header=architecture.render(binding).split('Module GeneratedArchitecturalProjection.')[0]
    candidates=[];source_hashes={}
    physical=binding['physical']['symbol'].split('.')[-1]
    for module in binding['imports']:
        path=architecture.pipeline.adapter.ROOT/'src'/Path(*module.split('.')).with_suffix('.v')
        source=path.read_text();source_hashes[module]=hashlib.sha256(source.encode()).hexdigest()
        for row in declarations(source):
            text=row['statement']
            if all(re.search(r'\b'+word+r'\b',text)for word in ('FirstVisibleCycle','run1',re.escape(physical))):
                if any(word in text for word in ('StreamingTransfer','Certificate','OrderedCycleSafety')):continue
                candidates.append(dict(module=module,**row))
    if len(candidates)!=1:raise ValueError('exactly one actual run1 segment component required; no old-transfer fallback')
    if len(binding['arguments'])>16:raise ValueError('segment parameter budget exceeded')
    term=lambda node:render_proof_argument(node,binding['arguments'])
    target,pending,physical=[term(binding[key])for key in ('target','pending','physical')]
    used=set(binding['arguments']);names=[]
    for base in ('runtime','retired','physical_evidence'):
        name=base
        while name in used:
            name = '{}_'.format(name)
        used.add(name);names.append(name)
    runtime,retired,hypothesis=names
    symbol=candidates[0]['symbol'];branches=[]
    for count in range(len(binding['arguments'])+1):
        prefix=' '.join(binding['arguments'][:count])
        branches.append('let evidence := constr:('+symbol+' '+prefix+
          ' '+runtime+' '+retired+' '+retired+' '+hypothesis+') in '
          'tryif has_evar evidence then fail 0 "unresolved segment parameter" else '
          'let fact := fresh "actual_segment" in pose proof evidence as fact; '
          'segment_unpack fact; solve [segment_pack]')
    source=header+'Require Import Ex.External.CPUGeneratedLocalSegment '+candidates[0]['module']+'.\n'
    source+='Module GeneratedLocalCycle.\n'
    source+='Ltac segment_head term := lazymatch term with ?f ?x => segment_head f | _ => term end.\n'
    source+='Ltac segment_unpack evidence := let T := type of evidence in let head := segment_head T in\n'
    source+=' first [let wanted := constr:(@'+binding['physical']['symbol']+') in unify head wanted |\n'
    source+=' lazymatch T with | exists _, _ => destruct evidence as [? evidence]; segment_unpack evidence\n'
    source+=' | _ /\\ _ => destruct evidence as [? evidence]; segment_unpack evidence end].\n'
    source+='Ltac segment_pack := repeat first [eassumption | match goal with\n'
    source+=' | |- _ /\\ _ => split | |- exists _, _ => eexists end].\n'
    source+='Theorem actual_local_transfer '+binding['binders']+' :\n'
    source+=' CPUGeneratedBoundary.CPUGeneratedBoundary.LocalSegmentStreamingTransfers ('+target+') ('+pending+') ('+physical+').\nProof.\n'
    source+=' eapply (CPUGeneratedLocalSegment.CPUGeneratedLocalSegment.run1_segments_to_streaming ('+target+') ('+pending+') ('+physical+')).\n'
    source+=' - intro '+runtime+'; reflexivity.\n'
    source+=' - intros '+runtime+' '+retired+' '+hypothesis+'. first [ '+' | '.join(branches)+' ].\n'
    source+='Qed.\nEnd GeneratedLocalCycle.\nPrint Assumptions GeneratedLocalCycle.actual_local_transfer.\n'
    return dict(component=candidates[0],source_sha256=source_hashes,
                old_local_transfer_witness_used=False,physical_relation_discovered=False,
                transfer_kind='actual_run1_segments'),source
