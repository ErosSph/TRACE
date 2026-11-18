#!/usr/bin/env python3
"""Opt-in binary-concretization candidate for source X/Z literals.

Unknown bits become explicit read-only inputs, never zero defaults.  This is
NOT a proved simulation of four-state SV: propagation, guard interpretation
and cross-delta choice history still require a definedness/soundness proof.
The default frontend and runtime semantics are unchanged.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import xml.etree.ElementTree as ET
from cpu_array_frontend import ArrayTranslator
from cv32e40p_extended_frontend import SignalInfo, loc_line, write_coq

def unknown_literal(text):
    match=re.fullmatch(r"(\d+)'(s?)([bh])([0-9a-fxz?_]+)",text.lower())
    if not match or not any(c in match[4] for c in 'xz?'):
        return None
    width,signed,base,digits=match.groups()
    width=int(width)
    if width<=0:raise ValueError('unknown literal width must be positive')
    digits=digits.replace('_','')
    bits=''
    for digit in digits:
        if digit in 'xz?':bits+=digit*(4 if base=='h' else 1)
        elif base=='h':bits+=format(int(digit,16),'04b')
        elif digit in '01':bits+=digit
        else:raise ValueError(f'invalid binary literal digit {digit}')
    # SV sized literals with leading X/Z extend that unknown digit to width.
    padding=bits[0] if bits[0] in 'xz?' else '0'
    bits=(padding*max(0,width-len(bits))+bits)[-width:]
    known_mask=known_value=0
    for bit in bits:
        known_mask=(known_mask<<1)|(bit in '01')
        known_value=(known_value<<1)|(bit=='1')
    return {'width':width,'signed':bool(signed),'bits':bits,
            'known_mask':known_mask,'known_value':known_value,
            'unknown_mask':((1<<width)-1)^known_mask}

class UnknownInputTranslator(ArrayTranslator):
    def __init__(self,root,top):
        super().__init__(root,top)
        self.unknown_sites=[]
        self._unknown_cache={}
        self._instance=top
        self._module=top
        self._parents={child:parent for parent in root.iter() for child in parent}
        self._empty_tasks={(name,t.get('name')) for name,module in self.modules.items()
            for t in module.findall('task')
            if len(t)==1 and t[0].tag=='begin' and len(t[0])==0}

    def instantiate(self,module_name,path):
        previous=self._instance
        old_module=self._module
        self._instance=path
        self._module=module_name
        try:return super().instantiate(module_name,path)
        finally:self._instance=previous;self._module=old_module

    def module_items(self,node,env,path):
        proxy=ET.Element(node.tag,node.attrib)
        for child in node:
            if child.tag=='task' and (self._module,child.get('name')) in self._empty_tasks:
                self.runtime_tags['empty_task_declaration_checked']+=1
            else:proxy.append(child)
        return super().module_items(proxy,env,path)

    def stmt(self,node,env):
        if node.tag=='taskref':
            if len(node)==0 and (self._module,node.get('name')) in self._empty_tasks:
                self.runtime_tags['empty_task_call_inlined']+=1
                return 'SSkip'
            raise ValueError(f'nonempty/unresolved task needs a semantics certificate at {node.get("loc")}')
        return super().stmt(node,env)

    def source_context(self,node):
        contexts=[]
        child=node
        while child in self._parents:
            parent=self._parents[child]
            if parent.tag in {'assign','assigndly'} and len(parent)==2:
                contexts.append({'kind':parent.tag,'loc':parent.get('loc'),
                   'destination_xml':ET.tostring(parent[-1],encoding='unicode')})
            if parent.tag=='if' and len(parent):
                position=list(parent).index(child)
                contexts.append({'kind':'if','loc':parent.get('loc'),
                   'position':position,'guard_xml':ET.tostring(parent[0],encoding='unicode')})
            if parent.tag=='caseitem':
                contexts.append({'kind':'caseitem','loc':parent.get('loc'),
                   'keys_xml':[ET.tostring(c,encoding='unicode') for c in parent
                              if c.tag=='const']})
            if parent.tag=='case' and len(parent):
                contexts.append({'kind':'case','loc':parent.get('loc'),
                   'selector_xml':ET.tostring(parent[0],encoding='unicode'),
                   'ordered_keys_xml':[[ET.tostring(c,encoding='unicode') for c in list(item)[:-1]]
                                       for item in parent.findall('caseitem')]})
            if parent.tag=='always':
                contexts.append({'kind':'always','loc':parent.get('loc')})
                break
            child=parent
        return contexts

    def expr(self,node,env):
        if node.tag=='redand':
            body=list(node)[0]
            self.runtime_tags['redand_as_all_ones_equality']+=1
            return (f'EBinary {self.width(node)} BEq ({self.expr(body,env)}) '
                    f'(EConst {self.width(body)} {(1<<self.width(body))-1})')
        if node.tag=='const':
            literal=unknown_literal(node.get('name',''))
            if literal:
                width=self.width(node)
                if width!=literal['width']:
                    raise ValueError('unknown literal context width mismatch needs extension certificate')
                key=(self._instance,id(node))
                if key not in self._unknown_cache:
                    sid=len(self.signals)
                    site=len(self.unknown_sites)
                    signal=SignalInfo(sid,width,f'{self._instance}.$unknown_{site}',
                                      loc_line(node),'arbitrary_input')
                    self.signals.append(signal)
                    record={'site':site,'signal_id':sid,'instance':self._instance,
                            'literal':node.get('name'),'loc':node.get('loc'),**literal,
                            'source_context':self.source_context(node),
                            'choice_scope':'per physical phase; fixed during its LFP settling',
                            'required_obligation':'observable definedness / independence, not assumed'}
                    self._unknown_cache[key]=record
                    self.unknown_sites.append(record)
                record=self._unknown_cache[key]
                self.runtime_tags['explicit_unknown_input']+=1
                return (f'EBinary {width} BOr (EConst {width} {literal["known_value"]}) '
                        f'(EBinary {width} BAnd (EVar {width} {record["signal_id"]}) '
                        f'(EConst {width} {literal["unknown_mask"]}))')
        return super().expr(node,env)

    def unknown_proof_obligations(self):
        # Source dependency graph is conservative: simultaneous/blocking
        # order is deliberately not treated as a proof of kill/overwrite.
        graph={}
        for proc in self.process_meta:
            for source in proc['readers']:
                for destination in proc['writers']:
                    graph.setdefault(source,set()).add(destination)
        precise={}
        signal_ids={s.path:s.id for s in self.signals}
        def expression_reads(node,instance):
            result={signal_ids[f'{instance}.{v.get("name")}'] for v in node.iter('varref')
                    if f'{instance}.{v.get("name")}' in signal_ids}
            for constant in node.iter('const'):
                site=self._unknown_cache.get((instance,id(constant)))
                if site:result.add(site['signal_id'])
            return result
        def collect_module(name,instance):
            module=self.modules[name]
            for assignment in module.iter():
                if assignment.tag not in {'assign','assigndly','contassign'} or len(assignment)!=2:continue
                rhs,lhs=list(assignment)
                references=list(lhs.iter('varref'))
                if not references:continue
                destination=signal_ids.get(f'{instance}.{references[0].get("name")}')
                if destination is None:continue
                reads=expression_reads(rhs,instance)
                # Lvalue offsets and ancestor branch guards affect a write.
                for part in list(lhs)[1:]:reads.update(expression_reads(part,instance))
                child=assignment
                while child in self._parents:
                    parent=self._parents[child]
                    if parent.tag=='if' and len(parent):reads.update(expression_reads(parent[0],instance))
                    if parent.tag=='case':
                        reads.update(expression_reads(parent[0],instance))
                        for item in parent.findall('caseitem'):
                            for key in list(item)[:-1]:reads.update(expression_reads(key,instance))
                    if parent is module:break
                    child=parent
                for read in reads:precise.setdefault(read,set()).add(destination)
            for inst in module.findall('instance'):
                collect_module(inst.get('defName'),f'{instance}.{inst.get("name")}')
        collect_module(self.top,self.top)
        for proc in self.process_meta:
            if proc['origin'].startswith('port_'):
                for read in proc['readers']:
                    precise.setdefault(read,set()).update(proc['writers'])
        sinks=[s for s in self.signals if s.path.endswith((
            '.cpuregs','.reg_pc','.reg_next_pc','.cpuregs_write','.latched_rd','.mem_addr'))]
        for site in self.unknown_sites:
            root=site['signal_id']
            queue=[root];prev={root:None}
            for source in queue:
                for dest in graph.get(source,()):
                    if dest not in prev:
                        prev[dest]=source;queue.append(dest)
            paths=[]
            for sink in sinks:
                if sink.id not in prev:continue
                path=[];current=sink.id
                while current is not None:
                    path.append(current);current=prev[current]
                paths.append({'sink':sink.path,'signal_path':list(reversed(path))})
            site['conservative_observable_paths']=paths
            queue=[root];prev={root:None}
            for source in queue:
                for dest in precise.get(source,()):
                    if dest not in prev:prev[dest]=source;queue.append(dest)
            paths=[]
            for sink in sinks:
                if sink.id not in prev:continue
                path=[];current=sink.id
                while current is not None:path.append(current);current=prev[current]
                paths.append({'sink':sink.path,'signal_path':list(reversed(path))})
            site['assignment_guard_dependency_paths']=paths
            site['dependency_path_status']='static overapproximation; no overwrite/guard satisfiability proof'
            site['writer_processes']=[p for p in self.process_meta if root in p['readers']]
        return self.unknown_sites

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--xml',type=Path,required=True)
    parser.add_argument('--top',required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--module',default='PicoUnknownInputAST')
    parser.add_argument('--prefix',default='pico_unknown')
    parser.add_argument('--namespace',default='PicoUnknown')
    args=parser.parse_args()
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    pinned=json.loads((args.xml.parent/'report.json').read_text())
    digest=hashlib.sha256(args.xml.read_bytes()).hexdigest()
    if pinned.get('xml_sha256')!=digest:
        raise ValueError('XML is not pinned by its full elaboration report')
    for item in pinned.get('source_hashes',[]):
        if hashlib.sha256(Path(item['path']).read_bytes()).hexdigest()!=item['sha256']:
            raise ValueError('pinned actual source changed')
    if not pinned.get('source_hashes'):raise ValueError('missing source hashes')
    root=ET.parse(args.xml).getroot()
    tr=UnknownInputTranslator(root,args.top)
    report={'source_xml_sha256':digest,'source_hashes':pinned['source_hashes'],
            'status':'pending','translation_soundness':'NOT_PROVED_FOR_FOUR_STATE_RTL',
            'choice_semantics':'explicit arbitrary inputs, independently chosen each physical phase',
            'soundness_boundary':'requires definedness/observable-independence and initialization/history proofs',
            'missing_valuation_policy':'reject at wrapper; never run raw zero-default inputs as certified execution'}
    try:
        tr.translate()
        source_digest=hashlib.sha256(json.dumps(pinned['source_hashes'],sort_keys=True).encode()).hexdigest()
        write_coq(out/(args.module+'.v'),tr,source_digest,digest,{},args.module,args.prefix)
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',args.namespace):
            raise ValueError('namespace must be a Coq identifier')
        ids='; '.join(str(site['signal_id'])+'%nat' for site in tr.unknown_sites)
        environment='''(** Explicit arbitrary choice boundary; raw missing-input default zero is
    never an accepted valuation. No four-state source soundness is asserted. *)
From Coq Require Import ZArith List Lia.
Require Import Lang.ExtendedSV %(namespace)s.%(module)s.
Import ExtendedSV %(module)s ListNotations.
Module %(module)sEnvironment.
Definition unknown_signals : list signal := [%(ids)s].
Fixpoint install_choices (ids:list signal) (values:list Z) (pre:State)
 {struct ids} : option State := match ids,values with
 | [],[]=>Some pre
 | id::tail,value::rest=>install_choices tail rest (write_signal pre id value)
 | _,_=>None end.
Record ChoiceVector : Type := { choice_values:list Z;
 choice_length:length choice_values=length unknown_signals }.
Definition phase_with_choices (choices:list Z) ev pre : option State :=
 match install_choices unknown_signals choices pre with
 | Some seeded=>Some (PhaseSemantics %(prefix)s_program ev seeded)
 | None=>None end.
Inductive ArbitraryChoicePhase ev pre : State -> Prop :=
| choice_phase : forall choices post,
 phase_with_choices choices ev pre=Some post -> ArbitraryChoicePhase ev pre post.
Lemma install_choices_complete ids values : length values=length ids ->
 forall pre,exists seeded,install_choices ids values pre=Some seeded.
Proof.
 revert values. induction ids as [|id tail IH]; intros [|value rest] H pre;
 try discriminate; [exists pre;reflexivity|].
 cbn in H. apply IH. lia.
Qed.
Theorem supplied_vector_has_phase choices ev pre :
 exists post,phase_with_choices (choice_values choices) ev pre=Some post.
Proof.
 destruct (install_choices_complete unknown_signals (choice_values choices)
   (choice_length choices) pre) as [seeded H].
 exists (PhaseSemantics %(prefix)s_program ev seeded).
 unfold phase_with_choices. rewrite H. reflexivity.
Qed.
Example missing_choices_rejected ev pre : phase_with_choices [] ev pre=None.
Proof. reflexivity. Qed.
Print Assumptions supplied_vector_has_phase.
End %(module)sEnvironment.
''' % {'namespace':args.namespace,'module':args.module,'prefix':args.prefix,'ids':ids}
        (out/(args.module+'Environment.v')).write_text(environment)
        report['coq_ast_sha256']=hashlib.sha256((out/(args.module+'.v')).read_bytes()).hexdigest()
        report['choice_environment_sha256']=hashlib.sha256((out/(args.module+'Environment.v')).read_bytes()).hexdigest()
        report['unknown_sources_have_no_process_writers']=not any(
            site['signal_id'] in proc['writers'] for site in tr.unknown_sites for proc in tr.process_meta)
        report.update(status='complete_runtime_candidate_with_explicit_unknown_inputs_not_refinement',
                      signals=len(tr.signals),processes=len(tr.processes),lfp_fuel=tr.lfp_fuel,
                      signal_table=[vars(s) for s in tr.signals],process_table=tr.process_meta,
                      unknown_sites=tr.unknown_proof_obligations(),features=dict(tr.runtime_tags))
    except (ValueError,KeyError,NotImplementedError) as error:
        report.update(status='unsupported',diagnostic=str(error),partial_unknown_sites=tr.unknown_sites)
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k in {'status','signals','processes','lfp_fuel','diagnostic'}}))
    return 0 if report['status'].startswith('complete_runtime_candidate') else 1

if __name__=='__main__':raise SystemExit(main())
