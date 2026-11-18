"""Simultaneous narrow-field histories with endogenous tags on internal edges.

Only direct same-width copies and actual combinational aliases are supported.
Boundary tokens and lossless validity coverage remain explicit obligations.
"""
import argparse,json,time,hashlib,re
from pathlib import Path
import cpu_pending_projection_origins as p
import cpu_zero_instruction_rf as rf
from cpu_certificate_acceptance import run_stage

def discover(ast,selected_roots=None,raw=None):
    raw=p.discover_narrow_fields(ast)['projections']if raw is None else raw
    rows=[r for r in raw if r['capture']==p.rtl.render(p.rtl.Term('EVar',(p.rtl.Term('5'),p.rtl.Term(str(r['source'])))))
          and sum(q['root']==r['root']for q in raw)==1]
    if selected_roots is not None:rows=[r for r in rows if r['root']in selected_roots]
    byroot={r['root']:i for i,r in enumerate(rows)};edges=[];boundaries=[]
    for i,r in enumerate(rows):
        root=r['source'];path=[];seen=set()
        while root not in byroot and root not in seen:
            seen.add(root);writers=[q for q in ast['processes']if root in q['writers']]
            if len(writers)!=1 or writers[0]['kind']!='Combinational':break
            body=writers[0]['body']
            if body.name!='SAssign'or body.args[0].name!='false':break
            rhs,lhs=body.args[1:]
            if rhs.name!='EVar'or rhs.args[0].name!='5'or lhs.name!='LVar'or lhs.args[0].name!='5':break
            path.append(root);root=int(rhs.args[1].name)
        if root in byroot:edges.append(dict(target=i,source=byroot[root],path=path))
        else:boundaries.append(dict(target=i,root=r['source'],frontier=root,path=path))
    head=None
    if len(boundaries)==1:
        boundary=boundaries[0];root=boundary['frontier']
        writers=[q for q in ast['processes']if root in q['writers']]
        if len(writers)==1 and writers[0]['kind']=='Combinational':
            body=writers[0]['body']
            if body.name=='SAssign'and body.args[0].name=='false'and body.args[2].name=='LVar'and body.args[2].args[0].name=='5':
                leaves=[t for t in p.rtl.walk(body.args[1])if t.name=='EVar']
                sources={int(t.args[1].name)for t in leaves if t.args[0].name=='32'}
                if len(sources)==1 and p.word_only(body.args[1],next(iter(sources))):
                    head=dict(target=boundary['target'],source=next(iter(sources)),expression=p.rtl.render(body.args[1]),
                        aliases=boundary['path'],output=root)
    return dict(rows=rows,edges=edges,boundaries=boundaries,head=head)

def render(ast_path,ast_module,selected_roots=None):
    ast,profile,paths=p.origins.raw_binding(ast_path,ast_module);data=discover(ast,selected_roots)
    if not data['edges']and not data['head']:return None,dict(**data,paths=paths)
    roots={r['root']for r in data['rows']}
    generated,prefix=p.render(ast_path,ast_module,selected_roots=roots,source_mode='narrow_field')
    # Keep the discovery order, which is the generator's order for these roots.
    if [r['root']for r in generated['projections']]!=[r['root']for r in data['rows']]:raise ValueError('projection order mismatch')
    aliases={r for e in data['edges']for r in e['path']}
    if data['head']:aliases.update(data['head']['aliases']+[data['head']['output']])
    _,ports,wires=rf.comb.proposal(profile,aliases)if aliases else (None,dict(ports=[],residuals=[]),'')
    if ports['residuals']:raise ValueError('unsupported actual combinational alias')
    portindex={r['output_root']:i for i,r in enumerate(ports['ports'])}
    program=profile['ast']['program'];rows=data['rows'];n=len(rows)
    edgebytarget={e['target']:e for e in data['edges']}
    lines=['Section FieldChain.','Context {Label:Type}.','Variable value:Label->Z.']
    tagargs=' '.join(f'(tag{i}:option Label)'for i in range(n))
    incomingargs=' '.join(f'(input{i}:option Label)'for i in range(n)if i not in edgebytarget)
    for i,row in enumerate(rows):
        lines += [f'Lemma reference_identity_{i} z:projection_{i}_reference z=norm 5 z.',
            f'Proof. unfold projection_{i}_reference,projection_{i}_capture,capture_value;cbn[eval_expr];rewrite read_signal_write_same,norm_idempotent;reflexivity. Qed.']
    lines += [f'Theorem chain_phase ev pre seed {tagargs} {incomingargs}:',
        f' CombLFP {program} seed(phase_driven_state {program} ev pre) ->']
    for i,row in enumerate(rows):
        lines += [f' changed_signal ev<>{row["root"]}%nat ->',
            f' (forall l,tag{i}=Some l ->norm 5(read_signal pre {row["root"]})=norm 5(value l)) ->']
        if i not in edgebytarget:
            lines += [f' (forall l,input{i}=Some l ->norm 5(read_signal(phase_driven_state {program} ev pre){row["source"]})=norm 5(value l)) ->']
    conclusions=[]
    for i,row in enumerate(rows):
        incoming=f'tag{edgebytarget[i]["source"]}'if i in edgebytarget else f'input{i}'
        conclusions.append(f'(forall l,projection_{i}_origin Label ev pre tag{i} {incoming}=Some l ->norm 5(read_signal(PhaseSemantics {program} ev pre){row["root"]})=norm 5(value l))')
    lines += [' /\\\n'.join(conclusions)+'.','Proof. intro HL.']
    for i in range(n):lines += [f'intros HE{i} HO{i}'+(f' HI{i}.'if i not in edgebytarget else '.')]
    for i,row in enumerate(rows):
        if i in edgebytarget:
            edge=edgebytarget[i];j=edge['source'];src=rows[j]['root']
            lines += [f'assert(HI{i}:forall l,tag{j}=Some l ->norm 5(read_signal(phase_driven_state {program} ev pre){row["source"]})=norm 5(value l)).',
                '{ intros l HT.']
            for root in edge['path']:
                k=portindex[root];lines += [f'rewrite(port_{k}_lfp seed _ HL);unfold port_{k}_rhs;cbn[eval_expr];rewrite norm_idempotent.']
            lines += [f'rewrite(sampled_root_preserved {program} ev pre {src}(history_comb_frame _ _ _ _ _ root_{src}_projection_certificate)HE{j}).',f'exact(HO{j} l HT). }}']
        incoming=f'tag{edgebytarget[i]["source"]}'if i in edgebytarget else f'input{i}'
        lines += [f'assert(HC{i}:{conclusions[i]}). {{ intros l HT.',
            f'pose proof(projection_{i}_actual_phase Label value ev pre tag{i} {incoming} l HE{i})as HP.',
            f'assert(HO:forall x,tag{i}=Some x ->norm 5(read_signal pre {row["root"]})=projection_{i}_reference(value x)).',
            f'{{ intros x HX;rewrite reference_identity_{i};exact(HO{i} x HX). }}',
            f'pose proof(HP HO HI{i} HT)as HX;rewrite reference_identity_{i} in HX;exact HX. }}']
    # Explicit conjunction construction avoids repeat split entering quantified clauses.
    for i in range(n-1):lines += [f'split;[exact HC{i}|].']
    lines += [f'exact HC{n-1}. Qed.','End FieldChain.']
    if data['head']:
        head=data['head'];source=head['source'];out=head['output'];j=portindex[out]
        lines += [f'Definition chain_head_value word:=norm 5(capture_value {source} port_{j}_rhs word).',
            f'Lemma chain_head_inputs:capture_inputs_onlyb {source} port_{j}_rhs=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Theorem chain_head_from_word (Label:Type)(word:Label->Z) ev pre seed (incoming:option Label):',
            f' CombLFP {program} seed(phase_driven_state {program} ev pre) ->',
            f' (forall l,incoming=Some l ->norm 32(read_signal(phase_driven_state {program} ev pre){source})=norm 32(word l)) ->',
            f' forall l,incoming=Some l ->norm 5(read_signal(phase_driven_state {program} ev pre){rows[head["target"]]["source"]})=norm 5(chain_head_value(word l)).',
            'Proof. intros HL HI l HT.']
        for root in head['aliases']:
            k=portindex[root];lines += [f'rewrite(port_{k}_lfp seed _ HL);unfold port_{k}_rhs;cbn[eval_expr];rewrite norm_idempotent.']
        lines += [f'rewrite(port_{j}_lfp seed _ HL). unfold chain_head_value.',
            f'rewrite(capture_value_sound {source} port_{j}_rhs _ (word l)chain_head_inputs(HI l HT)).',
            'rewrite norm_idempotent;reflexivity. Qed.']
        lines += [f'Theorem chain_from_word (Label:Type)(word:Label->Z) ev pre seed {tagargs} (incoming:option Label):',
            f' CombLFP {program} seed(phase_driven_state {program} ev pre) ->']
        for i,row in enumerate(rows):
            lines += [f' changed_signal ev<>{row["root"]}%nat ->',
                f' (forall l,tag{i}=Some l ->norm 5(read_signal pre {row["root"]})=norm 5(chain_head_value(word l))) ->']
        lines += [f' (forall l,incoming=Some l ->norm 32(read_signal(phase_driven_state {program} ev pre){source})=norm 32(word l)) ->',
            ' /\\\n'.join(c.replace('value l','chain_head_value(word l)').replace(f'input{head["target"]}','incoming')for c in conclusions)+'.',
            'Proof. intros HL '+ ' '.join(f'HE{i} HO{i}'for i in range(n))+' HI.',
            f'pose proof(chain_head_from_word Label word ev pre seed incoming HL HI)as HH.',
            'exact(@chain_phase Label (fun l=>chain_head_value(word l)) ev pre seed '+
                ' '.join(f'tag{i}'for i in range(n))+' incoming HL '+
                ' '.join(f'HE{i} HO{i}'+(' HH'if i==head['target']else '')for i in range(n))+'). Qed.']
    if data['head']:
        head=data['head']
        lines += ['Section ChainHistory.', 'Context {Label:Type}.', 'Variable word:Label->Z.',
            'Record ChainTags:=Build_ChainTags {'+';'.join(f'chain_tag{i}:option Label'for i in range(n))+'}.',
            'Definition ChainRelated pre(tags:ChainTags):Prop:=',
            ' /\\ '.join(f'(forall l,chain_tag{i} tags=Some l ->norm 5(read_signal pre {r["root"]})=norm 5(chain_head_value(word l)))'for i,r in enumerate(rows))+'.',
            'Definition advance_tags ev pre(tags:ChainTags)(incoming:option Label):ChainTags:=',
            'Build_ChainTags '+' '.join(f'(projection_{i}_origin Label ev pre(chain_tag{i} tags)'+
                (f'(chain_tag{edgebytarget[i]["source"]} tags))'if i in edgebytarget else ' incoming)')for i in range(n))+'.',
            'Definition ChainBoundary ev pre incoming:Prop:=exists seed,',
            f'CombLFP {program} seed(phase_driven_state {program} ev pre) /\\ '+
            ' /\\ '.join(f'changed_signal ev<>{r["root"]}%nat'for r in rows)+' /\\ ',
            f'(forall l,incoming=Some l ->norm 32(read_signal(phase_driven_state {program} ev pre){head["source"]})=norm 32(word l)).',
            'Lemma chain_history_step ev pre tags incoming:ChainRelated pre tags ->ChainBoundary ev pre incoming ->',
            f'ChainRelated(PhaseSemantics {program} ev pre)(advance_tags ev pre tags incoming).',
            'Proof. destruct tags as['+' '.join(f't{i}'for i in range(n))+'];',
            'unfold ChainRelated;cbn[chain_tag0 '+ ' '.join(f'chain_tag{i}'for i in range(1,n))+' advance_tags];',
            ('intro H0.'if n==1 else 'intros ['+' '.join(f'H{i}'+(' ['if i<n-2 else '')for i in range(n-1))+' H'+str(n-1)+']'*(n-1)+'.'),
            'intros [seed [HL '+''.join(f'[HE{i} 'for i in range(n))+'HI'+']'*(n+2)+'.',
            'exact(chain_from_word Label word ev pre seed '+' '.join(f't{i}'for i in range(n))+' incoming HL '+
            ' '.join(f'HE{i} H{i}'for i in range(n))+' HI). Qed.',
            'Require Import Lang.ExtendedSVHistoryChain.',
            f'Definition ChainExecution:=ExtendedSVHistoryChain.Execution {program} ChainTags (option Label) advance_tags ChainBoundary.',
            'Theorem chain_history_preserved pre tags events post final:',
            'ChainExecution pre tags events post final ->ChainRelated pre tags ->ChainRelated post final.',
            f'Proof. exact(ExtendedSVHistoryChain.preserves {program} ChainTags (option Label) advance_tags ChainBoundary ChainRelated chain_history_step pre tags events post final). Qed.',
            'Theorem chain_history_erases pre tags events post final:',
            f'ChainExecution pre tags events post final ->post=phase_run {program} events pre.',
            f'Proof. exact(ExtendedSVHistoryChain.erases {program} ChainTags (option Label) advance_tags ChainBoundary pre tags events post final). Qed.',
            'End ChainHistory.']
    lines += [
        'Goal True. idtac "FIELD_CHAIN_AUDIT". exact I. Qed.','Print Assumptions chain_phase.']
    if data['head']:lines += ['Print Assumptions chain_head_from_word.','Print Assumptions chain_from_word.','Print Assumptions chain_history_preserved.','Print Assumptions chain_history_erases.']
    return prefix+f'\nLocal Transparent {program}.\n'+wires+f'\nLocal Opaque {program}.\n'+'\n'.join(lines)+'\n',dict(**data,paths=paths)

def check(ast_path,ast_module,output,selected_roots=None):
    output=Path(output);output.mkdir(parents=True,exist_ok=False);source,data=render(ast_path,ast_module,selected_roots)
    report=dict(accepted=False,complete_R_generated=False,isa_identity_proved=False,
        boundary_identity_proved=False,validity_coverage_proved=False,old_inv_read=False,
        edges=data['edges'],boundaries=data['boundaries'],head=data['head'],field_count=len(data['rows']))
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    if source is None:report['status']='no_internal_field_chain'
    else:
        file=output/'FieldChain.v';file.write_text(source);flags=list(p.rtl.framework.FLAGS)
        for row in data['paths']:flags+=['-R',row['directory'],row['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedFieldChain'];start=time.monotonic();deadline=start+1200
        c,t=run_stage([str(p.origins.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],output/'coqc.log',1200)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest())
        if c.returncode==0 and time.monotonic()<deadline:
            marks=list(re.finditer(r'^FIELD_CHAIN_AUDIT\s*$',c.stdout,re.M));tail=c.stdout[marks[-1].end():]if marks else ''
            closed=len(marks)==1 and tail.count('Closed under the global context')==(5 if data['head']else 1) and'Axioms:'not in tail
            k,t=run_stage([str(p.origins.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedFieldChain.FieldChain'],output/'coqchk.log',deadline-time.monotonic())
            report.update(export_assumptions_closed=closed,coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=closed and k.returncode==0)
        report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:parser.add_argument('--'+name,required=True)
    a=parser.parse_args();print(json.dumps(check(a.ast,a.ast_module,a.output),indent=2))
