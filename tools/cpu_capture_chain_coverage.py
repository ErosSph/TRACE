"""Infer and prove validity coverage for endogenous capture/field histories.

Relations are reconstructed from raw wiring. Never accept unknown-origin
branches as empty valid slots. This does not prove ISA order or losslessness.
"""
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_capture_field_chain as capture
import cpu_pending_recipe_coverage as coverage
from cpu_certificate_acceptance import run_stage

def relations(data):
    if data['connection'] is None:return None
    chain=data['chain'];edges={e['target']:e['source']for e in chain['edges']}
    rows=[dict(r,source=chain['rows'][edges[i]]['root']if i in edges
        else data['connection']['capture']['carrier'])for i,r in enumerate(chain['rows'])]
    return dict(direct_origins=rows,connected_origins=[],copy_edges=[])

def render(ast_path,ast_module,selected_roots=None):
    ast,profile,paths=capture.birth.origin.raw_binding(ast_path,ast_module)
    data=capture.discover(ast,selected_roots);rs=relations(data)
    if rs is None:return None,dict(status='no_capture_field_chain_connection',paths=paths)
    cov=coverage.discover(ast,relations=rs)
    rows=data['chain']['rows'];byroot={r['root']:(i,r)for i,r in enumerate(cov['covered_fields'])}
    if any(r['root']not in byroot for r in rows):
        return None,dict(status='incomplete_chain_validity',coverage=cov,paths=paths)
    source,_=capture.render(ast_path,ast_module,selected_roots)
    _,vs=coverage.render(ast_path,ast_module,relations=rs)
    p=profile['ast']['program'];b=data['connection']['capture'];n=len(rows)
    edges={e['target']:e['source']for e in data['chain']['edges']}
    vals=[byroot[r['root']][1]['valid_root']for r in rows]
    lines=[f'Local Transparent {p}.','Module V.',vs,'End V.',f'Local Opaque {p}.',
        'Definition SlotCoverage pre(tags:@C.ChainTags Token):Prop:=',
        ' /\\ '.join(f'(norm 1(read_signal pre {v})<>0%Z ->exists l,C.chain_tag{i} tags=Some l)'for i,v in enumerate(vals))+'.',
        'Definition CoveredCapturedFields pre(packed:Packed):=CapturedFields pre packed /\\ SlotCoverage pre(snd packed).',
        'Definition CoveredBoundary ev pre(unused:unit):Prop:=CaptureFieldBoundary ev pre unused /\\ '+
        ' /\\ '.join(f'changed_signal ev<>{v}%nat'for v in vals)+'.',
        'Lemma covered_capture_step ev pre packed unused:CoveredCapturedFields pre packed ->CoveredBoundary ev pre unused ->',
        f'CoveredCapturedFields(PhaseSemantics {p} ev pre)(advance_capture_fields ev pre packed unused).',
        'Proof. destruct packed as[g tags];intros[Hrel Hslots][HB HVs].',
        'split;[exact(capture_fields_step ev pre (g,tags)unused Hrel HB)|].',
        'destruct Hrel as[HI HR].',
        'destruct HB as[seed [HL [HE [HV '+''.join(f'[HE{i} 'for i in range(n-1))+f'HE{n-1}'+']'*(n+3)+'.',
        'unfold SlotCoverage in Hslots;cbn[snd]in Hslots.',
        ('rename Hslots into H0.'if n==1 else 'destruct Hslots as['+''.join(f'H{i} ['for i in range(n-2))+f'H{n-2} H{n-1}'+']'*(n-1)+'.'),
        ('rename HVs into HV0.'if n==1 else 'destruct HVs as['+''.join(f'HV{i} ['for i in range(n-2))+f'HV{n-2} HV{n-1}'+']'*(n-1)+'.'),
        'destruct(proj1 HI)as[Hbirth Hword].']
    for i,r in enumerate(rows):
        k,covered=byroot[r['root']]
        if i in edges:
            j=edges[i];incoming=f'(C.chain_tag{j} tags)';inp=f'H{j}';evinp=f'HV{j}'
        else:incoming='(current g)';inp='Hbirth';evinp='HV'
        lines += [f'pose proof(V.coverage_{k}_actual_phase Token seed ev pre(C.chain_tag{i} tags){incoming} HV{i} {evinp} HL H{i} {inp})as HP{i}.']
    lines += ['unfold SlotCoverage;cbn[snd advance_capture_fields C.advance_tags '+
        ' '.join(f'C.chain_tag{i}'for i in range(n))+'].']
    for i in range(n-1):lines += [f'split;[exact HP{i}|].']
    lines += [f'exact HP{n-1}. Qed.',
        f'Definition CoveredExecution:=ExtendedSVHistoryChain.Execution {p} Packed unit advance_capture_fields CoveredBoundary.',
        'Theorem covered_capture_history pre packed events post final:CoveredExecution pre packed events post final ->CoveredCapturedFields pre packed ->CoveredCapturedFields post final.',
        f'Proof. exact(ExtendedSVHistoryChain.preserves {p} Packed unit advance_capture_fields CoveredBoundary CoveredCapturedFields covered_capture_step pre packed events post final). Qed.',
        f'Theorem covered_capture_erases pre packed events post final:CoveredExecution pre packed events post final ->post=phase_run {p} events pre.',
        f'Proof. exact(ExtendedSVHistoryChain.erases {p} Packed unit advance_capture_fields CoveredBoundary pre packed events post final). Qed.',
        'Goal True. idtac "COVERED_CAPTURE_AUDIT". exact I. Qed.',
        'Print Assumptions covered_capture_step.','Print Assumptions covered_capture_history.','Print Assumptions covered_capture_erases.']
    def component(name,i):
        for _ in range(i):name=f'(proj2 {name})'
        return name if i==n-1 else f'(proj1 {name})'
    for i,row in enumerate(rows):
        lines += [f'Theorem valid_field_{i}_has_value pre packed:',
            'CoveredCapturedFields pre packed ->',
            f'norm 1(read_signal pre {vals[i]})<>0%Z ->exists token,',
            f'C.chain_tag{i}(snd packed)=Some token /\\',
            f'norm 5(read_signal pre {row["root"]})=norm 5(C.chain_head_value(token_word token)).',
            'Proof. intros [[HB HR]HV] Hvalid.',
            f'destruct({component("HV",i)} Hvalid)as[token HT];exists token;split;[exact HT|].',
            f'exact({component("HR",i)} token HT). Qed.',
            f'Print Assumptions valid_field_{i}_has_value.']
    return source+'\n'+'\n'.join(lines)+'\n',dict(paths=paths,coverage=cov,valid_roots=vals,audited_exports=3+n)

def check(ast_path,ast_module,output,selected_roots=None):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    source,data=render(ast_path,ast_module,selected_roots)
    report=dict(accepted=False,old_inv_read=False,complete_R_generated=False,isa_admission_proved=False,
        selected_roots=None if selected_roots is None else sorted(selected_roots),
        admitted_token_losslessness_proved=False,initialization_proved=False)
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    if source is None:report['status']=data['status']
    else:
        file=output/'CoveredCapture.v';file.write_text(source);flags=list(capture.chain.p.rtl.framework.FLAGS)
        for row in data['paths']:flags+=['-R',row['directory'],row['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedCoveredCapture'];start=time.monotonic();deadline=start+1200
        c,t=run_stage([str(capture.birth.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],output/'coqc.log',1200)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest())
        if c.returncode==0 and time.monotonic()<deadline:
            marks=list(re.finditer(r'^COVERED_CAPTURE_AUDIT\s*$',c.stdout,re.M));tail=c.stdout[marks[-1].end():]if marks else ''
            closed=len(marks)==1 and tail.count('Closed under the global context')==data['audited_exports'] and 'Axioms:'not in tail
            k,t=run_stage([str(capture.birth.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedCoveredCapture.CoveredCapture'],output/'coqchk.log',deadline-time.monotonic())
            report.update(export_assumptions_closed=closed,coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=closed and k.returncode==0)
        report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:parser.add_argument('--'+name,required=True)
    parser.add_argument('--roots',type=int,nargs='+')
    a=parser.parse_args();print(json.dumps(check(a.ast,a.ast_module,a.output,None if a.roots is None else set(a.roots)),indent=2))
