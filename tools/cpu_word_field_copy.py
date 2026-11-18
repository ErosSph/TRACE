"""Compose an actual word-derived register field with its next direct copy.
No old CPU INV; input-word identity and validity remain explicit obligations.
"""
import argparse,json,re,time,hashlib
from pathlib import Path
import cpu_pending_projection_origins as p
from cpu_certificate_acceptance import run_stage

def discover(ast):
    producers=p.discover(ast)['projections'];consumers=p.discover_narrow_fields(ast)['projections']
    pairs=[]
    for c in consumers:
        if c['capture']!=f'(EVar 5 {c["source"]})':continue
        sources=[r for r in producers if r['root']==c['source']and r['width']==5]
        if len(sources)==1 and sum(r['root']==c['root']for r in consumers)==1:
            pairs.append(dict(producer=sources[0],consumer=c))
    return pairs

def render(ast_path,ast_module):
    ast,profile,paths=p.origins.raw_binding(ast_path,ast_module);pairs=discover(ast)
    program=profile['ast']['program'];sections=[]
    for index,pair in enumerate(pairs):
        a,b=pair['producer'],pair['consumer'];ar,br=a['root'],b['root']
        _,sa=p.render(ast_path,ast_module,{ar},source_mode='instruction')
        _,sb=p.render(ast_path,ast_module,{br},source_mode='narrow_field')
        lines=[f'Module Pair{index}.','Module U.',sa,'End U.','Module D.',sb,'End D.',
            'From Coq Require Import ZArith.',f'Require Import {ast_module}.',
            'Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression Lang.ExtendedSVWordInvariant Lang.ExtendedSVProjectionOrigin.',
            'Import ExtendedSV ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVWordInvariant ExtendedSVProjectionOrigin.',
            f'Local Opaque {program}.',
            'Lemma downstream_reference z:D.projection_0_reference z=norm 5 z.',
            'Proof. unfold D.projection_0_reference,D.projection_0_capture,capture_value;cbn[eval_expr];rewrite read_signal_write_same,norm_idempotent;reflexivity. Qed.',
            'Lemma producer_reference_normalized z:norm 5(U.projection_0_reference z)=U.projection_0_reference z.',
            'Proof. unfold U.projection_0_reference;apply norm_idempotent. Qed.',
            'Theorem word_copy_phase(Label:Type)(word:Label->Z)ev pre(oldproducer oldconsumer incoming:option Label):',
            f'changed_signal ev<>{ar}%nat ->changed_signal ev<>{br}%nat ->',
            f'(forall l,oldproducer=Some l ->norm 5(read_signal pre {ar})=U.projection_0_reference(word l)) ->',
            f'(forall l,oldconsumer=Some l ->norm 5(read_signal pre {br})=U.projection_0_reference(word l)) ->',
            f'(forall l,incoming=Some l ->norm 32(read_signal(phase_driven_state {program} ev pre){a["source"]})=norm 32(word l)) ->',
            f'(forall l,U.projection_0_origin Label ev pre oldproducer incoming=Some l ->norm 5(read_signal(PhaseSemantics {program} ev pre){ar})=U.projection_0_reference(word l)) /\\',
            f'(forall l,D.projection_0_origin Label ev pre oldconsumer oldproducer=Some l ->norm 5(read_signal(PhaseSemantics {program} ev pre){br})=U.projection_0_reference(word l)).',
            'Proof. intros HEU HED HU HD HI;split.',
            '- intros l HT;exact(U.projection_0_actual_phase Label word ev pre oldproducer incoming l HEU HU HI HT).',
            '- intros l HT.',
            'assert(Hold:forall x,oldconsumer=Some x ->norm 5(read_signal pre '+str(br)+')=D.projection_0_reference(U.projection_0_reference(word x))).',
            '{ intros x HX;rewrite downstream_reference,producer_reference_normalized;exact(HD x HX). }',
            f'assert(Hinput:forall x,oldproducer=Some x ->norm 5(read_signal(phase_driven_state {program} ev pre){ar})=norm 5(U.projection_0_reference(word x))).',
            f'{{ intros x HX;rewrite(sampled_root_preserved {program} ev pre {ar}(history_comb_frame _ _ _ _ _ U.root_{ar}_projection_certificate)HEU),producer_reference_normalized;exact(HU x HX). }}',
            'pose proof(D.projection_0_actual_phase Label (fun x=>U.projection_0_reference(word x)) ev pre oldconsumer oldproducer l HED Hold Hinput HT)as HP.',
            'rewrite downstream_reference,producer_reference_normalized in HP;exact HP. Qed.',f'End Pair{index}.']
        sections+=lines
    sections+=['Goal True. idtac "WORD_FIELD_COPY_AUDIT". exact I. Qed.']
    sections += [f'Print Assumptions Pair{i}.word_copy_phase.'for i in range(len(pairs))]
    return ('\n'.join(sections)+'\n'if pairs else None),dict(pairs=pairs,paths=paths)

def check(ast_path,ast_module,output):
    output=Path(output);output.mkdir(parents=True,exist_ok=False);source,data=render(ast_path,ast_module)
    report=dict(accepted=False,old_inv_read=False,complete_R_generated=False,isa_identity_proved=False,
        validity_coverage_proved=False,pairs=[dict(producer=x['producer']['root'],consumer=x['consumer']['root'])for x in data['pairs']])
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    if source is None:report['status']='no_word_field_copy_pair'
    else:
        file=output/'WordFieldCopy.v';file.write_text(source);flags=list(p.rtl.framework.FLAGS)
        for row in data['paths']:flags+=['-R',row['directory'],row['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedWordFieldCopy'];start=time.monotonic();deadline=start+1200
        c,t=run_stage([str(p.origins.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],output/'coqc.log',1200)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest())
        if c.returncode==0 and time.monotonic()<deadline:
            marks=list(re.finditer(r'^WORD_FIELD_COPY_AUDIT\s*$',c.stdout,re.M));tail=c.stdout[marks[-1].end():]if marks else ''
            closed=len(marks)==1 and tail.count('Closed under the global context')==len(data['pairs'])and'Axioms:'not in tail
            k,t=run_stage([str(p.origins.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedWordFieldCopy.WordFieldCopy'],output/'coqchk.log',deadline-time.monotonic())
            report.update(export_assumptions_closed=closed,coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=closed and k.returncode==0)
        report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:parser.add_argument('--'+name,required=True)
    a=parser.parse_args();print(json.dumps(check(a.ast,a.ast_module,a.output),indent=2))
