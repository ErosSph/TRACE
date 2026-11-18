"""Consume new RTL-generated value and validity proofs in a joint slot rule.

Providers are reconstructed from the raw AST and must match their checked
source/plan/object. No old CPU invariant, pending or theorem catalog is read.
Post-validity entails both a real origin tag and its corresponding field value.
Losslessness, ISA effect and global induction remain separate obligations.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_recipe_coverage as coverage
from cpu_certificate_acceptance import run_stage

origin=coverage.origin;connected=coverage.connected;copies=coverage.metadata


def verify(folder,filename,data,source):
    folder=Path(folder);report=json.loads((folder/'report.json').read_text())
    if not(report.get('accepted')is True and report.get('coqc_exit')==report.get('coqchk_exit')==0
        and report.get('assumptions_closed')is True and report.get('old_inv_read')is False
        and report.get('old_pending_read')is False and report.get('old_cpu_proofs_used',False)is False
        and report.get('global_inv_proved')is False and report.get('itree_refinement_proved')is False
        and report.get('validity_completeness_proved',False)is False
        and report.get('isa_effect_proved',False)is False
        and json.loads((folder/'plan.json').read_text())==data and(folder/filename).read_text()==source
        and report.get('source_sha256')==hashlib.sha256(source.encode()).hexdigest()
        and report.get('object_sha256')==hashlib.sha256((folder/filename).with_suffix('.vo').read_bytes()).hexdigest()):
        raise ValueError('exact current checked raw-generated provider required: '+filename+'; not an old INV')
    return report


def render(ast_path,ast_module,coverage_provider,connected_provider,copy_provider):
    ast,profile,loadpaths=origin.raw_binding(ast_path,ast_module)
    cd,cs=coverage.render(ast_path,ast_module);vd,vs=connected.render(ast_path,ast_module);md,ms=copies.render(ast_path,ast_module)
    reports=[verify(coverage_provider,'RecipeCoverage.v',cd,cs),verify(connected_provider,'ConnectedProjections.v',vd,vs),
        verify(copy_provider,'MetadataCopies.v',md,ms)]
    connections=[]
    for index,row in enumerate(cd['covered_fields']):
        matches=[dict(kind=kind,index=i,row=value)for kind,rows in [('connected',vd['projections']),('copy',md['copy_edges'])]
            for i,value in enumerate(rows)if value['root']==row['root']and value['source']==row['source']
            and value['width']==row['width']and value['recipe']==row['recipe']and value['capture']==row['capture']]
        if len(matches)!=1:raise ValueError('no unique new value proof for a covered field')
        connections.append(dict(coverage_index=index,coverage=row,provider=matches[0]))
    if not connections:raise ValueError('no covered field; no empty INV fallback')
    program=profile['ast']['program'];sources=sorted({r['coverage']['source']for r in connections})
    lines=['From Coq Require Import ZArith List Bool.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVProjectionOrigin Lang.ExtendedSVScalarExpression',
        ' Lang.ExtendedSVRootProjection Lang.ExtendedSVCoveredField',
        f' GeneratedRecipeCoverage.RecipeCoverage GeneratedConnectedProjections.ConnectedProjections GeneratedMetadataCopies.MetadataCopies {ast_module}.',
        'Import ExtendedSV ExtendedSVProjectionOrigin ExtendedSVScalarExpression ExtendedSVRootProjection ExtendedSVCoveredField.',
        'Module C:=GeneratedRecipeCoverage.RecipeCoverage.',
        'Module V:=GeneratedConnectedProjections.ConnectedProjections.',
        'Module M:=GeneratedMetadataCopies.MetadataCopies.']
    for root in sources:
        lines += [f'Lemma source_{root}_frame:comb_root_unwrittenb {program} {root}=true.',
            'Proof. vm_compute. reflexivity. Qed.']
    lines += [f'Local Opaque {program}.']
    for number,item in enumerate(connections):
        row=item['coverage'];i=item['coverage_index'];value=item['provider'];j=value['index'];kind=value['kind']
        root=row['root'];w=row['width'];v=row['valid_root'];src=row['source'];iv=row['source_valid']
        proc=ast['module']+'.'+row['process'];stem=f'field_{number}'
        ref=f'V.connected_{j}_reference(word l)'if kind=='connected'else'reference l'
        ref_label=f'V.connected_{j}_reference(word label)'if kind=='connected'else'reference label'
        param='(word:Label->Z)'if kind=='connected'else'(reference:Label->Z)'
        source_value=f'norm 32(read_signal pre {src})=norm 32(word l)'if kind=='connected'else f'norm {w}(read_signal pre {src})=reference l'
        lines += [f'Definition {stem}_origin(Label:Type)ev pre(old incoming:option Label):=',
            f' @projection_phase_origin Label {program} {proc} C.coverage_{i}_recipe ev pre old incoming.',
            f'Theorem {stem}_valid_value_phase(Label:Type){param}seed ev pre(old incoming:option Label):',
            f' changed_signal ev<>{root}%nat ->changed_signal ev<>{v}%nat ->',
            f' changed_signal ev<>{src}%nat ->changed_signal ev<>{iv}%nat ->',
            f' CombLFP {program} seed(phase_driven_state {program} ev pre) ->',
            f' (norm 1(read_signal pre {v})<>0%Z ->exists label,old=Some label) ->',
            f' (norm 1(read_signal pre {iv})<>0%Z ->exists label,incoming=Some label) ->',
            f' (forall l,old=Some l ->norm {w}(read_signal pre {root})={ref}) ->',
            f' (forall l,incoming=Some l ->{source_value}) ->',
            f' norm 1(read_signal(PhaseSemantics {program} ev pre){v})<>0%Z ->',
            f' exists label,{stem}_origin Label ev pre old incoming=Some label /\\',
            f' norm {w}(read_signal(PhaseSemantics {program} ev pre){root})={ref_label}.',
            'Proof. intros HE HV HS HVS HL HoldCover HinputCover HoldValue HinputValue Hvalid.',
            f' destruct(C.coverage_{i}_actual_phase Label seed ev pre old incoming HV HVS HL HoldCover HinputCover Hvalid)as[label Htag].',
            ' exists label;split;[exact Htag|].']
        if kind=='connected':
            lines += [f' eapply(@V.connected_{j}_actual_phase Label word seed ev pre old incoming label);',
                ' [exact HE|exact HL|exact HoldValue| |exact Htag].',
                f' intros l Hi. rewrite(sampled_root_preserved {program} ev pre {src} source_{src}_frame HS).',
                ' exact(HinputValue l Hi). Qed.']
        else:
            lines += [f' exact(@M.copy_{j}_actual_phase Label reference seed ev pre old incoming label',
                ' HE HS HL HoldValue HinputValue Htag). Qed.']
        lines.append(f'Print Assumptions {stem}_valid_value_phase.')
        source_width=32 if kind=='connected'else w
        source_ref='norm 32(word l)'if kind=='connected'else'reference l'
        lines += [f'Theorem {stem}_relation_phase(Label:Type){param}seed ev pre(old incoming:option Label):',
            f' changed_signal ev<>{root}%nat ->changed_signal ev<>{v}%nat ->',
            f' changed_signal ev<>{src}%nat ->changed_signal ev<>{iv}%nat ->',
            f' CombLFP {program} seed(phase_driven_state {program} ev pre) ->',
            f' @Related Label {w} {root} {v}(fun l=>{ref})old pre ->',
            f' @Related Label {source_width} {src} {iv}(fun l=>{source_ref})incoming pre ->',
            f' @Related Label {w} {root} {v}(fun l=>{ref})({stem}_origin Label ev pre old incoming)',
            f' (PhaseSemantics {program} ev pre).',
            'Proof. intros HE HV HS HVS HL[HoldCover HoldValue][HinputCover HinputValue]. constructor.',
            f' - exact(C.coverage_{i}_actual_phase Label seed ev pre old incoming HV HVS HL HoldCover HinputCover).',
            ' - intros label Htag.']
        if kind=='connected':
            lines += [f' eapply(@V.connected_{j}_actual_phase Label word seed ev pre old incoming label);',
                ' [exact HE|exact HL|exact HoldValue| |exact Htag].',
                f' intros l Hi. rewrite(sampled_root_preserved {program} ev pre {src} source_{src}_frame HS).',
                ' exact(HinputValue l Hi). Qed.']
        else:
            lines += [f' exact(@M.copy_{j}_actual_phase Label reference seed ev pre old incoming label',
                ' HE HS HL HoldValue HinputValue Htag). Qed.']
        lines.append(f'Print Assumptions {stem}_relation_phase.')
    return dict(ast_sha256=ast['source_sha256'],coq_load_paths=loadpaths,connections=connections,
        provider_hashes=[r['object_sha256']for r in reports],audited_exports=2*len(connections),
        old_inv_read=False,old_pending_read=False,validity_completeness_proved=False,
        global_inv_proved=False,itree_refinement_proved=False),'\n'.join(lines)+'\n'


def check(ast_path,ast_module,coverage_provider,connected_provider,copy_provider,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module,coverage_provider,connected_provider,copy_provider)
    except ValueError as error:
        report=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,old_pending_read=False,
            global_inv_proved=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    path=output/'CoveredFields.v';path.write_text(source)
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(coverage.rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    for folder,namespace in[(coverage_provider,'GeneratedRecipeCoverage'),(connected_provider,'GeneratedConnectedProjections'),
        (copy_provider,'GeneratedMetadataCopies'),(output,'GeneratedCoveredFields')]:flags+=['-R',str(Path(folder).resolve()),namespace]
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report=dict(accepted=False,scope='actual post-valid implies both known origin and matching metadata value',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        joint_field_count=len(data['connections']),old_inv_read=False,old_pending_read=False,
        validity_completeness_proved=False,isa_effect_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout
        report['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,
                '-norec','GeneratedRecipeCoverage.RecipeCoverage','-norec','GeneratedConnectedProjections.ConnectedProjections',
                '-norec','GeneratedMetadataCopies.MetadataCopies','-norec','GeneratedCoveredFields.CoveredFields'],
                output/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True)
    p.add_argument('--ast-module',required=True);p.add_argument('--coverage-provider',type=Path,required=True)
    p.add_argument('--connected-provider',type=Path,required=True);p.add_argument('--copy-provider',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    r=check(a.ast,a.ast_module,a.coverage_provider,a.connected_provider,a.copy_provider,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
