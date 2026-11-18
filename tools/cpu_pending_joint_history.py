"""Build a new joint provenance INV from raw RTL, not a CPU proof catalog.

Only freshly reconstructed, exact-checked providers may be consumed. The first
supported schema is one instruction carrier plus an acyclic metadata network.
This proves provenance, not ISA admission/retirement, architectural correctness
or progress. Unsupported schemas are residuals, never an empty INV fallback.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_capture_birth as birth
import cpu_pending_covered_fields as fields
from cpu_certificate_acceptance import run_stage

origin=birth.origin


def layout(births,connections):
    if len(births)!=1:raise ValueError('joint schema requires exactly one supported birth carrier')
    b=births[0];known={b['carrier']:dict(width=32,valid=b['valid_root'],tag='current(joint_birth g)',
        ref='word_reference l',recorded='CaptureRecorded')}
    pending=list(enumerate(connections));slots=[]
    while pending:
        progress=False
        for index,item in list(pending):
            row=item['coverage'];provider=item['provider'];src=known.get(row['source'])
            if src is None:continue
            if row['root']in known:raise ValueError('duplicate or cyclic metadata carrier')
            if src['valid']!=row['source_valid']:raise ValueError('source validity mismatch')
            if provider['kind']=='connected':
                if row['source']!=b['carrier']or src['width']!=32:
                    raise ValueError('derived-on-derived metadata schema needs a new checked rule')
                j=provider['index'];ref=f'V.connected_{j}_reference(token_word l)'
            else:
                if src['width']!=row['width']:raise ValueError('metadata copy width mismatch')
                ref=src['ref']
            slot=dict(index=index,root=row['root'],valid=row['valid_root'],width=row['width'],
                ref=ref,source_tag=src['tag'],kind=provider['kind'],source_recorded=src['recorded'],
                process=row.get('process'),coverage_index=item.get('coverage_index',index))
            slots.append(slot);known[row['root']]=dict(width=row['width'],valid=row['valid_root'],
                tag=f'joint_tag_{index} g',ref=ref,recorded=f'RecordField{index}')
            pending.remove((index,item));progress=True
        if not progress:raise ValueError('metadata graph disconnected from birth or cyclic')
    if not slots:raise ValueError('no metadata network; not a joint-history proof')
    return slots


def render(ast_path,ast_module,birth_provider,coverage_provider,value_provider,copy_provider,field_provider):
    ast,profile,loadpaths=origin.raw_binding(ast_path,ast_module)
    bd,bs=birth.render(ast_path,ast_module)
    br=fields.verify(birth_provider,'CaptureBirth.v',bd,bs)
    fd,fs=fields.render(ast_path,ast_module,coverage_provider,value_provider,copy_provider)
    fr=fields.verify(field_provider,'CoveredFields.v',fd,fs)
    slots=layout(bd['captures'],fd['connections']);b=bd['captures'][0];program=profile['ast']['program']
    roots=sorted({b['carrier'],b['valid_root']}|{r for slot in slots for r in(slot['root'],slot['valid'])})
    validroots=sorted({b['valid_root']}|{slot['valid']for slot in slots})
    if any(p['kind']=='Initial'and any(r in p['writers']for r in validroots)for p in ast['processes']):
        raise ValueError('initial validity writer requires a dedicated initialization certificate')
    lines=['From Coq Require Import ZArith List Bool.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCoveredField',
        ' Lang.ExtendedSVPhaseInstrumentation Lang.ExtendedSVOriginLedger Lang.ExtendedSVCapturedPending',
        ' Lang.ExtendedSVScalarHistory Lang.ExtendedSVConstantRoot Lang.ExtendedSVRootProjection',
        f' GeneratedCaptureBirth.CaptureBirth GeneratedCoveredFields.CoveredFields {ast_module}.',
        'Import ListNotations ExtendedSV ExtendedSVCaptureBirth ExtendedSVCoveredField',
        ' ExtendedSVScalarHistory ExtendedSVConstantRoot ExtendedSVRootProjection ExtendedSVPhaseInstrumentation ExtendedSVOriginLedger ExtendedSVCapturedPending.',
        'Module B:=GeneratedCaptureBirth.CaptureBirth.',
        'Module F:=GeneratedCoveredFields.CoveredFields.',
        'Module V:=GeneratedConnectedProjections.ConnectedProjections.',
        'Module C:=GeneratedRecipeCoverage.RecipeCoverage.',
        'Record JointGhost:Type:={joint_birth:Ghost;']
    lines += [f' joint_tag_{s["index"]}:option Token'+('}.'if k==len(slots)-1 else';')for k,s in enumerate(slots)]
    lines += [f'Local Opaque {program}.',
        'Definition joint_empty:=Build_JointGhost(Build_Ghost 0 None [])'+''.join(' None'for _ in slots)+'.',
        'Definition JointInv(pre:State)(g:JointGhost):=',
        f' Invariant {b["carrier"]} {b["valid_root"]} pre(joint_birth g) /\\']
    for k,s in enumerate(slots):
        lines.append(f' @ExtendedSVCoveredField.Related Token {s["width"]} {s["root"]} {s["valid"]}(fun l=>{s["ref"]})(joint_tag_{s["index"]} g)pre'+
            ('.'if k==len(slots)-1 else' /\\'))
    lines += ['Definition joint_step ev pre(g:JointGhost):=Build_JointGhost',
        ' (B.capture_0_step ev pre(joint_birth g))']
    for k,s in enumerate(slots):
        i=s['index'];lines.append(f' (F.field_{i}_origin Token ev pre(joint_tag_{i} g)({s["source_tag"]}))'+
            ('.'if k==len(slots)-1 else''))
    lines += [f'Definition EventAllowed(ev:Event):=Forall(fun root=>changed_signal ev<>root){roots_coq(roots)}.',
        'Theorem joint_phase seed ev pre g:EventAllowed ev ->',
        f' CombLFP {program} seed(phase_driven_state {program} ev pre) ->JointInv pre g ->',
        f' JointInv(PhaseSemantics {program} ev pre)(joint_step ev pre g).',
        'Proof. intros HE HL HI.',
        ' unfold EventAllowed in HE;repeat match goal with H:Forall _ (_::_) |- _=>inversion H;clear H;subst end.',
        ' unfold JointInv in *;destruct HI as[HB '+nested([f'HistoryField{s["index"]}'for s in slots])+'].',
        ' pose proof(proj1 HB)as BirthWord.',
        ' unfold joint_step;cbn[joint_birth '+ ' '.join(f'joint_tag_{s["index"]}'for s in slots)+'].',
        ' split;[apply B.capture_0_phase;assumption|].']
    for k,s in enumerate(slots):
        parameter='token_word'if s['kind']=='connected'else f'(fun l=>{s["ref"]})'
        proof=f'eapply(F.field_{s["index"]}_relation_phase Token {parameter} seed ev pre);eassumption'
        lines.append(' split;['+proof+'|].'if k<len(slots)-1 else' '+proof+'.')
    lines += ['Qed.',
        f'Definition joint_run events pre g:=@instrumented_run JointGhost {program} joint_step events pre g.',
        'Fixpoint Ready events pre:Prop:=match events with| []=>True|ev::rest=>',
        f' (exists seed,CombLFP {program} seed(phase_driven_state {program} ev pre)) /\\',
        f' Ready rest(PhaseSemantics {program} ev pre)end.',
        'Theorem joint_replay events:Forall EventAllowed events ->forall pre g,Ready events pre ->JointInv pre g ->',
        ' JointInv(fst(joint_run events pre g))(snd(joint_run events pre g)).',
        'Proof. intros HE;induction HE as[|ev rest HA HE IH];intros pre g HR HI;[exact HI|].',
        ' destruct HR as[[seed HL]HR];cbn[joint_run instrumented_run];apply IH;[exact HR|].',
        ' exact(joint_phase seed ev pre g HA HL HI). Qed.',
        f'Theorem joint_erases events:forall pre g,fst(joint_run events pre g)=phase_run {program} events pre.',
        f'Proof. exact(@instrumented_erases JointGhost {program} joint_step events). Qed.',
        f'Local Transparent {program}.']
    for r in validroots:
        lines += [f'Lemma initial_valid_{r}:roots_unwrittenb {r}(filter is_initial(processes {program}))=true.',
            'Proof. vm_compute. reflexivity. Qed.']
    lines += [f'Local Opaque {program}.',
        f'Theorem joint_initialize:JointInv(initialize {program} [])joint_empty.',
        'Proof. unfold JointInv,joint_empty;cbn[joint_birth '+ ' '.join(f'joint_tag_{s["index"]}'for s in slots)+'].',
        ' split;[exact B.capture_0_zero_seed|].']
    for k,s in enumerate(slots):
        prefix=' split;['if k<len(slots)-1 else' '
        suffix='|].'if k<len(slots)-1 else'.'
        lines += [prefix+f'apply invalid_empty_related;rewrite(initialize_unwritten_field {program} {s["valid"]} initial_valid_{s["valid"]} []);reflexivity'+suffix]
    lines.append('Qed.')
    birth_args=f'{program} {ast["module"]}.{b["process"]} {b["carrier"]} B.root_{b["carrier"]}_expression B.root_{b["valid_root"]}_expression B.capture_0_pc ev pre(joint_birth g)'
    lines += ['Definition JointRecorded(g:JointGhost):=CurrentRecorded(joint_birth g) /\\']
    for k,s in enumerate(slots):
        lines.append(f' Recorded(history(joint_birth g))(joint_tag_{s["index"]} g)'+('.'if k==len(slots)-1 else' /\\'))
    lines += ['Definition AuthenticInv pre g:=JointInv pre g /\\JointRecorded g.',
        'Theorem joint_recorded_phase ev pre g:JointRecorded g ->JointRecorded(joint_step ev pre g).',
        'Proof. intro HR;unfold JointRecorded in *;destruct HR as[CaptureRecorded '+nested([f'RecordField{s["index"]}'for s in slots])+'].',
        ' unfold joint_step;cbn[joint_birth '+ ' '.join(f'joint_tag_{s["index"]}'for s in slots)+'].',
        f' split;[exact(ghost_current_recorded {birth_args} CaptureRecorded)|].']
    for k,s in enumerate(slots):
        proof=('eapply recorded_mono with(before:=history(joint_birth g));'
            f'[intros token Hin;exact(ghost_history_preserves {birth_args} token Hin)|'
            f'exact(phase_recorded {program} {ast["module"]}.{s["process"]} C.coverage_{s["coverage_index"]}_recipe'
            f' ev pre(joint_tag_{s["index"]} g)({s["source_tag"]})(history(joint_birth g)) RecordField{s["index"]} {s["source_recorded"]})]')
        lines.append(' split;['+proof+'|].'if k<len(slots)-1 else' '+proof+'.')
    lines += ['Qed.',
        'Theorem joint_authentic_phase seed ev pre g:EventAllowed ev ->',
        f' CombLFP {program} seed(phase_driven_state {program} ev pre) ->AuthenticInv pre g ->',
        f' AuthenticInv(PhaseSemantics {program} ev pre)(joint_step ev pre g).',
        'Proof. intros HE HL[HV HR];split;[exact(joint_phase seed ev pre g HE HL HV)|now apply joint_recorded_phase]. Qed.',
        'Theorem joint_authentic_replay events:Forall EventAllowed events ->forall pre g,Ready events pre ->AuthenticInv pre g ->',
        ' AuthenticInv(fst(joint_run events pre g))(snd(joint_run events pre g)).',
        'Proof. intros HE;induction HE as[|ev rest HA HE IH];intros pre g HR HI;[exact HI|].',
        ' destruct HR as[[seed HL]HR];cbn[joint_run instrumented_run];apply IH;[exact HR|].',
        ' exact(joint_authentic_phase seed ev pre g HA HL HI). Qed.',
        f'Theorem joint_authentic_initialize:AuthenticInv(initialize {program} [])joint_empty.',
        'Proof. split;[exact joint_initialize|]. unfold JointRecorded,joint_empty,CurrentRecorded,Recorded;',
        ' cbn[joint_birth current history '+ ' '.join(f'joint_tag_{s["index"]}'for s in slots)+'];repeat split;intros token H;discriminate. Qed.',
        'Theorem joint_recorded_id_unique pre g a b:AuthenticInv pre g ->',
        ' In a(history(joint_birth g)) ->In b(history(joint_birth g)) ->token_id a=token_id b ->a=b.',
        'Proof. intros[[HB HM]HR]HA HB2 HE;destruct HB as[HV[HT[HH HN]]].',
        ' exact(ledger_id_unique(history(joint_birth g))HN a b HA HB2 HE). Qed.']
    exports=['joint_phase','joint_replay','joint_erases','joint_initialize','joint_recorded_phase',
        'joint_authentic_phase','joint_authentic_replay','joint_authentic_initialize','joint_recorded_id_unique']
    raw_birth_args=f'{program} {ast["module"]}.{b["process"]} {b["carrier"]} B.root_{b["carrier"]}_expression B.root_{b["valid_root"]}_expression B.capture_0_pc'
    lines += [f'Definition pending_admitted ev pre g:=observed_births {raw_birth_args} ev pre(joint_birth g).',
        f'Definition pending_step ev pre g queue retiring cancel:=queue_step {raw_birth_args} ev pre(joint_birth g)queue retiring cancel.',
        'Definition PendingInv pre g queue:=AuthenticInv pre g /\\Pending(history(joint_birth g))queue.',
        'Theorem pending_admissions_recorded ev pre g:',
        ' Forall(fun token=>In token(history(joint_birth(joint_step ev pre g))))(pending_admitted ev pre g).',
        f'Proof. exact(phase_births_recorded {raw_birth_args} ev pre(joint_birth g)). Qed.',
        'Theorem pending_queue_partition ev pre g queue retiring cancel kept killed:',
        ' pending_step ev pre g queue retiring cancel=Some(kept,killed) ->',
        ' queue++pending_admitted ev pre g=retiring++(kept++killed).',
        f'Proof. exact(phase_queue_partition {raw_birth_args} ev pre(joint_birth g)queue retiring cancel kept killed). Qed.',
        'Theorem pending_phase_candidate seed ev pre g queue retiring cancel kept killed:EventAllowed ev ->',
        f' CombLFP {program} seed(phase_driven_state {program} ev pre) ->PendingInv pre g queue ->',
        ' pending_step ev pre g queue retiring cancel=Some(kept,killed) ->',
        f' PendingInv(PhaseSemantics {program} ev pre)(joint_step ev pre g)kept.',
        'Proof. intros HE HL[HI HQ]HS;split;[exact(joint_authentic_phase seed ev pre g HE HL HI)|].',
        ' destruct HI as[[HB HM]HR];destruct HB as[HV[HT[HH HN]]].',
        f' exact(phase_queue_preserved {raw_birth_args} ev pre(joint_birth g)queue retiring cancel kept killed HH HQ HS). Qed.',
        f'Theorem pending_initialize:PendingInv(initialize {program} [])joint_empty[].',
        'Proof. split;[exact joint_authentic_initialize|]. split;constructor. Qed.']
    exports+=['pending_admissions_recorded','pending_queue_partition','pending_phase_candidate','pending_initialize']
    for name in exports:lines.append('Print Assumptions '+name+'.')
    return dict(ast_sha256=ast['source_sha256'],coq_load_paths=loadpaths,slots=slots,provider_hashes=[br['object_sha256'],fr['object_sha256']],
        audited_exports=len(exports),old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,
        label_authenticity_invariant_generated=True,
        manual_admission_input=False,pending_checker_never_fails_proved=False,retirement_binding_proved=False,
        external_origin_labels_required=False,original_runtime_initialization_proved=False,
        pending_retirement_correspondence_proved=False,global_inv_proved=False,itree_refinement_proved=False),'\n'.join(lines)+'\n'


def roots_coq(roots):return '['+';'.join(str(r)+'%nat'for r in roots)+']'
def nested(names):return names[0]if len(names)==1 else'['+names[0]+' '+nested(names[1:])+']'


def check(ast_path,ast_module,birth_provider,coverage_provider,value_provider,copy_provider,field_provider,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module,birth_provider,coverage_provider,value_provider,copy_provider,field_provider)
    except ValueError as error:
        result=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,old_pending_read=False,
            global_inv_proved=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result
    path=output/'JointHistory.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(birth.rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    for folder,namespace in[(birth_provider,'GeneratedCaptureBirth'),(coverage_provider,'GeneratedRecipeCoverage'),
        (value_provider,'GeneratedConnectedProjections'),(copy_provider,'GeneratedMetadataCopies'),
        (field_provider,'GeneratedCoveredFields'),(output,'GeneratedJointHistory')]:flags+=['-R',str(Path(folder).resolve()),namespace]
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    result=dict(accepted=False,native_started=True,scope='new joint capture/metadata provenance invariant and finite phase induction',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,external_origin_labels_required=False,
        manual_admission_input=False,pending_checker_never_fails_proved=False,retirement_binding_proved=False,
        original_runtime_initialization_proved=False,pending_retirement_correspondence_proved=False,
        global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout
        result['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedJointHistory.JointHistory'],
                output/'coqchk.log',deadline-time.monotonic())
            result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    result['overall_seconds']=time.monotonic()-start
    if result['accepted']:result['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in['ast','birth-provider','coverage-provider','value-provider','copy-provider','field-provider','output']:
        p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--ast-module',required=True);a=p.parse_args()
    result=check(a.ast,a.ast_module,a.birth_provider,a.coverage_provider,a.value_provider,a.copy_provider,a.field_provider,a.output)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
