"""Connect freshly proved control tails to actual RTL instruction holds.

Discovery reads only AST. New provider sources/plans/objects are reconstructed
and verified; no old CPU INV or pending catalog supplies control conditions.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_stall_flush as control
import cpu_pending_retirement as retirement
from cpu_certificate_acceptance import run_stage
birth=retirement.birth;fields=retirement.fields;origin=retirement.origin;rtl=retirement.rtl


def source_shape(row):
    word=rtl.Parser(row['word_expression']).complete();valid=rtl.Parser(row['valid_expression']).complete()
    if word.name!='ECond'or not control.is_var(word.args[1],1):return None
    normal=word.args[2]
    if normal.name!='ECond'or not control.is_var(normal.args[1],1):return None
    enabled=normal.args[3]
    if enabled.name!='ECond'or not control.is_var(enabled.args[1],1):return None
    root=row['carrier'];v=row['valid_root']
    if not birth.validity.is_var(enabled.args[2],32)or not birth.validity.is_var(enabled.args[3],32,root):return None
    reset,flush,enable=word.args[1],normal.args[1],enabled.args[1]
    expected=rtl.Term('ECond',(rtl.Term('1'),reset,
        rtl.Term('ECond',(rtl.Term('1'),flush,rtl.Term('EConst',(rtl.Term('1'),rtl.Term('0'))),
            rtl.Term('ECond',(rtl.Term('1'),enable,rtl.Term('EConst',(rtl.Term('1'),rtl.Term('1'))),
                rtl.Term('EVar',(rtl.Term('1'),rtl.Term(str(v)))))))),rtl.Term('EConst',(rtl.Term('1'),rtl.Term('0')))))
    if valid!=expected:return None
    return dict(reset=int(reset.args[1].name),flush=int(flush.args[1].name),enable=int(enable.args[1].name))


def discover(ast):
    bs=birth.discover(ast);cs=control.discover(ast);rows=[]
    for i,b in enumerate(bs['captures']):
        shape=source_shape(b)
        if shape is None:continue
        for j,c in enumerate(cs['tails']):
            er=retirement.alias_route(ast,shape['enable'],1,{c['gate']:c})
            fr=retirement.alias_route(ast,shape['flush'],1,{c['flag']:c})
            if er is not None and fr is not None:
                rows.append(dict(birth_index=i,control_index=j,birth=b,control=c,enable_route=er,flush_route=fr,**shape))
    return dict(holds=rows,old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,
        admitted_token_losslessness_proved=False,global_inv_proved=False,itree_refinement_proved=False)


def render(ast_path,ast_module,birth_provider,control_provider):
    ast,profile,paths=origin.raw_binding(ast_path,ast_module);data=discover(ast)
    if len(data['holds'])!=1:raise ValueError('one structurally linked source/control hold required; no assumed flush condition')
    bd,bs=birth.render(ast_path,ast_module);cd,cs=control.render(ast_path,ast_module)
    br=fields.verify(birth_provider,'CaptureBirth.v',bd,bs);cr=fields.verify(control_provider,'StallFlush.v',cd,cs)
    row=data['holds'][0];b=row['birth'];c=row['control'];p=profile['ast']['program'];w=b['carrier'];v=b['valid_root']
    edges={e['root']:e for route in[row['enable_route'],row['flush_route']]for e in route['edges']}
    _,analysis,source=fields.connected.comb.proposal(profile,list(edges))
    if analysis['residuals']:raise ValueError('actual guard-alias proof residual')
    ports={r['output_root']:i for i,r in enumerate(analysis['ports'])}
    lines=['Require Import Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPending Lang.ExtendedSVScalarHistory',
        ' Lang.ExtendedSVScalarExpression Lang.ExtendedSVInstructionOrigin Lang.ExtendedSVWordInvariant',
        ' GeneratedCaptureBirth.CaptureBirth GeneratedStallFlush.StallFlush.',
        'Import ExtendedSVCaptureBirth ExtendedSVCapturedPending ExtendedSVScalarHistory ExtendedSVScalarExpression',
        ' ExtendedSVInstructionOrigin ExtendedSVWordInvariant.',
        'Module B:=GeneratedCaptureBirth.CaptureBirth. Module C:=GeneratedStallFlush.StallFlush.',f'Local Opaque {p}.']
    for label,route,target in[('enable',row['enable_route'],c['gate']),('flush',row['flush_route'],c['flag'])]:
        lines += [f'Lemma {label}_alias seed fixed:CombLFP {p} seed fixed ->',
            f' norm 1(read_signal fixed {row[label]})=norm 1(read_signal fixed {target}).','Proof. intro HL.']
        for e in route['edges']:
            n=ports[e['root']];lines += [f' rewrite(port_{n}_lfp _ _ HL);cbn[port_{n}_rhs eval_expr];rewrite norm_idempotent.']
        lines += [' reflexivity. Qed.']
    reset=row['reset'];flush=row['flush'];enable=row['enable'];proc=ast['module']+'.'+b['process'];bi=row['birth_index'];ci=row['control_index']
    lines += ['Theorem flush_requires_enable seed fixed:',f' CombLFP {p} seed fixed ->norm 1(read_signal fixed {flush})<>0%Z ->',
        f' norm 1(read_signal fixed {enable})<>0%Z.',
        f'Proof. intros HL HF;rewrite(enable_alias _ _ HL);apply(C.ctrl_{ci}_actual_lfp _ _ HL);rewrite <-(flush_alias _ _ HL);exact HF. Qed.',
        f'Lemma stalled_flush_zero seed fixed:CombLFP {p} seed fixed ->norm 1(read_signal fixed {enable})=0%Z ->',
        f' norm 1(read_signal fixed {flush})=0%Z.',
        f'Proof. intros HL HE;destruct(Z.eq_dec(norm 1(read_signal fixed {flush}))0)as[HF|HF];[exact HF|].',
        ' exfalso;exact(flush_requires_enable _ _ HL HF HE). Qed.',
        'Theorem actual_stalled_source_phase seed ev pre:',
        f' changed_signal ev<>{w}%nat ->changed_signal ev<>{v}%nat ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){reset})<>0%Z ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){enable})=0%Z ->',
        f' norm 32(read_signal(PhaseSemantics {p} ev pre){w})=norm 32(read_signal pre {w}) /\\',
        f' norm 1(read_signal(PhaseSemantics {p} ev pre){v})=norm 1(read_signal pre {v}).',
        'Proof. intros HW HV HL HR HE.',
        f' assert(HRZ:Z.eqb(norm 1(read_signal(phase_driven_state {p} ev pre){reset}))0=false)by(now apply Z.eqb_neq).',
        f' pose proof(stalled_flush_zero _ _ HL HE)as HF.',
        f' rewrite(history_phase_projection {p} {w} 32 {proc} B.root_{w}_expression B.root_{w}_birth_certificate ev pre HW),',
        f' (history_phase_projection {p} {v} 1 {proc} B.root_{v}_expression B.root_{v}_birth_certificate ev pre HV).',
        f' destruct(process_matches_states pre(phase_driven_state {p} ev pre){proc});[|split;reflexivity].',
        f' cbn[B.root_{w}_expression B.root_{v}_expression eval_expr];rewrite HRZ,HF,HE;cbn[Z.eqb];rewrite !norm_idempotent.',
        f' rewrite(sampled_root_preserved {p} ev pre {w}(history_comb_frame _ _ _ _ _ B.root_{w}_birth_certificate)HW),',
        f' (sampled_root_preserved {p} ev pre {v}(history_comb_frame _ _ _ _ _ B.root_{v}_birth_certificate)HV);split;reflexivity. Qed.',
        'Theorem stalled_phase_creates_no_capture seed ev pre g:',
        f' CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){reset})<>0%Z ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){enable})=0%Z ->',
        f' observed_births {p} {proc} {w} B.root_{w}_expression B.root_{v}_expression B.capture_{bi}_pc ev pre g=[].',
        'Proof. intros HL HR HE.',
        f' assert(HRZ:Z.eqb(norm 1(read_signal(phase_driven_state {p} ev pre){reset}))0=false)by(now apply Z.eqb_neq).',
        ' pose proof(stalled_flush_zero _ _ HL HE)as HF.',
        f' unfold observed_births,phase_decision;destruct(process_matches_states pre(phase_driven_state {p} ev pre){proc});[|reflexivity].',
        f' unfold decide;cbn[B.root_{w}_expression B.root_{v}_expression eval_expr copy_source];rewrite HRZ,HF,HE;cbn[Z.eqb];rewrite !norm_idempotent.',
        f' destruct(Z.eqb(norm 1(read_signal(phase_driven_state {p} ev pre){v}))0);[reflexivity|].',
        ' rewrite Nat.eqb_refl;reflexivity. Qed.',
        'Lemma no_birth_live_keeps_old decision serial sampled pc old:',
        ' NewTokens decision serial sampled pc=[] ->',
        ' (exists label,next_tag decision serial sampled pc old=Some label) ->',
        ' next_tag decision serial sampled pc old=old.',
        'Proof. intros HB HC;destruct decision;[reflexivity|destruct HC as[label H];discriminate|discriminate]. Qed.',
        'Theorem stalled_current_label_kept seed ev pre g:',
        f' changed_signal ev<>{w}%nat ->changed_signal ev<>{v}%nat ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){reset})<>0%Z ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){enable})=0%Z ->',
        f' Invariant {w} {v} pre g ->norm 1(read_signal pre {v})<>0%Z ->',
        f' current(B.capture_{bi}_step ev pre g)=current g.',
        'Proof. intros HW HV HL HR HE HI Hlive.',
        f' pose proof(B.capture_{bi}_phase ev pre g HW HV HI)as[HP Hrest];destruct HP as[Hcover Hvalue].',
        ' pose proof(proj2(actual_stalled_source_phase seed ev pre HW HV HL HR HE))as Hvalid.',
        f' assert(Hpost:norm 1(read_signal(PhaseSemantics {p} ev pre){v})<>0%Z)by(now rewrite Hvalid).',
        ' pose proof(Hcover Hpost)as HC.',
        f' apply(no_birth_live_keeps_old(phase_decision {p} {proc} {w} B.root_{w}_expression B.root_{v}_expression ev pre)',
        f' (serial g)(phase_driven_state {p} ev pre)B.capture_{bi}_pc(current g));',
        ' [exact(stalled_phase_creates_no_capture seed ev pre g HL HR HE)|exact HC]. Qed.']
    exports=['flush_requires_enable','actual_stalled_source_phase','stalled_phase_creates_no_capture','stalled_current_label_kept']
    for name in exports:lines.append('Print Assumptions '+name+'.')
    return dict(**data,ast_sha256=ast['source_sha256'],coq_load_paths=paths,provider_hashes=[br['object_sha256'],cr['object_sha256']],
        audited_exports=len(analysis['ports'])+len(exports)),source+'\n'+'\n'.join(lines)+'\n'


def check(ast_path,ast_module,birth_provider,control_provider,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module,birth_provider,control_provider)
    except ValueError as error:
        result=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,global_inv_proved=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result
    path=output/'SourceHold.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    for folder,namespace in[(birth_provider,'GeneratedCaptureBirth'),(control_provider,'GeneratedStallFlush'),(output,'GeneratedSourceHold')]:
        flags+=['-R',str(Path(folder).resolve()),namespace]
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    result=dict(accepted=False,native_started=True,scope='actual normal stalled instruction carrier holds and creates no capture; not global queue flow',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),old_inv_read=False,
        old_pending_read=False,old_cpu_proofs_used=False,admitted_token_losslessness_proved=False,
        global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout
        result['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedSourceHold.SourceHold'],output/'coqchk.log',deadline-time.monotonic())
            result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    result['overall_seconds']=time.monotonic()-start
    if result['accepted']:result['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in['ast','birth-provider','control-provider','output']:p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--ast-module',required=True);a=p.parse_args()
    r=check(a.ast,a.ast_module,a.birth_provider,a.control_provider,a.output);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
