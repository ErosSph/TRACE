"""Infer source-to-pipeline handoff from raw RTL and fresh certificates.

No old CPU INV is an input. Clock coherence is checked through actual aliases;
raw clock normalization is a concrete generated invariant, not silently inferred
from a normalized projection. This remains a local component, not ISA refinement.
"""
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_pending_source_hold as hold
from cpu_certificate_acceptance import run_stage
r=hold.retirement;fields=hold.fields;origin=hold.origin;rtl=hold.rtl


def strip(e):
    while e.name=='EExtend'and e.args[:2]==(rtl.Term('1'),rtl.Term('false')):e=e.args[2]
    return e


def gated_valid(row,source_valid,gate):
    e=rtl.Parser(row['expanded']).complete()
    if e.name!='ECond'or e.args[0].name!='1'or not hold.control.is_var(e.args[1],1):return None
    if not hold.control.is_const(e.args[3],1,0):return None
    bit=strip(e.args[2])
    if bit.name!='EBinary'or bit.args[:2]!=(rtl.Term('1'),rtl.Term('BAnd')):return None
    if {strip(x)for x in bit.args[2:]}!={rtl.Term('EVar',(rtl.Term('1'),rtl.Term(str(source_valid)))),
        rtl.Term('EVar',(rtl.Term('1'),rtl.Term(str(gate))))}:return None
    reset=int(e.args[1].args[1].name)
    expected=rtl.Term('Select',(e.args[1],rtl.Term('Capture'),rtl.Term('Unknown')))
    return reset if row['recipe']==rtl.render(expected) else None


def chain(ast,root):
    edges=[];seen=set()
    while root not in seen:
        seen.add(root);writers=[p for p in ast['processes']if p['kind']!='Initial'and root in p['writers']]
        if len(writers)!=1 or writers[0]['kind']!='Combinational':return dict(terminal=root,edges=edges)
        p=writers[0];b=p['body']
        if b.name!='SAssign'or b.args[0].name!='false'or b.args[2]!=rtl.Term('LVar',(rtl.Term('1'),rtl.Term(str(root))))or not hold.control.is_var(b.args[1],1):
            return dict(terminal=root,edges=edges)
        src=int(b.args[1].args[1].name);edges.append(dict(root=root,source=src,process=p['name']));root=src
    return None


def event_pair(events,reset):
    found=re.findall(r'\{\| event_edge := (Posedge|Negedge); event_signal := ([0-9]+) \|\}',events)
    if len(found)!=2 or events!='['+'; '.join('{| event_edge := '+e+'; event_signal := '+s+' |}'for e,s in found)+']':return None
    if found[0][0]!='Posedge'or found[1]!=('Negedge',str(reset)):return None
    return int(found[0][1])


def discover(ast):
    rows=[];procs={p['name']:p for p in ast['processes']}
    for h in hold.discover(ast)['holds']:
        for item in r.raw_connections(ast):
            c=item['coverage'];b=h['birth']
            if c['source']!=b['carrier']or c['source_valid']!=b['valid_root']:continue
            reset=gated_valid(c,b['valid_root'],h['control']['gate'])
            if reset is None:continue
            sc=event_pair(procs[b['process']]['events'],h['reset']);dc=event_pair(procs[c['process']]['events'],reset)
            if sc is None or dc is None:continue
            routes={k:chain(ast,v)for k,v in dict(source_clock=sc,target_clock=dc,source_reset=h['reset'],target_reset=reset).items()}
            if any(v is None for v in routes.values()):continue
            if routes['source_clock']['terminal']!=routes['target_clock']['terminal']or routes['source_reset']['terminal']!=routes['target_reset']['terminal']:continue
            rows.append(dict(hold=h,connection=item,target_reset=reset,source_clock=sc,target_clock=dc,routes=routes))
    return dict(handoffs=rows,old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,
        whole_queue_losslessness_proved=False,global_inv_proved=False,itree_refinement_proved=False)


def render(ast_path,ast_module,provider):
    provider=Path(provider);ast,profile,paths=origin.raw_binding(ast_path,ast_module);data=discover(ast)
    if len(data['handoffs'])!=1:raise ValueError('one raw gated-valid handoff with common clock/reset routes required')
    hd,hs=hold.render(ast_path,ast_module,provider/'capture-birth',provider/'stall-flush')
    hr=fields.verify(provider/'source-hold','SourceHold.v',hd,hs)
    jd,js=r.joint.render(ast_path,ast_module,provider/'capture-birth',provider/'coverage',provider/'value',provider/'copies',provider/'joint')
    jr=fields.verify(provider/'joint-history','JointHistory.v',jd,js)
    row=data['handoffs'][0];h=row['hold'];b=h['birth'];c=row['connection']['coverage'];i=row['connection']['coverage_index']
    slot=next(s for s in jd['slots']if s['root']==c['root']);index=slot['index'];p=profile['ast']['program']
    w=b['carrier'];v=b['valid_root'];en=h['enable'];rst=h['reset'];dr=row['target_reset'];vr=c['valid_root'];gate=h['control']['gate']
    sp=ast['module']+'.'+b['process'];dp=ast['module']+'.'+c['process'];sc=row['source_clock'];dc=row['target_clock']
    edges={e['root']:e for route in row['routes'].values()for e in route['edges']}
    _,analysis,source=fields.connected.comb.proposal(profile,list(edges))
    if analysis['residuals']:raise ValueError('actual clock/reset alias residual')
    ports={x['output_root']:n for n,x in enumerate(analysis['ports'])};clockroots=sorted({sc,dc,rst,dr});roots=r.joint.roots_coq(clockroots)
    lines=['From Coq Require Import List ZArith Bool.',
        f'Require Import {ast_module}.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVStallFlush Lang.ExtendedSVWordInvariant Lang.ExtendedSVProjectionOrigin',
        ' Lang.ExtendedSVProjectionConnection Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression',
        ' Lang.ExtendedSVCaptureBirth GeneratedSourceHold.SourceHold GeneratedJointHistory.JointHistory.',
        'Import ListNotations ExtendedSV ExtendedSVStallFlush ExtendedSVWordInvariant ExtendedSVProjectionOrigin ExtendedSVProjectionConnection',
        ' ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVCaptureBirth.',
        'Module H:=GeneratedSourceHold.SourceHold. Module J:=GeneratedJointHistory.JointHistory.',
        'Module B:=GeneratedCaptureBirth.CaptureBirth. Module C:=GeneratedRecipeCoverage.RecipeCoverage.',
        'Module F:=GeneratedCoveredFields.CoveredFields.',
        f'Definition clock_roots:list nat:={roots}.',
        f'Lemma clock_words_checked:Forall(fun root=>program_wordb {p} 1 root=true)clock_roots.',
        'Proof. vm_compute;repeat constructor. Qed.',f'Local Opaque {p}.',
        'Definition ClockWords s:=forall root,In root clock_roots ->WordRoot 1 root s.',
        'Definition ClockAllowed ev:=forall root,In root clock_roots ->changed_signal ev<>root.',
        f'Lemma clock_words_initialize:ClockWords(initialize {p} []).',
        'Proof. intros root HI;apply initialize_word;[exact(proj1(Forall_forall _ _)clock_words_checked root HI)|reflexivity]. Qed.',
        f'Lemma clock_words_sampled ev pre:ClockAllowed ev ->ClockWords pre ->ClockWords(phase_driven_state {p} ev pre).',
        'Proof. intros HE HW root HI;unfold phase_driven_state;apply lfp_word;',
        ' [exact(proj1(Forall_forall _ _)clock_words_checked root HI)|].',
        ' unfold WordRoot;rewrite read_signal_write_other by(exact(HE root HI));exact(HW root HI). Qed.',
        f'Lemma clock_words_phase ev pre:ClockAllowed ev ->ClockWords pre ->ClockWords(PhaseSemantics {p} ev pre).',
        f'Proof. intros HE HW root HI;exact(phase_word {p} 1 root ev pre',
        ' (proj1(Forall_forall _ _)clock_words_checked root HI)(HE root HI)(HW root HI)). Qed.']
    for name,route in row['routes'].items():
        start=dict(source_clock=sc,target_clock=dc,source_reset=rst,target_reset=dr)[name]
        lines += [f'Lemma {name}_alias seed fixed:CombLFP {p} seed fixed ->',
            f' norm 1(read_signal fixed {start})=norm 1(read_signal fixed {route["terminal"]}).','Proof. intro HL.']
        for e in route['edges']:
            n=ports[e['root']];lines += [f' rewrite(W.port_{n}_lfp _ _ HL);cbn[W.port_{n}_rhs eval_expr];rewrite norm_idempotent.']
        lines += [' reflexivity. Qed.']
    for name,a,z in [('clock',sc,dc),('reset',rst,dr)]:
        lines += [f'Lemma {name}_equal seed fixed:ClockWords fixed ->CombLFP {p} seed fixed ->read_signal fixed {a}=read_signal fixed {z}.',
            f'Proof. intros HW HL;pose proof(eq_trans(source_{name}_alias _ _ HL)(eq_sym(target_{name}_alias _ _ HL)))as HA.',
            f' pose proof(HW {a}(ltac:(unfold clock_roots;cbn;auto)))as HX;',
            f' pose proof(HW {z}(ltac:(unfold clock_roots;cbn;auto)))as HY.',
            ' unfold WordRoot,Word in HX,HY;rewrite <-HX,<-HY in HA;exact HA. Qed.']
    lines += ['Theorem actual_process_clocks_agree seed0 seed ev pre:',
        f' ClockAllowed ev ->ClockWords pre ->CombLFP {p} seed0 pre ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
        f' process_matches_states pre(phase_driven_state {p} ev pre){sp}=',
        f' process_matches_states pre(phase_driven_state {p} ev pre){dp}.',
        'Proof. intros HE HW HL0 HL;pose proof(clock_words_sampled ev pre HE HW)as HD.',
        f' change((edge_fires Posedge(read_signal pre {sc})(read_signal(phase_driven_state {p} ev pre){sc}) ||',
        f' (edge_fires Negedge(read_signal pre {rst})(read_signal(phase_driven_state {p} ev pre){rst}) ||false))%bool=',
        f' (edge_fires Posedge(read_signal pre {dc})(read_signal(phase_driven_state {p} ev pre){dc}) ||',
        f' (edge_fires Negedge(read_signal pre {dr})(read_signal(phase_driven_state {p} ev pre){dr}) ||false))%bool).',
        ' rewrite(clock_equal _ _ HW HL0),(reset_equal _ _ HW HL0),',
        ' (clock_equal _ _ HD HL),(reset_equal _ _ HD HL);reflexivity. Qed.',
        'Lemma target_reset_active seed ev pre:',
        f' ClockAllowed ev ->ClockWords pre ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){rst})<>0%Z ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){dr})<>0%Z.',
        'Proof. intros HE HW HL HR;rewrite <-(reset_equal _ _(clock_words_sampled ev pre HE HW)HL);exact HR. Qed.',
        'Theorem enabled_target_valid seed ev pre:',
        f' changed_signal ev<>{v}%nat ->changed_signal ev<>{vr}%nat ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){dr})<>0%Z ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){en})<>0%Z ->norm 1(read_signal pre {v})<>0%Z ->',
        f' process_matches_states pre(phase_driven_state {p} ev pre){dp}=true ->',
        f' norm 1(read_signal(PhaseSemantics {p} ev pre){vr})=1%Z.',
        'Proof. intros HV HT HL HR HE HI HF.',
        f' rewrite(history_phase_projection {p} {vr} 1 {dp} C.root_{vr}_expression C.root_{vr}_valid_certificate ev pre HT),HF.',
        f' pose proof(bindings_substitute_sound C.coverage_{i}_bindings C.root_{vr}_expression(phase_driven_state {p} ev pre)',
        f' (C.coverage_{i}_bindings_agree seed _ HL))as HX;rewrite C.coverage_{i}_expansion_checked in HX;rewrite <-HX.',
        f' assert(HRone:norm 1(read_signal(phase_driven_state {p} ev pre){dr})=1%Z).',
        f' {{ destruct(one_bit_cases(phase_driven_state {p} ev pre){dr})as[HZ|HZ];[contradiction|exact HZ]. }}',
        f' assert(Hgate:norm 1(read_signal(phase_driven_state {p} ev pre){gate})=1%Z).',
        f' {{ rewrite(H.enable_alias _ _ HL)in HE;destruct(one_bit_cases(phase_driven_state {p} ev pre){gate})as[HZ|HZ];[contradiction|exact HZ]. }}',
        f' assert(Hinput:norm 1(read_signal(phase_driven_state {p} ev pre){v})=1%Z).',
        f' {{ rewrite(sampled_root_preserved {p} ev pre {v}(history_comb_frame _ _ _ _ _ B.root_{v}_birth_certificate)HV).',
        f' destruct(one_bit_cases pre {v})as[HZ|HZ];[contradiction|exact HZ]. }}',
        f' cbn[C.coverage_{i}_expanded eval_expr];rewrite HRone,Hgate,Hinput;reflexivity. Qed.',
        'Theorem enabled_identity_handoff seed0 seed ev pre g label:',
        f' J.EventAllowed ev ->ClockAllowed ev ->ClockWords pre ->CombLFP {p} seed0 pre ->',
        f' CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){rst})<>0%Z ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){en})<>0%Z ->norm 1(read_signal pre {v})<>0%Z ->',
        f' process_matches_states pre(phase_driven_state {p} ev pre){sp}=true ->',
        ' current(J.joint_birth g)=Some label ->',
        f' J.joint_tag_{index}(J.joint_step ev pre g)=Some label /\\norm 1(read_signal(PhaseSemantics {p} ev pre){vr})=1%Z.',
        'Proof. intros HJ HC HW HL0 HL HR HE HI HF HT.',
        f' assert(HV:changed_signal ev<>{v}%nat)by(exact(proj1(Forall_forall _ _)HJ {v}(ltac:(cbn;auto)))).',
        f' assert(HD:changed_signal ev<>{vr}%nat)by(exact(proj1(Forall_forall _ _)HJ {vr}(ltac:(cbn;auto)))).',
        ' pose proof(target_reset_active seed ev pre HC HW HL HR)as HRA.',
        f' assert(HF2:process_matches_states pre(phase_driven_state {p} ev pre){dp}=true).',
        ' { rewrite <-(actual_process_clocks_agree seed0 seed ev pre HC HW HL0 HL);exact HF. }',
        f' assert(HRone:norm 1(read_signal(phase_driven_state {p} ev pre){dr})=1%Z).',
        f' {{ destruct(one_bit_cases(phase_driven_state {p} ev pre){dr})as[HZ|HZ];[contradiction|exact HZ]. }}',
        ' split.',
        f' - change(F.field_{index}_origin Token ev pre(J.joint_tag_{index} g)(current(J.joint_birth g))=Some label).',
        f' unfold F.field_{index}_origin,projection_phase_origin;rewrite HF2;cbn[C.coverage_{i}_recipe recipe_origin eval_expr];now rewrite HRone.',
        ' - exact(enabled_target_valid seed ev pre HV HD HL HRA HE HI HF2). Qed.',
        'Theorem source_token_not_lost seed0 seed ev pre g label:',
        f' J.EventAllowed ev ->ClockAllowed ev ->ClockWords pre ->CombLFP {p} seed0 pre ->',
        f' CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){rst})<>0%Z ->',
        f' Invariant {w} {v} pre(J.joint_birth g) ->norm 1(read_signal pre {v})<>0%Z ->',
        ' current(J.joint_birth g)=Some label ->',
        ' current(J.joint_birth(J.joint_step ev pre g))=Some label \/',
        f' (J.joint_tag_{index}(J.joint_step ev pre g)=Some label /\\norm 1(read_signal(PhaseSemantics {p} ev pre){vr})=1%Z).',
        'Proof. intros HJ HC HW HL0 HL HR HI HV HT.',
        f' destruct(process_matches_states pre(phase_driven_state {p} ev pre){sp})eqn:HF.',
        f' - destruct(Z.eq_dec(norm 1(read_signal(phase_driven_state {p} ev pre){en}))0%Z)as[HE|HE].',
        '   + left;change(current(B.capture_0_step ev pre(J.joint_birth g))=Some label).',
        f'     rewrite(H.stalled_current_label_kept seed ev pre(J.joint_birth g));[exact HT|',
        f'     exact(proj1(Forall_forall _ _)HJ {w}(ltac:(cbn;auto)))|exact(proj1(Forall_forall _ _)HJ {v}(ltac:(cbn;auto)))|exact HL|exact HR|exact HE|exact HI|exact HV].',
        '   + right;exact(enabled_identity_handoff seed0 seed ev pre g label HJ HC HW HL0 HL HR HE HV HF HT).',
        ' - left;change(current(B.capture_0_step ev pre(J.joint_birth g))=Some label).',
        '   unfold B.capture_0_step,ghost_step,phase_decision;rewrite HF;exact HT. Qed.',
        'Definition TransportInv pre g:=J.AuthenticInv pre g /\\ClockWords pre.',
        f'Theorem transport_initialize:TransportInv(initialize {p} [])J.joint_empty.',
        'Proof. split;[exact J.joint_authentic_initialize|exact clock_words_initialize]. Qed.',
        'Theorem transport_phase seed ev pre g:J.EventAllowed ev ->ClockAllowed ev ->',
        f' CombLFP {p} seed(phase_driven_state {p} ev pre) ->TransportInv pre g ->',
        f' TransportInv(PhaseSemantics {p} ev pre)(J.joint_step ev pre g).',
        'Proof. intros HJ HC HL[HI HW];split;[exact(J.joint_authentic_phase seed ev pre g HJ HL HI)|',
        'exact(clock_words_phase ev pre HC HW)]. Qed.',
        'Theorem transport_source_identity seed0 seed ev pre g label:',
        f' J.EventAllowed ev ->ClockAllowed ev ->CombLFP {p} seed0 pre ->',
        f' CombLFP {p} seed(phase_driven_state {p} ev pre) ->TransportInv pre g ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){rst})<>0%Z ->',
        f' norm 1(read_signal pre {v})<>0%Z ->current(J.joint_birth g)=Some label ->',
        f' TransportInv(PhaseSemantics {p} ev pre)(J.joint_step ev pre g) /\\',
        ' (current(J.joint_birth(J.joint_step ev pre g))=Some label \/',
        f' (J.joint_tag_{index}(J.joint_step ev pre g)=Some label /\\norm 1(read_signal(PhaseSemantics {p} ev pre){vr})=1%Z)).',
        'Proof. intros HJ HC HL0 HL HI HR HV HT;split;[exact(transport_phase seed ev pre g HJ HC HL HI)|].',
        ' destruct HI as[HA HW];exact(source_token_not_lost seed0 seed ev pre g label HJ HC HW HL0 HL HR(proj1(proj1 HA))HV HT). Qed.']
    exports=['clock_words_initialize','clock_words_phase','actual_process_clocks_agree','enabled_target_valid','enabled_identity_handoff','source_token_not_lost',
        'transport_initialize','transport_phase','transport_source_identity']
    for name in exports:lines.append('Print Assumptions '+name+'.')
    return dict(**data,ast_sha256=ast['source_sha256'],coq_load_paths=paths,provider_hashes=[hr['object_sha256'],jr['object_sha256']],
        audited_exports=len(analysis['ports'])+len(exports)),'Module W.\n'+source+'\nEnd W.\n'+'\n'.join(lines)+'\n'


def check(ast_path,ast_module,provider,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module,provider)
    except ValueError as error:
        result=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,global_inv_proved=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result
    path=output/'SourceTransfer.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    for folder,namespace in [('capture-birth','GeneratedCaptureBirth'),('coverage','GeneratedRecipeCoverage'),('value','GeneratedConnectedProjections'),('copies','GeneratedMetadataCopies'),('joint','GeneratedCoveredFields'),('joint-history','GeneratedJointHistory'),('stall-flush','GeneratedStallFlush'),('source-hold','GeneratedSourceHold')]:
        flags+=['-R',str((Path(provider)/folder).resolve()),namespace]
    flags+=['-R',str(output.resolve()),'GeneratedSourceTransfer'];start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    result=dict(accepted=False,native_started=True,scope='actual normal source token held or handed to next valid stage; not whole-queue/ISA refinement',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),old_inv_read=False,
        old_pending_read=False,old_cpu_proofs_used=False,whole_queue_losslessness_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout;result['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedSourceTransfer.SourceTransfer'],output/'coqchk.log',deadline-time.monotonic())
            result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    result['overall_seconds']=time.monotonic()-start
    if result['accepted']:result['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in['ast','provider','output']:p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--ast-module',required=True);a=p.parse_args()
    result=check(a.ast,a.ast_module,a.provider,a.output);print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
