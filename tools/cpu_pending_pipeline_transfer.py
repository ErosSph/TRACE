"""Generate valid/tag shift equations for the raw metadata pipeline suffix.

The first gated source transfer is a newly generated checked dependency, not an
old CPU INV. Every supported copy edge is reconstructed from raw expressions,
event polarity and actual clock/reset aliases. No manual stage IDs are inputs.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_source_transfer as first
from cpu_certificate_acceptance import run_stage
r=first.r;fields=first.fields;origin=first.origin;rtl=first.rtl


def reset_guard(row):
    e=rtl.Parser(row['expanded']).complete()
    if e.name!='ECond'or e.args[0].name!='1'or not first.hold.control.is_var(e.args[1],1):return None
    if not first.hold.control.is_const(e.args[3],1,0):return None
    recipe=rtl.render(rtl.Term('Select',(e.args[1],rtl.Term('Capture'),rtl.Term('Unknown'))))
    return int(e.args[1].args[1].name)if row['recipe']==recipe else None


def unconditional_valid(row):
    reset=reset_guard(row)
    if reset is None:return None
    e=first.strip(rtl.Parser(row['expanded']).complete().args[2])
    return reset if e==rtl.Term('EVar',(rtl.Term('1'),rtl.Term(str(row['source_valid']))))else None


def discover(ast):
    initial=first.discover(ast);rows=[];residuals=[];expected=0
    if len(initial['handoffs'])==1:
        base=initial['handoffs'][0];links=r.raw_connections(ast);byroot={x['coverage']['root']:x for x in links}
        procs={x['name']:x for x in ast['processes']}
        for item in links:
            if item['provider']['kind']!='copy':continue
            expected+=1;c=item['coverage'];parent=byroot.get(c['source']);dr=unconditional_valid(c)
            if parent is None or dr is None:residuals.append('copy valid has no supported unconditional source transport');continue
            sr=reset_guard(parent['coverage'])
            if sr is None or parent['coverage']['valid_root']!=c['source_valid']:
                residuals.append('copy source reset/validity does not match predecessor');continue
            sp=parent['coverage']['process'];dp=c['process']
            sc=first.event_pair(procs[sp]['events'],sr);dc=first.event_pair(procs[dp]['events'],dr)
            if sc is None or dc is None:residuals.append('copy process edges unsupported');continue
            roles=dict(base_clock=base['source_clock'],base_reset=base['hold']['reset'],
                source_clock=sc,target_clock=dc,source_reset=sr,target_reset=dr)
            routes={k:first.chain(ast,v)for k,v in roles.items()}
            if any(v is None for v in routes.values()):residuals.append('clock/reset alias cycle');continue
            if any(routes[k]['terminal']!=routes['base_clock']['terminal']for k in ['source_clock','target_clock'])or any(
                routes[k]['terminal']!=routes['base_reset']['terminal']for k in ['source_reset','target_reset']):
                residuals.append('copy clock/reset does not share source phase');continue
            rows.append(dict(connection=item,parent=parent,roles=roles,routes=routes))
    return dict(initial_handoffs=len(initial['handoffs']),suffix_edges=rows,expected_copy_edges=expected,residuals=residuals,
        old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,whole_queue_losslessness_proved=False,
        global_inv_proved=False,itree_refinement_proved=False)


def render(ast_path,ast_module,provider):
    provider=Path(provider);ast,profile,paths=origin.raw_binding(ast_path,ast_module);data=discover(ast)
    if data['initial_handoffs']!=1 or not data['suffix_edges']or data['residuals']or len(data['suffix_edges'])!=data['expected_copy_edges']:
        raise ValueError('complete supported raw copy suffix required; no skipped metadata edges')
    td,ts=first.render(ast_path,ast_module,provider)
    tr=fields.verify(provider/'source-transfer','SourceTransfer.v',td,ts)
    jd,js=r.joint.render(ast_path,ast_module,provider/'capture-birth',provider/'coverage',provider/'value',provider/'copies',provider/'joint')
    jr=fields.verify(provider/'joint-history','JointHistory.v',jd,js)
    slots={s['root']:s for s in jd['slots']};base=td['handoffs'][0];bc=base['source_clock'];br=base['hold']['reset']
    bp=ast['module']+'.'+base['hold']['birth']['process'];p=profile['ast']['program'];nodes={}
    for row in data['suffix_edges']:
        for role,route in row['routes'].items():nodes[row['roles'][role]]=route
    clocklist=sorted(nodes);roots=r.joint.roots_coq(clocklist);edges={e['root']:e for route in nodes.values()for e in route['edges']}
    birth=base['hold']['birth'];eventroots=sorted({birth['carrier'],birth['valid_root']}|
        {root for slot in jd['slots']for root in(slot['root'],slot['valid'])})
    def member(root,items):
        proof='or_introl eq_refl'
        for _ in range(items.index(root)):proof='or_intror('+proof+')'
        return '('+proof+')'
    _,analysis,wiring=fields.connected.comb.proposal(profile,list(edges))
    if analysis['residuals']:raise ValueError('suffix actual clock/reset wiring residual')
    ports={x['output_root']:n for n,x in enumerate(analysis['ports'])}
    lines=['From Coq Require Import ZArith List Bool.',f'Require Import {ast_module}.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVProjectionOrigin',
        ' Lang.ExtendedSVProjectionConnection Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression',
        ' Lang.ExtendedSVCaptureBirth Lang.ExtendedSVStallFlush GeneratedSourceTransfer.SourceTransfer.',
        'Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVProjectionOrigin',
        ' ExtendedSVProjectionConnection ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVCaptureBirth ExtendedSVStallFlush.',
        'Module T:=GeneratedSourceTransfer.SourceTransfer. Module J:=T.J. Module C:=T.C. Module F:=T.F.',
        f'Definition clock_roots:list nat:={roots}.',
        f'Lemma clock_words_checked:Forall(fun root=>program_wordb {p} 1 root=true)clock_roots.',
        'Proof. vm_compute;repeat constructor. Qed.',f'Local Opaque {p}.',
        'Definition ClockWords s:=forall root,In root clock_roots ->WordRoot 1 root s.',
        'Definition ClockAllowed ev:=forall root,In root clock_roots ->changed_signal ev<>root.',
        'Lemma words_include_first s:ClockWords s ->T.ClockWords s.',
        'Proof. intros HW root HI;apply HW;unfold T.clock_roots in HI;unfold clock_roots;cbn in *;tauto. Qed.',
        'Lemma allowed_include_first ev:ClockAllowed ev ->T.ClockAllowed ev.',
        'Proof. intros HE root HI;apply HE;unfold T.clock_roots in HI;unfold clock_roots;cbn in *;tauto. Qed.',
        f'Lemma clock_words_initialize:ClockWords(initialize {p} []).',
        'Proof. intros root HI;apply initialize_word;[exact(proj1(Forall_forall _ _)clock_words_checked root HI)|reflexivity]. Qed.',
        f'Lemma clock_words_sampled ev pre:ClockAllowed ev ->ClockWords pre ->ClockWords(phase_driven_state {p} ev pre).',
        'Proof. intros HE HW root HI;unfold phase_driven_state;apply lfp_word;',
        ' [exact(proj1(Forall_forall _ _)clock_words_checked root HI)|].',
        ' unfold WordRoot;rewrite read_signal_write_other by(exact(HE root HI));exact(HW root HI). Qed.',
        f'Lemma clock_words_phase ev pre:ClockAllowed ev ->ClockWords pre ->ClockWords(PhaseSemantics {p} ev pre).',
        f'Proof. intros HE HW root HI;exact(phase_word {p} 1 root ev pre',
        ' (proj1(Forall_forall _ _)clock_words_checked root HI)(HE root HI)(HW root HI)). Qed.']
    for root,route in sorted(nodes.items()):
        lines += [f'Lemma root_{root}_alias seed fixed:CombLFP {p} seed fixed ->',
            f' norm 1(read_signal fixed {root})=norm 1(read_signal fixed {route["terminal"]}).','Proof. intro HL.']
        for e in route['edges']:
            n=ports[e['root']];lines += [f' rewrite(Wires.port_{n}_lfp _ _ HL);cbn[Wires.port_{n}_rhs eval_expr];rewrite norm_idempotent.']
        lines += [' reflexivity. Qed.']
    def normalized_alias(a,b):return f'eq_trans(root_{a}_alias _ _ HL)(eq_sym(root_{b}_alias _ _ HL))'
    exports=[];shift_fields=[];shift_proofs=[]
    for number,row in enumerate(data['suffix_edges']):
        c=row['connection']['coverage'];ci=row['connection']['coverage_index'];dst=slots[c['root']];src=slots[c['source']]
        di=dst['index'];si=src['index'];vr=c['valid_root'];sv=c['source_valid'];dr=row['roles']['target_reset'];dc=row['roles']['target_clock']
        proc=ast['module']+'.'+c['process'];stem=f'stage_{number}'
        for name,a,b in [('clock',dc,bc),('reset',dr,br)]:
            lines += [f'Lemma {stem}_{name}_equal seed fixed:ClockWords fixed ->CombLFP {p} seed fixed ->read_signal fixed {a}=read_signal fixed {b}.',
                f'Proof. intros HW HL;pose proof({normalized_alias(a,b)})as HA.',
                f' pose proof(HW {a}{member(a,clocklist)})as HX;',
                f' pose proof(HW {b}{member(b,clocklist)})as HY;',
                ' unfold WordRoot,Word in HX,HY;rewrite <-HX,<-HY in HA;exact HA. Qed.']
        common=f'ClockAllowed ev ->ClockWords pre ->CombLFP {p} seed0 pre ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->'
        normal=f'norm 1(read_signal(phase_driven_state {p} ev pre){br})<>0%Z ->'
        lines += [f'Theorem {stem}_clocks_agree seed0 seed ev pre:',common,
            f' process_matches_states pre(phase_driven_state {p} ev pre){proc}=',
            f' process_matches_states pre(phase_driven_state {p} ev pre){bp}.',
            'Proof. intros HE HW HL0 HL;pose proof(clock_words_sampled ev pre HE HW)as HD.',
            f' change((edge_fires Posedge(read_signal pre {dc})(read_signal(phase_driven_state {p} ev pre){dc}) ||',
            f' (edge_fires Negedge(read_signal pre {dr})(read_signal(phase_driven_state {p} ev pre){dr}) ||false))%bool=',
            f' (edge_fires Posedge(read_signal pre {bc})(read_signal(phase_driven_state {p} ev pre){bc}) ||',
            f' (edge_fires Negedge(read_signal pre {br})(read_signal(phase_driven_state {p} ev pre){br}) ||false))%bool).',
            f' rewrite({stem}_clock_equal _ _ HW HL0),({stem}_reset_equal _ _ HW HL0),',
            f' ({stem}_clock_equal _ _ HD HL),({stem}_reset_equal _ _ HD HL);reflexivity. Qed.',
            f'Lemma {stem}_reset_one seed ev pre:CombLFP {p} seed(phase_driven_state {p} ev pre) ->',normal,
            f' norm 1(read_signal(phase_driven_state {p} ev pre){dr})=1%Z.',
            f'Proof. intros HL HR;pose proof({normalized_alias(dr,br)})as HA;',
            f' destruct(one_bit_cases(phase_driven_state {p} ev pre){dr})as[HZ|HZ];[rewrite HZ in HA;exfalso;apply HR;now symmetry|exact HZ]. Qed.',
            f'Theorem {stem}_valid_equation seed0 seed ev pre:J.EventAllowed ev ->',common,normal,
            f' norm 1(read_signal(PhaseSemantics {p} ev pre){vr})=',
            f' if process_matches_states pre(phase_driven_state {p} ev pre){bp}',
            f' then norm 1(read_signal pre {sv})else norm 1(read_signal pre {vr}).',
            'Proof. intros HJ HE HW HL0 HL HR.',
            f' assert(HD:changed_signal ev<>{vr}%nat)by(exact(proj1(Forall_forall _ _)HJ {vr}{member(vr,eventroots)})).',
            f' assert(HS:changed_signal ev<>{sv}%nat)by(exact(proj1(Forall_forall _ _)HJ {sv}{member(sv,eventroots)})).',
            f' rewrite(history_phase_projection {p} {vr} 1 {proc} C.root_{vr}_expression C.root_{vr}_valid_certificate ev pre HD),',
            f' ({stem}_clocks_agree seed0 seed ev pre HE HW HL0 HL).',
            f' destruct(process_matches_states pre(phase_driven_state {p} ev pre){bp});[|reflexivity].',
            f' pose proof(bindings_substitute_sound C.coverage_{ci}_bindings C.root_{vr}_expression(phase_driven_state {p} ev pre)',
            f' (C.coverage_{ci}_bindings_agree seed _ HL))as HX;rewrite C.coverage_{ci}_expansion_checked in HX;rewrite <-HX.',
            f' pose proof({stem}_reset_one seed ev pre HL HR)as Hreset.',
            f' cbn[C.coverage_{ci}_expanded eval_expr];rewrite Hreset;replace (1 =? 0)%Z with false by reflexivity;',
            ' rewrite !norm_idempotent.',
            f' rewrite(sampled_root_preserved {p} ev pre {sv} C.root_{sv}_comb_frame HS);reflexivity. Qed.',
            f'Theorem {stem}_tag_equation seed0 seed ev pre g:',common,normal,
            f' J.joint_tag_{di}(J.joint_step ev pre g)=',
            f' if process_matches_states pre(phase_driven_state {p} ev pre){bp}',
            f' then J.joint_tag_{si} g else J.joint_tag_{di} g.',
            'Proof. intros HE HW HL0 HL HR.',
            f' change(F.field_{di}_origin Token ev pre(J.joint_tag_{di} g)(J.joint_tag_{si} g)=',
            f' if process_matches_states pre(phase_driven_state {p} ev pre){bp} then J.joint_tag_{si} g else J.joint_tag_{di} g).',
            f' unfold F.field_{di}_origin,projection_phase_origin;rewrite({stem}_clocks_agree seed0 seed ev pre HE HW HL0 HL).',
            f' destruct(process_matches_states pre(phase_driven_state {p} ev pre){bp});[|reflexivity].',
            f' pose proof({stem}_reset_one seed ev pre HL HR)as Hreset;',
            f' cbn[C.coverage_{ci}_recipe recipe_origin eval_expr];now rewrite Hreset. Qed.',
            f'Theorem {stem}_valid_identity_handoff seed0 seed ev pre g label:J.EventAllowed ev ->',common,normal,
            f' process_matches_states pre(phase_driven_state {p} ev pre){bp}=true ->',
            f' norm 1(read_signal pre {sv})<>0%Z ->J.joint_tag_{si} g=Some label ->',
            f' norm 1(read_signal(PhaseSemantics {p} ev pre){vr})<>0%Z /\\J.joint_tag_{di}(J.joint_step ev pre g)=Some label.',
            f'Proof. intros HJ HE HW HL0 HL HR HF HV HT;rewrite({stem}_valid_equation seed0 seed ev pre HJ HE HW HL0 HL HR),',
            f' ({stem}_tag_equation seed0 seed ev pre g HE HW HL0 HL HR),HF;split;assumption. Qed.']
        exports += [stem+'_clocks_agree',stem+'_valid_equation',stem+'_tag_equation',stem+'_valid_identity_handoff']
        shift_fields += [f'norm 1(read_signal(PhaseSemantics {p} ev pre){vr})=(if process_matches_states pre(phase_driven_state {p} ev pre){bp} then norm 1(read_signal pre {sv})else norm 1(read_signal pre {vr}))',
            f'J.joint_tag_{di}(J.joint_step ev pre g)=(if process_matches_states pre(phase_driven_state {p} ev pre){bp} then J.joint_tag_{si} g else J.joint_tag_{di} g)']
        shift_proofs += [f'{stem}_valid_equation seed0 seed ev pre HJ HE HW HL0 HL HR',
            f'{stem}_tag_equation seed0 seed ev pre g HE HW HL0 HL HR']
    lines += ['Definition PipelineInv pre g:=T.TransportInv pre g /\\ClockWords pre.',
        f'Theorem pipeline_initialize:PipelineInv(initialize {p} [])J.joint_empty.',
        'Proof. split;[exact T.transport_initialize|exact clock_words_initialize]. Qed.',
        'Theorem pipeline_phase seed ev pre g:J.EventAllowed ev ->ClockAllowed ev ->',
        f' CombLFP {p} seed(phase_driven_state {p} ev pre) ->PipelineInv pre g ->',
        f' PipelineInv(PhaseSemantics {p} ev pre)(J.joint_step ev pre g).',
        'Proof. intros HJ HE HL[HI HW];split;[exact(T.transport_phase seed ev pre g HJ(allowed_include_first ev HE)HL HI)|',
        'exact(clock_words_phase ev pre HE HW)]. Qed.',
        'Definition SuffixShift ev pre g:Prop:='+' /\\\n '.join(shift_fields)+'.',
        'Theorem pipeline_shift_preserves_inv seed0 seed ev pre g:J.EventAllowed ev ->ClockAllowed ev ->',
        f' CombLFP {p} seed0 pre ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){br})<>0%Z ->PipelineInv pre g ->',
        f' PipelineInv(PhaseSemantics {p} ev pre)(J.joint_step ev pre g) /\\SuffixShift ev pre g.',
        'Proof. intros HJ HE HL0 HL HR HI;split;[exact(pipeline_phase seed ev pre g HJ HE HL HI)|].',
        ' destruct HI as[HT HW];unfold SuffixShift.']
    for n,proof in enumerate(shift_proofs):
        lines.append(' split;[exact('+proof+')|].'if n<len(shift_proofs)-1 else' exact('+proof+').')
    lines.append('Qed.')
    exports+=['pipeline_initialize','pipeline_phase','pipeline_shift_preserves_inv']
    for name in exports:lines.append('Print Assumptions '+name+'.')
    return dict(**data,ast_sha256=ast['source_sha256'],coq_load_paths=paths,provider_hashes=[tr['object_sha256'],jr['object_sha256']],
        audited_exports=len(analysis['ports'])+len(exports)),'Module Wires.\n'+wiring+'\nEnd Wires.\n'+'\n'.join(lines)+'\n'


def check(ast_path,ast_module,provider,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module,provider)
    except ValueError as error:
        result=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,global_inv_proved=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result
    path=output/'PipelineTransfer.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    for folder,namespace in [('capture-birth','GeneratedCaptureBirth'),('coverage','GeneratedRecipeCoverage'),('value','GeneratedConnectedProjections'),('copies','GeneratedMetadataCopies'),('joint','GeneratedCoveredFields'),('joint-history','GeneratedJointHistory'),('stall-flush','GeneratedStallFlush'),('source-hold','GeneratedSourceHold'),('source-transfer','GeneratedSourceTransfer')]:
        flags+=['-R',str((Path(provider)/folder).resolve()),namespace]
    flags+=['-R',str(output.resolve()),'GeneratedPipelineTransfer'];start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    result=dict(accepted=False,native_started=True,scope='actual valid/tag shift on every supported raw copy suffix edge, not queue/ISA refinement',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),old_inv_read=False,
        old_pending_read=False,old_cpu_proofs_used=False,whole_queue_losslessness_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout;result['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedPipelineTransfer.PipelineTransfer'],output/'coqchk.log',deadline-time.monotonic())
            result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    result['overall_seconds']=time.monotonic()-start
    if result['accepted']:result['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','provider','output']:parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--ast-module',required=True);a=parser.parse_args()
    result=check(a.ast,a.ast_module,a.provider,a.output);print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
