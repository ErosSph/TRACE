"""Infer physical falling-edge retirement and prove actual head consumption.

Raw event/alias/NOT/reset analysis supplies roles. Fresh exact-checked pipeline
and retirement providers supply proofs, never an old CPU INV. A phase-aware
physical queue candidate is synthesized; complete cycle closure remains separate.
"""
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_pending_pipeline_transfer as pipeline
from cpu_certificate_acceptance import run_stage
first=pipeline.first;r=pipeline.r;fields=pipeline.fields;origin=pipeline.origin;rtl=pipeline.rtl


def linear_nodes(ast,base,candidate):
    connections=r.raw_connections(ast);slots=r.joint.layout([base['hold']['birth']],connections)
    byroot={s['root']:s for s in slots};b=base['hold']['birth']
    nodes=[dict(root=b['carrier'],valid=b['valid_root'],process=b['process'],index=None)]
    remaining=list(connections)
    while remaining:
        matches=[item for item in remaining if item['coverage']['source']==nodes[-1]['root']]
        if len(matches)!=1:raise ValueError('one linear metadata chain required; forks/disconnection not an ordered queue')
        item=matches[0];row=item['coverage'];slot=byroot[row['root']]
        if row['source_valid']!=nodes[-1]['valid']:raise ValueError('linear predecessor validity mismatch')
        nodes.append(dict(root=row['root'],valid=row['valid_root'],process=row['process'],index=slot['index']))
        remaining.remove(item)
    if len(nodes)<2 or nodes[-1]['root']!=candidate['slot']['root']:raise ValueError('physical cut is not the terminal node')
    return nodes


def inverted_clock(ast,root):
    route=first.chain(ast,root)
    if route is None:return None
    driver=route['terminal'];writers=[p for p in ast['processes']if p['kind']!='Initial'and driver in p['writers']]
    if len(writers)!=1 or writers[0]['kind']!='Combinational':return None
    body=writers[0]['body']
    if body.name!='SAssign'or body.args[0].name!='false'or body.args[2]!=rtl.Term('LVar',(rtl.Term('1'),rtl.Term(str(driver)))):return None
    e=body.args[1]
    if e.name!='EUnary'or e.args[:2]!=(rtl.Term('1'),rtl.Term('UNot'))or not first.hold.control.is_var(e.args[2],1):return None
    source=int(e.args[2].args[1].name);source_route=first.chain(ast,source)
    if source_route is None:return None
    return dict(output_route=route,driver=driver,source=source,source_route=source_route,process=writers[0]['name'])


def discover(ast):
    cuts=r.discover(ast);pd=pipeline.discover(ast);initial=first.discover(ast);rows=[];residuals=[]
    if len(cuts['candidates'])==len(initial['handoffs'])==1 and pd['suffix_edges']and not pd['residuals']:
        candidate=cuts['candidates'][0];base=initial['handoffs'][0];conditions=candidate['write']['operation_conditions']
        if len(conditions)!=1 or not conditions[0]['positive']:
            residuals.append('normal operational envelope is not one positive reset guard')
        else:
            reset=rtl.Parser(conditions[0]['expression']).complete()
            if not first.hold.control.is_var(reset,1):residuals.append('operational reset is not a scalar bit')
            else:
                rr=int(reset.args[1].name);clock=first.event_pair(candidate['write']['events'],rr)
                inv=inverted_clock(ast,clock)if clock is not None else None
                reset_route=first.chain(ast,rr)
                if inv is None or reset_route is None:residuals.append('physical cut has no supported inverted clock/reset')
                elif inv['source_route']['terminal']!=base['routes']['source_clock']['terminal']or reset_route['terminal']!=base['routes']['source_reset']['terminal']:
                    residuals.append('cut clock/reset source differs from capture pipeline')
                else:
                    try:nodes=linear_nodes(ast,base,candidate)
                    except ValueError as error:residuals.append(str(error))
                    else:rows.append(dict(candidate=candidate,base=base,nodes=nodes,inverter=inv,rf_clock=clock,rf_reset=rr,reset_route=reset_route))
    return dict(phases=rows,residuals=residuals,old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,
        falling_queue_success_proved=False,full_queue_inv_preservation_proved=False,global_inv_proved=False,itree_refinement_proved=False)


def render(ast_path,ast_module,provider):
    provider=Path(provider);ast,profile,paths=origin.raw_binding(ast_path,ast_module);data=discover(ast)
    if len(data['phases'])!=1:raise ValueError('one complete raw linear pipeline/inverted-retirement phase required')
    pd,ps=pipeline.render(ast_path,ast_module,provider)
    pr=fields.verify(provider/'pipeline-transfer','PipelineTransfer.v',pd,ps)
    rd,rs=r.render(ast_path,ast_module,provider)
    rr=fields.verify(provider/'retirement-cut','RetirementCandidate.v',rd,rs)
    row=data['phases'][0];base=row['base'];b=base['hold']['birth'];nodes=row['nodes'];terminal=nodes[-1]
    p=profile['ast']['program'];bc=base['source_clock'];br=base['hold']['reset'];fc=row['rf_clock'];fr=row['rf_reset']
    bp=ast['module']+'.'+b['process'];rp=ast['module']+'.'+row['candidate']['write']['process'];inv=row['inverter']
    named_routes=dict(base_clock=base['routes']['source_clock'],base_reset=base['routes']['source_reset'],
        rf_clock=inv['output_route'],inverter_source=inv['source_route'],rf_reset=row['reset_route'])
    roots=sorted({v for edge in pd['suffix_edges']for v in edge['roles'].values()}|{fc,fr})
    def member(root,items):
        proof='or_introl eq_refl'
        for _ in range(items.index(root)):proof='or_intror('+proof+')'
        return '('+proof+')'
    eventroots=sorted({v for node in nodes for v in(node['root'],node['valid'])})
    edges={e['root']:e for route in named_routes.values()for e in route['edges']};targets=list(edges)+[inv['driver']]
    _,analysis,wiring=fields.connected.comb.proposal(profile,targets)
    if analysis['residuals']:raise ValueError('actual inverter/reset wiring residual')
    ports={x['output_root']:n for n,x in enumerate(analysis['ports'])}
    lines=['From Coq Require Import List ZArith Bool.',f'Require Import {ast_module}.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVStallFlush',
        ' Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPending Lang.ExtendedSVCaptureAccounting Lang.ExtendedSVScalarHistory Lang.ExtendedSVProjectionOrigin',
        ' Lib.CheckedPendingQueue Lib.CheckedPendingQueueComplete GeneratedPipelineTransfer.PipelineTransfer GeneratedRetirementCandidate.RetirementCandidate.',
        'Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVStallFlush ExtendedSVCapturedPending',
        ' ExtendedSVCaptureBirth ExtendedSVScalarHistory ExtendedSVProjectionOrigin.',
        'Module P:=GeneratedPipelineTransfer.PipelineTransfer. Module T:=P.T. Module J:=P.J.',
        'Module B:=T.B. Module C:=P.C. Module F:=P.F.',
        'Module R:=GeneratedRetirementCandidate.RetirementCandidate. Module A:=ExtendedSVCaptureAccounting.',
        f'Definition clock_roots:list nat:={r.joint.roots_coq(roots)}.',
        f'Lemma clock_words_checked:Forall(fun root=>program_wordb {p} 1 root=true)clock_roots.',
        'Proof. vm_compute;repeat constructor. Qed.',f'Local Opaque {p}.',
        'Definition ClockWords s:=forall root,In root clock_roots ->WordRoot 1 root s.',
        'Definition ClockAllowed ev:=forall root,In root clock_roots ->changed_signal ev<>root.',
        'Lemma words_include_pipeline s:ClockWords s ->P.ClockWords s.',
        'Proof. intros HW root HI;apply HW;unfold P.clock_roots in HI;unfold clock_roots;cbn in *;tauto. Qed.',
        'Lemma allowed_include_pipeline ev:ClockAllowed ev ->P.ClockAllowed ev.',
        'Proof. intros HE root HI;apply HE;unfold P.clock_roots in HI;unfold clock_roots;cbn in *;tauto. Qed.',
        f'Lemma clock_words_initialize:ClockWords(initialize {p} []).',
        'Proof. intros root HI;apply initialize_word;[exact(proj1(Forall_forall _ _)clock_words_checked root HI)|reflexivity]. Qed.',
        f'Lemma clock_words_sampled ev pre:ClockAllowed ev ->ClockWords pre ->ClockWords(phase_driven_state {p} ev pre).',
        'Proof. intros HE HW root HI;unfold phase_driven_state;apply lfp_word;',
        ' [exact(proj1(Forall_forall _ _)clock_words_checked root HI)|].',
        ' unfold WordRoot;rewrite read_signal_write_other by(exact(HE root HI));exact(HW root HI). Qed.',
        f'Lemma clock_words_phase ev pre:ClockAllowed ev ->ClockWords pre ->ClockWords(PhaseSemantics {p} ev pre).',
        f'Proof. intros HE HW root HI;exact(phase_word {p} 1 root ev pre',
        ' (proj1(Forall_forall _ _)clock_words_checked root HI)(HE root HI)(HW root HI)). Qed.',
        'Lemma raw_bit_cases s root:ClockWords s ->In root clock_roots ->read_signal s root=0%Z \/read_signal s root=1%Z.',
        'Proof. intros HW HI;pose proof(HW root HI)as Hword;unfold WordRoot,Word in Hword;',
        'destruct(one_bit_cases s root)as[H|H];[left|right];now rewrite Hword,H. Qed.']
    for name,route in named_routes.items():
        start=dict(base_clock=bc,base_reset=br,rf_clock=fc,inverter_source=inv['source'],rf_reset=fr)[name]
        lines += [f'Lemma {name}_alias seed fixed:CombLFP {p} seed fixed ->norm 1(read_signal fixed {start})=norm 1(read_signal fixed {route["terminal"]}).',
            'Proof. intro HL.']
        for edge in route['edges']:
            n=ports[edge['root']];lines += [f' rewrite(Wire.port_{n}_lfp _ _ HL);cbn[Wire.port_{n}_rhs eval_expr];rewrite norm_idempotent.']
        lines += [' reflexivity. Qed.']
    n=ports[inv['driver']]
    lines += [f'Lemma rf_clock_norm seed fixed:CombLFP {p} seed fixed ->',
        f' norm 1(read_signal fixed {fc})=norm 1(Z.lnot(norm 1(read_signal fixed {bc}))).','Proof. intro HL.']
    if fc!=inv['driver']:lines+=[' rewrite(rf_clock_alias _ _ HL).']
    lines += [f' rewrite(Wire.port_{n}_lfp _ _ HL);cbn[Wire.port_{n}_rhs eval_expr];rewrite !norm_idempotent.',
        f' assert(HS:norm 1(read_signal fixed {inv["source"]})=norm 1(read_signal fixed {bc}))by',
        ' (exact(eq_trans(inverter_source_alias _ _ HL)(eq_sym(base_clock_alias _ _ HL)))). now rewrite HS. Qed.',
        f'Lemma rf_clock_raw seed fixed:ClockWords fixed ->CombLFP {p} seed fixed ->',
        f' read_signal fixed {fc}=(if Z.eqb(read_signal fixed {bc})0%Z then 1%Z else 0%Z).',
        f'Proof. intros HW HL;pose proof(HW {fc}{member(fc,roots)})as HF;pose proof(HW {bc}{member(bc,roots)})as HB;',
        ' unfold WordRoot,Word in HF,HB;rewrite HF,(rf_clock_norm seed fixed HL),HB;',
        f' destruct(one_bit_cases fixed {bc})as[H|H];rewrite H;reflexivity. Qed.',
        'Lemma base_reset_raw_one ev pre:ClockAllowed ev ->ClockWords pre ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){br})<>0%Z ->',
        f' read_signal(phase_driven_state {p} ev pre){br}=1%Z.',
        'Proof. intros HE HW HR;pose proof(clock_words_sampled ev pre HE HW)as HD;',
        f' pose proof(HD {br}{member(br,roots)})as HWB;unfold WordRoot,Word in HWB;',
        f' destruct(one_bit_cases(phase_driven_state {p} ev pre){br})as[H|H];[contradiction|now rewrite HWB,H]. Qed.',
        'Lemma rf_reset_norm_one seed ev pre:',f'CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){br})<>0%Z ->',
        f' norm 1(read_signal(phase_driven_state {p} ev pre){fr})=1%Z.',
        'Proof. intros HL HR;pose proof(eq_trans(rf_reset_alias _ _ HL)(eq_sym(base_reset_alias _ _ HL)))as HA;',
        f' destruct(one_bit_cases(phase_driven_state {p} ev pre){fr})as[H|H];[rewrite H in HA;exfalso;apply HR;now symmetry|exact H]. Qed.',
        f'Definition Falling ev pre:=edge_fires Negedge(read_signal pre {bc})(read_signal(phase_driven_state {p} ev pre){bc}).',
        f'Definition Rising ev pre:=edge_fires Posedge(read_signal pre {bc})(read_signal(phase_driven_state {p} ev pre){bc}).']
    common=f'ClockAllowed ev ->ClockWords pre ->CombLFP {p} seed0 pre ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->'
    normal=f'norm 1(read_signal(phase_driven_state {p} ev pre){br})<>0%Z ->'
    lines += ['Theorem actual_retirement_process_falls seed0 seed ev pre:',common,normal,
        f' process_matches_states pre(phase_driven_state {p} ev pre){rp}=Falling ev pre.',
        'Proof. intros HE HW HL0 HL HR;pose proof(clock_words_sampled ev pre HE HW)as HD;',
        f' pose proof(HD {fr}{member(fr,roots)})as HWR;unfold WordRoot,Word in HWR;',
        ' pose proof(rf_reset_norm_one seed ev pre HL HR)as HRone.',
        f' assert(HRF:read_signal(phase_driven_state {p} ev pre){fr}=1%Z)by(now rewrite HWR,HRone).',
        f' change((edge_fires Posedge(read_signal pre {fc})(read_signal(phase_driven_state {p} ev pre){fc}) ||',
        f' (edge_fires Negedge(read_signal pre {fr})(read_signal(phase_driven_state {p} ev pre){fr}) ||false))%bool=Falling ev pre).',
        ' rewrite(rf_clock_raw _ _ HW HL0),(rf_clock_raw _ _ HD HL),HRF;unfold Falling,edge_fires;',
        f' destruct(raw_bit_cases pre {bc} HW {member(bc,roots)})as[HA|HA];',
        f' destruct(raw_bit_cases(phase_driven_state {p} ev pre){bc} HD {member(bc,roots)})as[HB|HB];',
        f' rewrite HA,HB;destruct(Z.eqb(read_signal pre {fr})0%Z);rewrite ?andb_false_r,?orb_false_r;reflexivity. Qed.']
    lines += ['Theorem actual_cut_fires_on_falling seed0 seed ev pre:',common,normal,
        ' R.cut_fires ev pre=Falling ev pre.',
        'Proof. intros HE HW HL0 HL HR;unfold R.cut_fires;',
        ' rewrite(actual_retirement_process_falls seed0 seed ev pre HE HW HL0 HL HR).',
        ' assert(HO:R.operation_enabled(phase_driven_state '+p+' ev pre)=true).',
        ' { unfold R.operation_enabled;cbn[eval_expr];rewrite(rf_reset_norm_one seed ev pre HL HR);reflexivity. }',
        ' rewrite HO;apply andb_true_r. Qed.',
        'Lemma source_matches_rising ev pre:ClockAllowed ev ->ClockWords pre ->',normal,
        f' process_matches_states pre(phase_driven_state {p} ev pre){bp}=Rising ev pre.',
        'Proof. intros HE HW HR;pose proof(base_reset_raw_one ev pre HE HW HR)as HB;',
        f' change((Rising ev pre || (edge_fires Negedge(read_signal pre {br})(read_signal(phase_driven_state {p} ev pre){br}) ||false))%bool=Rising ev pre).',
        ' rewrite HB;unfold edge_fires;change((Rising ev pre || (negb(Z.eqb(read_signal pre '+str(br)+')0%Z) && false ||false))%bool=Rising ev pre);',
        ' now rewrite andb_false_r,!orb_false_r. Qed.',
        'Theorem falling_has_no_capture seed0 seed ev pre:',common,normal,
        f' Falling ev pre=true ->process_matches_states pre(phase_driven_state {p} ev pre){bp}=false.',
        'Proof. intros HE HW HL0 HL HR HF;rewrite(source_matches_rising ev pre HE HW HR);',
        ' unfold Falling,edge_fires in HF;apply andb_true_iff in HF as[HO HN];unfold Rising,edge_fires;',
        ' rewrite HN;apply andb_false_r. Qed.',
        'Lemma falling_pre_clock_high ev pre:ClockWords pre ->Falling ev pre=true ->',f' norm 1(read_signal pre {bc})=1%Z.',
        f'Proof. intros HW HF;destruct(raw_bit_cases pre {bc} HW {member(bc,roots)})as[H|H];',
        ' [exfalso;unfold Falling,edge_fires in HF;rewrite H in HF;discriminate|rewrite H;reflexivity]. Qed.',
        'Theorem falling_admits_nothing seed0 seed ev pre g:',common,normal,
        ' Falling ev pre=true ->J.pending_admitted ev pre g=[].',
        'Proof. intros HE HW HL0 HL HR HF;pose proof(falling_has_no_capture seed0 seed ev pre HE HW HL0 HL HR HF)as HN;',
        ' unfold J.pending_admitted,observed_births,phase_decision;rewrite HN;reflexivity. Qed.']
    def tag(node,g='g'):
        return f'current(J.joint_birth {g})'if node['index']is None else f'J.joint_tag_{node["index"]} {g}'
    def node_match(node):
        if node['index']is None:return None
        if node['process']==base['connection']['coverage']['process']:
            return first_match
        for i,x in enumerate(pd['suffix_edges']):
            if x['connection']['coverage']['process']==node['process']:
                return f'P.stage_{i}_clocks_agree seed0 seed ev pre HP HWp HL0 HL'
        raise ValueError('no new actual clock equality for linear node')
    # The first stage uses T's exact checked aliases, obtained via P's inclusions.
    first_match='eq_sym(T.actual_process_clocks_agree seed0 seed ev pre (P.allowed_include_first ev HP)(P.words_include_first pre HWp)HL0 HL)'
    for i,node in enumerate(nodes):
        proc=ast['module']+'.'+node['process'];v=node['valid'];cert=f'B.root_{v}_birth_certificate'if node['index']is None else f'C.root_{v}_valid_certificate'
        expr=f'B.root_{v}_expression'if node['index']is None else f'C.root_{v}_expression'
        match=node_match(node)
        if match is not None:
            lines += [f'Lemma node_{i}_clocks seed0 seed ev pre:',common,
                f' process_matches_states pre(phase_driven_state {p} ev pre){proc}=process_matches_states pre(phase_driven_state {p} ev pre){bp}.',
                'Proof. intros HE HW HL0 HL;pose proof(allowed_include_pipeline ev HE)as HP;',
                f' pose proof(words_include_pipeline pre HW)as HWp;exact({match}). Qed.']
        lines += [f'Lemma node_{i}_valid_idle seed0 seed ev pre:J.EventAllowed ev ->',common,
            f' process_matches_states pre(phase_driven_state {p} ev pre){bp}=false ->',
            f' norm 1(read_signal(PhaseSemantics {p} ev pre){v})=norm 1(read_signal pre {v}).',
            'Proof. intros HJ HE HW HL0 HL HF.',
            f' assert(HV:changed_signal ev<>{v}%nat)by(exact(proj1(Forall_forall _ _)HJ {v}{member(v,eventroots)})).',
            f' rewrite(history_phase_projection {p} {v} 1 {proc} {expr} {cert} ev pre HV)'+
                (f',(node_{i}_clocks seed0 seed ev pre HE HW HL0 HL)'if match is not None else'')+',HF;reflexivity. Qed.']
    lines += ['Lemma joint_idle seed0 seed ev pre g:',common,
        f' process_matches_states pre(phase_driven_state {p} ev pre){bp}=false ->J.joint_step ev pre g=g.',
        'Proof. intros HE HW HL0 HL HF;unfold J.joint_step,B.capture_0_step,ghost_step,phase_decision,',
        ','.join(f'F.field_{node["index"]}_origin'for node in nodes[1:])+',projection_phase_origin;']
    for i in range(1,len(nodes)):lines += [f' rewrite(node_{i}_clocks seed0 seed ev pre HE HW HL0 HL).']
    lines += [' rewrite HF;destruct g as[old '+ ' '.join('tag'+str(i)for i in range(len(nodes)-1))+'];destruct old;reflexivity. Qed.',
        'Definition slot_tokens s valid(tag:option Token):=match tag with None=>[]|Some token=>',
        ' if Z.eqb(norm 1(read_signal s valid))0%Z then[]else[token]end.',
        'Definition lower_view s(g:J.JointGhost):='+ '++'.join(f'slot_tokens s {node["valid"]}({tag(node)})'for node in reversed(nodes[:-1]))+'.',
        f'Definition retire_view s(g:J.JointGhost):=slot_tokens s {terminal["valid"]}({tag(terminal)}).',
        f'Definition waiting_view s g:=if Z.eqb(norm 1(read_signal s {bc}))0%Z then lower_view s g else retire_view s g++lower_view s g.',
        'Definition QueueCandidate pre g a:=P.PipelineInv pre g /\\R.AccountedInv pre g a /\\ClockWords pre /\\A.waiting a=waiting_view pre g.',
        f'Theorem queue_candidate_initialize:QueueCandidate(initialize {p} [])J.joint_empty A.empty.',
        'Proof. split;[exact P.pipeline_initialize|]. split;[exact R.accounted_initialization|]. split;[exact clock_words_initialize|].',
        ' unfold waiting_view,retire_view,lower_view,J.joint_empty;cbn[A.waiting J.joint_birth current '+
        ' '.join('J.joint_tag_'+str(node['index'])for node in nodes[1:])+' slot_tokens];destruct(Z.eqb _ 0%Z);reflexivity. Qed.',
        'Lemma lower_view_idle seed0 seed ev pre g:J.EventAllowed ev ->',common,
        f' process_matches_states pre(phase_driven_state {p} ev pre){bp}=false ->',
        f' lower_view(PhaseSemantics {p} ev pre)(J.joint_step ev pre g)=lower_view pre g.',
        'Proof. intros HJ HE HW HL0 HL HF;rewrite(joint_idle seed0 seed ev pre g HE HW HL0 HL HF);unfold lower_view,slot_tokens;']
    for i in range(len(nodes)-1):lines += [f' rewrite(node_{i}_valid_idle seed0 seed ev pre HJ HE HW HL0 HL HF).']
    lines += [' reflexivity. Qed.',
        'Theorem actual_falling_retiring_view seed0 seed ev pre g:',common,normal,
        ' J.AuthenticInv pre g ->Falling ev pre=true ->R.retiring_candidate ev pre g=Some(retire_view pre g).',
        'Proof. intros HE HW HL0 HL HR HI HF;destruct(R.candidate_defined ev pre g HI)as[tokens HC].',
        f' change((if R.cut_fires ev pre then if Z.eqb(norm 1(read_signal pre {terminal["valid"]}))0%Z then Some[]else',
        f' match {tag(terminal)} with Some token=>Some[token]|None=>None end else Some[])=Some tokens)in HC.',
        f' change((if R.cut_fires ev pre then if Z.eqb(norm 1(read_signal pre {terminal["valid"]}))0%Z then Some[]else',
        f' match {tag(terminal)} with Some token=>Some[token]|None=>None end else Some[])=Some(retire_view pre g)).',
        ' rewrite(actual_cut_fires_on_falling seed0 seed ev pre HE HW HL0 HL HR),HF in HC|-*;',
        ' unfold retire_view,slot_tokens;',
        f' destruct(Z.eqb(norm 1(read_signal pre {terminal["valid"]}))0%Z)eqn:HV;destruct({tag(terminal)})as[token|]eqn:HT;rewrite ?HV;try reflexivity;discriminate HC. Qed.',
        'Theorem actual_falling_accounting seed0 seed ev pre g a:J.EventAllowed ev ->ClockAllowed ev ->',
        f' CombLFP {p} seed0 pre ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->',normal,
        ' Falling ev pre=true ->QueueCandidate pre g a ->exists next,',
        ' R.accounted_step ev pre g a 0=Some next /\\',
        f' R.AccountedInv(PhaseSemantics {p} ev pre)(J.joint_step ev pre g)next /\\',
        f' P.PipelineInv(PhaseSemantics {p} ev pre)(J.joint_step ev pre g) /\\ClockWords(PhaseSemantics {p} ev pre) /\\',
        f' A.waiting next=lower_view(PhaseSemantics {p} ev pre)(J.joint_step ev pre g) /\\',
        ' A.retired next=A.retired a++retire_view pre g /\\A.cancelled next=A.cancelled a.',
        'Proof. intros HJ HE HL0 HL HR HF[HP[HA[HW HQ]]].',
        ' pose proof(actual_falling_retiring_view seed0 seed ev pre g HE HW HL0 HL HR(proj1 HA)HF)as HC.',
        ' pose proof(falling_admits_nothing seed0 seed ev pre g HE HW HL0 HL HR HF)as HB.',
        ' assert(Hprefix:A.waiting a=retire_view pre g++lower_view pre g).',
        ' { rewrite HQ;unfold waiting_view;rewrite(falling_pre_clock_high ev pre HW HF);reflexivity. }',
        ' assert(HS:CheckedPendingQueue.step token_eq_dec(A.waiting a)(J.pending_admitted ev pre g)(retire_view pre g)0=Some(lower_view pre g,[])).',
        ' { apply CheckedPendingQueueComplete.no_cancel_complete;rewrite HB,app_nil_r;exact Hprefix. }',
        ' set(next:=A.Build_Accounts(A.retired a++retire_view pre g)(lower_view pre g)(A.cancelled a)).',
        ' assert(Hstep:R.accounted_step ev pre g a 0=Some next).',
        ' { unfold R.accounted_step;rewrite HC;unfold A.advance;rewrite HS;cbn[A.retired A.cancelled];now rewrite app_nil_r. }',
        ' exists next;split;[exact Hstep|]. split;[exact(R.accounted_phase_candidate seed ev pre g a 0 next HJ HL HA Hstep)|].',
        ' split;[exact(P.pipeline_phase seed ev pre g HJ(allowed_include_pipeline ev HE)HL HP)|].',
        ' split;[exact(clock_words_phase ev pre HE HW)|]. split.',
        ' - change(lower_view pre g=lower_view(PhaseSemantics '+p+' ev pre)(J.joint_step ev pre g));symmetry;',
        '   exact(lower_view_idle seed0 seed ev pre g HJ HE HW HL0 HL(falling_has_no_capture seed0 seed ev pre HE HW HL0 HL HR HF)).',
        ' - split;reflexivity. Qed.']
    exports=['clock_words_initialize','clock_words_phase','actual_retirement_process_falls','actual_cut_fires_on_falling',
        'falling_has_no_capture','falling_admits_nothing','joint_idle','queue_candidate_initialize','lower_view_idle',
        'actual_falling_retiring_view','actual_falling_accounting']
    for name in exports:lines+=['Print Assumptions '+name+'.']
    return dict(**data,ast_sha256=ast['source_sha256'],coq_load_paths=paths,provider_hashes=[pr['object_sha256'],rr['object_sha256']],
        audited_exports=len(analysis['ports'])+len(exports)),'Module Wire.\n'+wiring+'\nEnd Wire.\n'+'\n'.join(lines)+'\n'


def check(ast_path,ast_module,provider,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module,provider)
    except ValueError as error:
        result=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,global_inv_proved=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result
    path=output/'RetirementPhase.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for binding in data['coq_load_paths']:flags+=['-R',binding['directory'],binding['namespace']]
    for folder,namespace in [('capture-birth','GeneratedCaptureBirth'),('coverage','GeneratedRecipeCoverage'),('value','GeneratedConnectedProjections'),('copies','GeneratedMetadataCopies'),('joint','GeneratedCoveredFields'),('joint-history','GeneratedJointHistory'),('stall-flush','GeneratedStallFlush'),('source-hold','GeneratedSourceHold'),('source-transfer','GeneratedSourceTransfer'),('pipeline-transfer','GeneratedPipelineTransfer'),('retirement-cut','GeneratedRetirementCandidate')]:
        flags+=['-R',str((Path(provider)/folder).resolve()),namespace]
    flags+=['-R',str(output.resolve()),'GeneratedRetirementPhase'];start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    result=dict(accepted=False,native_started=True,scope='actual falling physical cut consumes generated waiting head and restores accounting; not whole-cycle QueueCandidate/ISA refinement',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),old_inv_read=False,
        old_pending_read=False,old_cpu_proofs_used=False,falling_queue_success_proved=False,full_queue_inv_preservation_proved=False,
        global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout;result['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedRetirementPhase.RetirementPhase'],output/'coqchk.log',deadline-time.monotonic())
            result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    result['overall_seconds']=time.monotonic()-start
    if result['accepted']:result.update(object_sha256=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest(),falling_queue_success_proved=True)
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','provider','output']:parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--ast-module',required=True);args=parser.parse_args()
    result=check(args.ast,args.ast_module,args.provider,args.output);print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
