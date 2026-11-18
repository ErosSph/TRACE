"""Restore a generated physical pending queue on actual normal phases.

Roles come from raw AST capture/control/metadata paths. Fresh clock-frame and
pipeline certificates are checked exactly; no historical CPU invariant is read.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_clock_frame as clock
from cpu_certificate_acceptance import run_stage
phase=clock.phase;fields=clock.fields;origin=clock.origin;rtl=clock.rtl


def discover(ast):
    data=clock.discover(ast);rows=[];residuals=list(data['residuals'])
    for row in data['clock_frames']:
        birth=row['phase']['base']['hold']['birth']
        if len(birth['sources'])!=1 or birth['sources'][0]==birth['carrier']:
            residuals.append('one distinct actual capture source required');continue
        rows.append(dict(frame=row,capture_source=birth['sources'][0]))
    return dict(rising_paths=rows,residuals=residuals,old_inv_read=False,old_pending_read=False,
        old_cpu_proofs_used=False,full_cycle_preservation_proved=False,global_inv_proved=False,itree_refinement_proved=False)


def render(ast_path,ast_module,provider):
    provider=Path(provider);ast,profile,paths=origin.raw_binding(ast_path,ast_module);data=discover(ast)
    if len(data['rising_paths'])!=1:raise ValueError('one complete actual linear rising path required')
    cd,cs=clock.render(ast_path,ast_module,provider)
    cr=fields.verify(provider/'clock-frame','ClockFrame.v',cd,cs)
    row=data['rising_paths'][0];q=row['frame']['phase'];base=q['base'];h=base['hold'];b=h['birth']
    nodes=q['nodes'];p=profile['ast']['program'];proc=ast['module']+'.'+b['process']
    root=b['carrier'];valid=b['valid_root'];reset=h['reset'];enable=h['enable'];flush=h['flush'];bi=h['birth_index']
    target=nodes[1];target_valid=target['valid'];target_index=target['index'];source=row['capture_source']
    coverage=base['connection']['coverage_index'];bc=base['source_clock'];dr=base['target_reset']
    eventroots=sorted({v for n in nodes for v in(n['root'],n['valid'])})
    def member(value,items):
        term='or_introl eq_refl'
        for _ in range(items.index(value)):term='or_intror('+term+')'
        return '('+term+')'
    def tag(node,g):
        return f'current(J.joint_birth {g})'if node['index']is None else f'J.joint_tag_{node["index"]} {g}'
    sampled=f'(phase_driven_state {p} ev pre)';post=f'(PhaseSemantics {p} ev pre)';nextg='(J.joint_step ev pre g)'
    common=f'J.EventAllowed ev ->Q.ClockAllowed ev ->Q.ClockWords pre ->CombLFP {p} seed0 pre ->CombLFP {p} seed{sampled} ->'
    normal=f'norm 1(read_signal{sampled}{reset})<>0%Z ->Q.Rising ev pre=true ->'
    hf=f'process_matches_states pre{sampled}{proc}'
    lines=['From Coq Require Import List ZArith Bool.',f'Require Import {ast_module}.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVStallFlush',
        ' Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPending Lang.ExtendedSVScalarHistory Lang.ExtendedSVInstructionOrigin',
        ' Lang.ExtendedSVScalarExpression Lang.ExtendedSVProjectionOrigin Lang.ExtendedSVProjectionConnection',
        ' Lib.CheckedPendingQueue Lib.CheckedPendingQueueComplete GeneratedClockFrame.ClockFrame.',
        'Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVStallFlush ExtendedSVCaptureBirth',
        ' ExtendedSVCapturedPending ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVProjectionOrigin ExtendedSVProjectionConnection ExtendedSVInstructionOrigin.',
        'Module W:=GeneratedClockFrame.ClockFrame. Module Q:=W.Q. Module P:=Q.P. Module T:=P.T.',
        'Module J:=Q.J. Module B:=Q.B. Module C:=Q.C. Module F:=Q.F. Module H:=T.H. Module R:=Q.R. Module A:=Q.A.',
        f'Local Opaque {p}.',
        'Lemma rising_fires ev pre:Q.ClockAllowed ev ->Q.ClockWords pre ->',normal[:-len('Q.Rising ev pre=true ->')],
        f'Q.Rising ev pre=true ->{hf}=true.',
        'Proof. intros HE HW HR HF;rewrite(Q.source_matches_rising ev pre HE HW HR);exact HF. Qed.',
        'Lemma rising_not_falling ev pre:Q.Rising ev pre=true ->Q.Falling ev pre=false.',
        'Proof. unfold Q.Rising,Q.Falling,edge_fires;intro HF;apply andb_true_iff in HF as[HO HN];',
        ' rewrite HO;reflexivity. Qed.',
        f'Lemma rising_pre_low ev pre:Q.Rising ev pre=true ->norm 1(read_signal pre {bc})=0%Z.',
        'Proof. unfold Q.Rising,edge_fires;intro HF;apply andb_true_iff in HF as[HO HN];apply Z.eqb_eq in HO;now rewrite HO. Qed.',
        'Lemma rising_post_high ev pre:Q.ClockAllowed ev ->Q.ClockWords pre ->Q.Rising ev pre=true ->',
        f' norm 1(read_signal{post}{bc})=1%Z.',
        'Proof. intros HE HW HF;rewrite W.clock_phase_norm;',
        ' pose proof(Q.clock_words_sampled ev pre HE HW)as HD;',
        f' destruct(one_bit_cases{sampled}{bc})as[HZ|HZ];[|exact HZ];',
        f' pose proof(HD {bc}{member(bc,sorted({v for e in phase.pipeline.discover(ast)["suffix_edges"]for v in e["roles"].values()}|{q["rf_clock"],q["rf_reset"]}))})as Hword;',
        ' unfold WordRoot,Word in Hword;unfold Q.Rising,edge_fires in HF;rewrite Hword,HZ in HF;',
        ' rewrite andb_false_r in HF;discriminate. Qed.',
        'Lemma rising_retires_nothing seed0 seed ev pre g:',common,normal,
        ' R.retiring_candidate ev pre g=Some[].',
        'Proof. intros HJ HE HW HL0 HL HR HF;unfold R.retiring_candidate;',
        ' rewrite(Q.actual_cut_fires_on_falling seed0 seed ev pre HE HW HL0 HL HR),',
        ' (rising_not_falling ev pre HF);reflexivity. Qed.',
        'Lemma source_decision seed0 seed ev pre:',common,normal,
        f' phase_decision {p} {proc} {root} B.root_{root}_expression B.root_{valid}_expression ev pre=',
        f' if Z.eqb(norm 1(read_signal{sampled}{flush}))0%Z then',
        f' if Z.eqb(norm 1(read_signal{sampled}{enable}))0%Z then',
        f' if Z.eqb(norm 1(read_signal pre {valid}))0%Z then Drop else Keep else Accept {source} else Drop.',
        'Proof. intros HJ HE HW HL0 HL HR HF;',
        f' assert(HV:changed_signal ev<>{valid}%nat)by(exact(proj1(Forall_forall _ _)HJ {valid}{member(valid,eventroots)})).',
        f' assert(HRZ:Z.eqb(norm 1(read_signal{sampled}{reset}))0=false)by(now apply Z.eqb_neq).',
        ' unfold phase_decision;rewrite(rising_fires ev pre HE HW HR HF);unfold decide;',
        f' cbn[B.root_{root}_expression B.root_{valid}_expression eval_expr copy_source];rewrite HRZ;',
        f' destruct(Z.eqb(norm 1(read_signal{sampled}{flush}))0%Z);',
        f' destruct(Z.eqb(norm 1(read_signal{sampled}{enable}))0%Z);',
        ' cbn[Z.eqb];rewrite ?norm_idempotent;',
        f' rewrite ?(sampled_root_preserved {p} ev pre {valid}(history_comb_frame _ _ _ _ _ B.root_{valid}_birth_certificate)HV);',
        f' destruct(Z.eqb(norm 1(read_signal pre {valid}))0%Z);reflexivity. Qed.',
        'Lemma source_valid_next seed0 seed ev pre:',common,normal,
        f' norm 1(read_signal{post}{valid})=',
        f' if Z.eqb(norm 1(read_signal{sampled}{flush}))0%Z then',
        f' if Z.eqb(norm 1(read_signal{sampled}{enable}))0%Z then norm 1(read_signal pre {valid})else 1%Z else 0%Z.',
        'Proof. intros HJ HE HW HL0 HL HR HF;',
        f' assert(HV:changed_signal ev<>{valid}%nat)by(exact(proj1(Forall_forall _ _)HJ {valid}{member(valid,eventroots)})).',
        f' rewrite(history_phase_projection {p} {valid} 1 {proc} B.root_{valid}_expression B.root_{valid}_birth_certificate ev pre HV),',
        ' (rising_fires ev pre HE HW HR HF).',
        f' assert(HRZ:Z.eqb(norm 1(read_signal{sampled}{reset}))0=false)by(now apply Z.eqb_neq).',
        f' cbn[B.root_{valid}_expression eval_expr];rewrite HRZ;',
        f' destruct(Z.eqb(norm 1(read_signal{sampled}{flush}))0%Z);',
        f' destruct(Z.eqb(norm 1(read_signal{sampled}{enable}))0%Z);',
        ' rewrite ?norm_idempotent;',
        f' rewrite ?(sampled_root_preserved {p} ev pre {valid}(history_comb_frame _ _ _ _ _ B.root_{valid}_birth_certificate)HV);reflexivity. Qed.',
        'Lemma first_tag_next seed0 seed ev pre g:',common,normal,
        f' J.joint_tag_{target_index}{nextg}=current(J.joint_birth g).',
        'Proof. intros HJ HE HW HL0 HL HR HF;',
        f' change(F.field_{target_index}_origin Token ev pre(J.joint_tag_{target_index} g)(current(J.joint_birth g))=current(J.joint_birth g)).',
        f' unfold F.field_{target_index}_origin,projection_phase_origin;',
        f' rewrite(Q.node_1_clocks seed0 seed ev pre HE HW HL0 HL),(rising_fires ev pre HE HW HR HF).',
        ' pose proof(T.target_reset_active seed ev pre(P.allowed_include_first ev(Q.allowed_include_pipeline ev HE))',
        ' (P.words_include_first pre(Q.words_include_pipeline pre HW))HL HR)as HRA;',
        f' cbn[C.coverage_{coverage}_recipe recipe_origin eval_expr];',
        f' assert(HRZ:Z.eqb(norm 1(read_signal{sampled}{dr}))0=false)by(now apply Z.eqb_neq);now rewrite HRZ. Qed.',
        'Lemma first_valid_next seed0 seed ev pre:',common,normal,
        f' norm 1(read_signal{post}{target_valid})=',
        f' if Z.eqb(norm 1(read_signal{sampled}{enable}))0%Z then 0%Z else norm 1(read_signal pre {valid}).',
        'Proof. intros HJ HE HW HL0 HL HR HF;',
        f' assert(HV:changed_signal ev<>{valid}%nat)by(exact(proj1(Forall_forall _ _)HJ {valid}{member(valid,eventroots)}));',
        f' assert(HT:changed_signal ev<>{target_valid}%nat)by(exact(proj1(Forall_forall _ _)HJ {target_valid}{member(target_valid,eventroots)})).',
        f' rewrite(history_phase_projection {p} {target_valid} 1 {ast["module"]+"."+target["process"]} C.root_{target_valid}_expression C.root_{target_valid}_valid_certificate ev pre HT),',
        ' (Q.node_1_clocks seed0 seed ev pre HE HW HL0 HL),(rising_fires ev pre HE HW HR HF).',
        f' pose proof(bindings_substitute_sound C.coverage_{coverage}_bindings C.root_{target_valid}_expression{sampled}',
        f' (C.coverage_{coverage}_bindings_agree seed _ HL))as HX;rewrite C.coverage_{coverage}_expansion_checked in HX;rewrite <-HX.',
        ' pose proof(T.target_reset_active seed ev pre(P.allowed_include_first ev(Q.allowed_include_pipeline ev HE))',
        ' (P.words_include_first pre(Q.words_include_pipeline pre HW))HL HR)as HRA;',
        f' assert(HRone:norm 1(read_signal{sampled}{dr})=1%Z).',
        f' {{ destruct(one_bit_cases{sampled}{dr})as[HZ|HZ];[contradiction|exact HZ]. }}',
        f' cbn[C.coverage_{coverage}_expanded eval_expr];rewrite HRone;replace(1=?0)%Z with false by reflexivity;',
        f' rewrite !norm_idempotent,(sampled_root_preserved {p} ev pre {valid}(history_comb_frame _ _ _ _ _ B.root_{valid}_birth_certificate)HV).',
        ' rewrite(H.enable_alias _ _ HL);',
        f' destruct(one_bit_cases pre {valid})as[HVZ|HVZ];',
        f' destruct(one_bit_cases{sampled}{h["control"]["gate"]})as[HGZ|HGZ];rewrite HVZ,HGZ;reflexivity. Qed.',
        'Theorem source_window_conserved seed0 seed ev pre g:',common,normal,
        f' Q.slot_tokens{post}{target_valid}(J.joint_tag_{target_index}{nextg})++',
        f' Q.slot_tokens{post}{valid}(current(J.joint_birth{nextg}))=',
        f' Q.slot_tokens pre {valid}(current(J.joint_birth g))++J.pending_admitted ev pre g.',
        'Proof. intros HJ HE HW HL0 HL HR HF;unfold Q.slot_tokens;',
        ' rewrite(first_tag_next seed0 seed ev pre g HJ HE HW HL0 HL HR HF),',
        ' (first_valid_next seed0 seed ev pre HJ HE HW HL0 HL HR HF),',
        ' (source_valid_next seed0 seed ev pre HJ HE HW HL0 HL HR HF).',
        f' change((match current(J.joint_birth g)with None=>[]|Some t=>if Z.eqb(if Z.eqb(norm 1(read_signal{sampled}{enable}))0%Z then 0%Z else norm 1(read_signal pre {valid}))0%Z then[]else[t]end)++',
        f' (match current(B.capture_{bi}_step ev pre(J.joint_birth g))with None=>[]|Some t=>if Z.eqb(if Z.eqb(norm 1(read_signal{sampled}{flush}))0%Z then if Z.eqb(norm 1(read_signal{sampled}{enable}))0%Z then norm 1(read_signal pre {valid})else 1%Z else 0%Z)0%Z then[]else[t]end)=',
        f' (match current(J.joint_birth g)with None=>[]|Some t=>if Z.eqb(norm 1(read_signal pre {valid}))0%Z then[]else[t]end)++J.pending_admitted ev pre g).',
        f' unfold B.capture_{bi}_step,ghost_step,J.pending_admitted,observed_births;',
        ' cbn[current];rewrite(source_decision seed0 seed ev pre HJ HE HW HL0 HL HR HF).',
        f' destruct(one_bit_cases{sampled}{enable})as[HEN|HEN];',
        f' destruct(one_bit_cases{sampled}{flush})as[HFL|HFL];',
        f' destruct(one_bit_cases pre {valid})as[HVL|HVL];rewrite HEN,HFL,HVL;',
        ' cbn[next_tag NewTokens birth];try(now destruct(current(J.joint_birth g)));',
        ' exfalso;pose proof(H.stalled_flush_zero seed _ HL HEN)as Hzero;rewrite HFL in Hzero;discriminate. Qed.']
    suffix=phase.pipeline.discover(ast)['suffix_edges']
    for i,node in enumerate(nodes[2:]):
        src=nodes[i+1]
        lines += [f'Lemma suffix_packet_{i} seed0 seed ev pre g:',common,normal,
            f' Q.slot_tokens{post}{node["valid"]}({tag(node,nextg)})=Q.slot_tokens pre {src["valid"]}({tag(src,"g")}).',
            'Proof. intros HJ HE HW HL0 HL HR HF;unfold Q.slot_tokens;',
            f' rewrite(P.stage_{i}_valid_equation seed0 seed ev pre HJ(Q.allowed_include_pipeline ev HE)(Q.words_include_pipeline pre HW)HL0 HL HR),',
            f' (P.stage_{i}_tag_equation seed0 seed ev pre g(Q.allowed_include_pipeline ev HE)(Q.words_include_pipeline pre HW)HL0 HL HR),',
            ' (rising_fires ev pre HE HW HR HF);reflexivity. Qed.']
    lines+=['Theorem rising_waiting_conserved seed0 seed ev pre g:',common,normal,
        f' Q.waiting_view{post}{nextg}=Q.waiting_view pre g++J.pending_admitted ev pre g.',
        'Proof. intros HJ HE HW HL0 HL HR HF;unfold Q.waiting_view;',
        ' rewrite(rising_pre_low ev pre HF),(rising_post_high ev pre HE HW HF);',
        ' change(Q.retire_view'+post+nextg+'++Q.lower_view'+post+nextg+'=Q.lower_view pre g++J.pending_admitted ev pre g).',
        ' unfold Q.retire_view,Q.lower_view;']
    for i in range(len(suffix)):lines += [f' rewrite(suffix_packet_{i} seed0 seed ev pre g HJ HE HW HL0 HL HR HF).']
    lines += [' repeat rewrite <-app_assoc;',
        ' rewrite(source_window_conserved seed0 seed ev pre g HJ HE HW HL0 HL HR HF);now repeat rewrite <-app_assoc. Qed.',
        'Theorem rising_restores_queue_candidate seed0 seed ev pre g a:J.EventAllowed ev ->Q.ClockAllowed ev ->',
        f' CombLFP {p} seed0 pre ->CombLFP {p} seed{sampled} ->',normal,
        ' Q.QueueCandidate pre g a ->exists next,R.accounted_step ev pre g a 0=Some next /\\',
        f' Q.QueueCandidate{post}{nextg}next /\\A.retired next=A.retired a /\\A.cancelled next=A.cancelled a.',
        'Proof. intros HJ HE HL0 HL HR HF[HP[HA[HW HQ]]].',
        ' pose proof(rising_retires_nothing seed0 seed ev pre g HJ HE HW HL0 HL HR HF)as HC.',
        ' set(kept:=A.waiting a++J.pending_admitted ev pre g).',
        ' assert(HS:CheckedPendingQueue.step token_eq_dec(A.waiting a)(J.pending_admitted ev pre g)[]0=Some(kept,[])).',
        ' { apply CheckedPendingQueueComplete.no_cancel_complete;reflexivity. }',
        ' set(next:=A.Build_Accounts(A.retired a)kept(A.cancelled a)).',
        ' assert(Hstep:R.accounted_step ev pre g a 0=Some next).',
        ' { unfold R.accounted_step;rewrite HC;unfold A.advance;rewrite HS;cbn;now rewrite !app_nil_r. }',
        ' exists next;split;[exact Hstep|]. split.',
        ' - split;[exact(P.pipeline_phase seed ev pre g HJ(Q.allowed_include_pipeline ev HE)HL HP)|].',
        '   split;[exact(R.accounted_phase_candidate seed ev pre g a 0 next HJ HL HA Hstep)|].',
        '   split;[exact(Q.clock_words_phase ev pre HE HW)|].',
        '   change(A.waiting a++J.pending_admitted ev pre g=Q.waiting_view'+post+nextg+');',
        '   rewrite(rising_waiting_conserved seed0 seed ev pre g HJ HE HW HL0 HL HR HF),HQ;reflexivity.',
        ' - split;reflexivity. Qed.']
    quiet=f'norm 1(read_signal{sampled}{reset})<>0%Z ->Q.Rising ev pre=false ->Q.Falling ev pre=false ->'
    clockroots=sorted({v for e in suffix for v in e['roles'].values()}|{q['rf_clock'],q['rf_reset']})
    lines += ['Lemma idle_post_clock ev pre:Q.ClockAllowed ev ->Q.ClockWords pre ->',
        ' Q.Rising ev pre=false ->Q.Falling ev pre=false ->',
        f' norm 1(read_signal{post}{bc})=norm 1(read_signal pre {bc}).',
        'Proof. intros HE HW HRI HFA;rewrite W.clock_phase_norm;',
        ' pose proof(Q.clock_words_sampled ev pre HE HW)as HD;',
        f' destruct(Q.raw_bit_cases pre {bc} HW {member(bc,clockroots)})as[HA|HA];',
        f' destruct(Q.raw_bit_cases{sampled}{bc} HD {member(bc,clockroots)})as[HB|HB];',
        ' rewrite HA,HB;try reflexivity;',
        ' unfold Q.Rising,Q.Falling,edge_fires in *;rewrite HA,HB in *;discriminate. Qed.',
        'Lemma idle_admits_nothing ev pre g:Q.ClockAllowed ev ->Q.ClockWords pre ->',quiet,
        ' J.pending_admitted ev pre g=[].',
        'Proof. intros HE HW HR HRI HFA;unfold J.pending_admitted,observed_births,phase_decision;',
        ' rewrite(Q.source_matches_rising ev pre HE HW HR),HRI;reflexivity. Qed.',
        'Lemma idle_waiting_view seed0 seed ev pre g:',common,quiet,
        f' Q.waiting_view{post}{nextg}=Q.waiting_view pre g.',
        'Proof. intros HJ HE HW HL0 HL HR HRI HFA;',
        f' assert(HF:{hf}=false)by(now rewrite(Q.source_matches_rising ev pre HE HW HR),HRI).',
        ' unfold Q.waiting_view;rewrite(idle_post_clock ev pre HE HW HRI HFA),',
        ' (Q.joint_idle seed0 seed ev pre g HE HW HL0 HL HF);',
        ' unfold Q.retire_view,Q.lower_view,Q.slot_tokens;']
    for i in range(len(nodes)):lines += [f' rewrite(Q.node_{i}_valid_idle seed0 seed ev pre HJ HE HW HL0 HL HF).']
    lines += [' reflexivity. Qed.',
        'Theorem idle_restores_queue_candidate seed0 seed ev pre g a:J.EventAllowed ev ->Q.ClockAllowed ev ->',
        f' CombLFP {p} seed0 pre ->CombLFP {p} seed{sampled} ->',quiet,
        ' Q.QueueCandidate pre g a ->R.accounted_step ev pre g a 0=Some a /\\',
        f' Q.QueueCandidate{post}{nextg}a.',
        'Proof. intros HJ HE HL0 HL HR HRI HFA[HP[HA[HW HQ]]].',
        ' assert(HC:R.retiring_candidate ev pre g=Some[]).',
        ' { unfold R.retiring_candidate;rewrite(Q.actual_cut_fires_on_falling seed0 seed ev pre HE HW HL0 HL HR),HFA;reflexivity. }',
        ' pose proof(idle_admits_nothing ev pre g HE HW HR HRI HFA)as HB.',
        ' assert(HS:CheckedPendingQueue.step token_eq_dec(A.waiting a)(J.pending_admitted ev pre g)[]0=Some(A.waiting a,[])).',
        ' { apply CheckedPendingQueueComplete.no_cancel_complete;now rewrite HB,app_nil_r. }',
        ' assert(Hstep:R.accounted_step ev pre g a 0=Some a).',
        ' { unfold R.accounted_step;rewrite HC;unfold A.advance;rewrite HS;cbn;rewrite !app_nil_r;destruct a;reflexivity. }',
        ' split;[exact Hstep|]. split;[exact(P.pipeline_phase seed ev pre g HJ(Q.allowed_include_pipeline ev HE)HL HP)|].',
        ' split;[exact(R.accounted_phase_candidate seed ev pre g a 0 a HJ HL HA Hstep)|].',
        ' split;[exact(Q.clock_words_phase ev pre HE HW)|].',
        ' rewrite(idle_waiting_view seed0 seed ev pre g HJ HE HW HL0 HL HR HRI HFA);exact HQ. Qed.',
        'Theorem normal_phase_restores_queue_candidate seed0 seed ev pre g a:J.EventAllowed ev ->Q.ClockAllowed ev ->',
        f' CombLFP {p} seed0 pre ->CombLFP {p} seed{sampled} ->',
        f' norm 1(read_signal{sampled}{reset})<>0%Z ->Q.QueueCandidate pre g a ->exists next,',
        f' R.accounted_step ev pre g a 0=Some next /\\Q.QueueCandidate{post}{nextg}next.',
        'Proof. intros HJ HE HL0 HL HR HI;destruct(Q.Rising ev pre)eqn:HRI.',
        ' - destruct(rising_restores_queue_candidate seed0 seed ev pre g a HJ HE HL0 HL HR HRI HI)as[next[HS[HQ HX]]];exists next;now split.',
        ' - destruct(Q.Falling ev pre)eqn:HFA.',
        '   + destruct(W.falling_restores_queue_candidate seed0 seed ev pre g a HJ HE HL0 HL HR HFA HI)as[next[HS[HQ HX]]];exists next;now split.',
        '   + exists a;exact(idle_restores_queue_candidate seed0 seed ev pre g a HJ HE HL0 HL HR HRI HFA HI). Qed.']
    exports=['rising_not_falling','rising_post_high','rising_retires_nothing','source_decision','source_valid_next','first_tag_next','first_valid_next','source_window_conserved']+['suffix_packet_'+str(i)for i in range(len(suffix))]+['rising_waiting_conserved','rising_restores_queue_candidate','idle_post_clock','idle_waiting_view','idle_restores_queue_candidate','normal_phase_restores_queue_candidate']
    lines+=['Print Assumptions '+name+'.'for name in exports]
    return dict(**data,ast_sha256=ast['source_sha256'],coq_load_paths=paths,provider_hash=cr['object_sha256'],audited_exports=len(exports)),'\n'.join(lines)+'\n'


def check(ast_path,ast_module,provider,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module,provider)
    except ValueError as error:
        result=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,global_inv_proved=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result
    path=output/'RisingQueue.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for binding in data['coq_load_paths']:flags+=['-R',binding['directory'],binding['namespace']]
    for folder,namespace in [('capture-birth','GeneratedCaptureBirth'),('coverage','GeneratedRecipeCoverage'),('value','GeneratedConnectedProjections'),('copies','GeneratedMetadataCopies'),('joint','GeneratedCoveredFields'),('joint-history','GeneratedJointHistory'),('stall-flush','GeneratedStallFlush'),('source-hold','GeneratedSourceHold'),('source-transfer','GeneratedSourceTransfer'),('pipeline-transfer','GeneratedPipelineTransfer'),('retirement-cut','GeneratedRetirementCandidate'),('retirement-phase','GeneratedRetirementPhase'),('clock-frame','GeneratedClockFrame')]:
        flags+=['-R',str((Path(provider)/folder).resolve()),namespace]
    flags+=['-R',str(output.resolve()),'GeneratedRisingQueue'];start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    result=dict(accepted=False,native_started=True,scope='normal rising/falling/idle phases restore same raw-generated physical QueueCandidate under explicit LFP conditions; not original CPU/ISA refinement',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),old_inv_read=False,
        old_pending_read=False,old_cpu_proofs_used=False,rising_candidate_restored=False,normal_phase_preservation_proved=False,
        full_cycle_preservation_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout;result['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedRisingQueue.RisingQueue'],output/'coqchk.log',deadline-time.monotonic())
            result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    result['overall_seconds']=time.monotonic()-start
    if result['accepted']:result.update(object_sha256=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest(),rising_candidate_restored=True,normal_phase_preservation_proved=True)
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','provider','output']:parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--ast-module',required=True);args=parser.parse_args()
    result=check(args.ast,args.ast_module,args.provider,args.output);print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
