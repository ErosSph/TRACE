"""Raw RTL write sinks -> untrusted physical retirement-cut candidates.

RF write-enable is NOT an ISA retirement predicate. Candidate cuts use actual
process firing plus terminal metadata validity, and still require ordering,
flush and ISA proofs. No old CPU INV, pending or proof catalog is an input.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_joint_history as joint
from cpu_certificate_acceptance import run_stage

birth=joint.birth;fields=joint.fields;origin=joint.origin;rtl=birth.rtl


def raw_connections(ast):
    c=fields.coverage.discover(ast);v=fields.connected.discover(ast);m=fields.copies.discover(ast)
    result=[]
    for index,row in enumerate(c['covered_fields']):
        matches=[dict(kind=kind,index=i,row=value)for kind,rows in[('connected',v['projections']),('copy',m['copy_edges'])]
            for i,value in enumerate(rows)if all(value[k]==row[k]for k in('root','source','width','recipe','capture'))]
        if len(matches)!=1:raise ValueError('new field value/validity rule not unique')
        result.append(dict(coverage_index=index,coverage=row,provider=matches[0]))
    return result


def alias_route(ast,root,width,terminals):
    seen=set();edges=[]
    while root not in terminals:
        if root in seen:return None
        seen.add(root);writers=[p for p in ast['processes']if p['kind']!='Initial'and root in p['writers']]
        if len(writers)!=1 or writers[0]['kind']!='Combinational':return None
        p=writers[0];body=p['body']
        if body.name!='SAssign'or body.args[0].name!='false':return None
        rhs,lhs=body.args[1:]
        if lhs.name!='LVar'or int(lhs.args[0].name)!=width or rhs.name!='EVar'or int(rhs.args[0].name)!=width:return None
        edges.append(dict(root=root,source=int(rhs.args[1].name),width=width,process=p['name']))
        root=int(rhs.args[1].name)
    return dict(terminal=root,edges=edges)


def zero_reset_branch(body,root):
    writes=[n for n in rtl.walk(body)if n.name=='SAssign'and rtl.root_of(n.args[2])==root]
    return bool(writes)and all(n.args[2].name=='LVar'and n.args[1].name=='EConst'and n.args[1].args[1].name=='0'for n in writes)


def operation_envelopes(body,target,root,ancestors=()):
    if body.name=='SAssign':
        if body!=target:return[]
        return[[dict(positive=positive,expression=rtl.render(guard))for positive,guard,sibling in ancestors
            if zero_reset_branch(sibling,root)]]
    if body.name=='SSeq':
        return [e for child in body.args[0].args for e in operation_envelopes(child,target,root,ancestors)]
    if body.name=='SIf':
        guard,yes,no=body.args
        return(operation_envelopes(yes,target,root,ancestors+((True,guard,no),))+
            operation_envelopes(no,target,root,ancestors+((False,guard,yes),)))
    if body.name=='SCase':
        return[e for arm in body.args[1].args for e in operation_envelopes(arm.args[1],target,root,ancestors)]
    return[]


def discover(ast):
    sites=[]
    for p in ast['processes']:
        if p['kind']!='Sequential':continue
        for path,node in origin.pending.paths(p['body']):
            nba,rhs,lhs=node.args
            if lhs.name!='LSel'or lhs.args[0].name!='32'or lhs.args[1].name!='LVar':continue
            total,storage=map(lambda n:int(n.name),lhs.args[1].args)
            envelopes=operation_envelopes(p['body'],node,storage)
            unique={json.dumps(e,sort_keys=True):e for e in envelopes}
            conditions=next(iter(unique.values()))if len(unique)==1 else None
            has_full_write=any(n.args[2].name=='LVar'and rtl.root_of(n.args[2])==storage
                for n in rtl.walk(p['body'])if n.name=='SAssign')
            pure_nba=all(n.args[0].name=='true'for n in rtl.walk(p['body'])if n.name=='SAssign')
            sites.append(dict(process=p['name'],events=p['events'],source_line=p['line'],nba=nba.name=='true',
                root=storage,total=total,path=json.loads(json.dumps(path)),rhs=rtl.render(rhs),offset=rtl.render(lhs.args[2]),
                operation_conditions=conditions,guard_sampling_supported=pure_nba,
                reset_envelope_supported=conditions is not None and(not has_full_write or bool(conditions))))
    b=birth.discover(ast);residuals=[];slots=[]
    if len(b['captures'])==1:
        try:slots=joint.layout(b['captures'],raw_connections(ast))
        except ValueError as error:residuals.append(str(error))
    else:residuals.append('requires an endogenous birth/metadata schema before a cut can be linked')
    source_roots={int(s['source_tag'].split('joint_tag_')[1].split()[0])for s in slots if s['source_tag'].startswith('joint_tag_')}
    terminals={s['root']:s for s in slots if s['index']not in source_roots and s['width']==5}
    candidates=[];seen=set()
    for site in sites:
        # 32 lanes of 32 bits is structural evidence, not a claim that this is RF.
        if site['total']!=1024 or not site['guard_sampling_supported']or not site['reset_envelope_supported']:continue
        for leaf in rtl.walk(rtl.Parser(site['offset']).complete()):
            if leaf.name!='EVar'or leaf.args[0].name!='5':continue
            leaf_root=int(leaf.args[1].name);route=alias_route(ast,leaf_root,5,terminals)
            if route is None:continue
            slot=terminals[route['terminal']];key=(site['process'],site['root'],slot['root'],leaf_root)
            if key in seen:continue
            seen.add(key);candidates.append(dict(id='cut_'+str(len(candidates)),write=site,slot=slot,
                index_leaf=leaf_root,route=route,cut_kind='actual_operational_process_firing_and_pre_terminal_validity',
                write_enable_is_not_retirement=True,isa_retirement_proved=False))
    if not candidates:residuals.append('no terminal-metadata to packed-write-address route under the supported rules')
    return dict(candidates=candidates,storage_writes=sites,residuals=residuals,old_inv_read=False,old_pending_read=False,
        old_cpu_proofs_used=False,retirement_binding_proved=False,pending_checker_never_fails_proved=False,
        global_inv_proved=False,itree_refinement_proved=False)


def render(ast_path,ast_module,provider,selected=None):
    provider=Path(provider);ast,profile,loadpaths=origin.raw_binding(ast_path,ast_module);data=discover(ast)
    if selected is not None:
        matches=[c for c in data['candidates']if c['id']==selected]
        if len(matches)!=1:raise ValueError('chosen ID has no raw-RTL candidate derivation')
    else:matches=data['candidates']
    if len(matches)!=1:raise ValueError('one supported cut required; ambiguity/absence is not an ISA retirement proof')
    jd,js=joint.render(ast_path,ast_module,provider/'capture-birth',provider/'coverage',provider/'value',provider/'copies',provider/'joint')
    report=fields.verify(provider/'joint-history','JointHistory.v',jd,js)
    candidate=matches[0];slot=candidate['slot'];i=slot['index'];stage=slot['root'];valid=slot['valid']
    program=profile['ast']['program'];proc=ast['module']+'.'+candidate['write']['process'];r=candidate['index_leaf']
    edges=candidate['route']['edges'];roots=[e['root']for e in edges]
    writer_index=next(n for n,p in enumerate(ast['processes'])if ast['module']+'.'+p['name']==proc)
    _,analysis,comb_source=fields.connected.comb.proposal(profile,roots)
    if analysis['residuals']:raise ValueError('actual write-index combinational proof has residuals')
    ports={p['output_root']:n for n,p in enumerate(analysis['ports'])}
    lines=['From Coq Require Import Bool.',
        'Require Import Lang.ExtendedSVCaptureBirth Lang.ExtendedSVOriginLedger Lang.ExtendedSVCapturedPending Lang.ExtendedSVCaptureAccounting',
        ' Lang.ExtendedSVCoveredField Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression Lang.ExtendedSVAutoAdapterEffects Lang.ExtendedSVRootProjection Lang.ExtendedSVWordInvariant',
        ' GeneratedJointHistory.JointHistory.',
        'Import ExtendedSVCaptureBirth ExtendedSVOriginLedger ExtendedSVCapturedPending ExtendedSVCoveredField',
        ' ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVAutoAdapterEffects ExtendedSVRootProjection ExtendedSVWordInvariant.',
        'Module J:=GeneratedJointHistory.JointHistory.',
        'Module A:=ExtendedSVCaptureAccounting.',
        f'Definition write_effect:EffectPlan:={rtl.render(rtl.effect_of(next(p["body"]for p in ast["processes"]if ast["module"]+"."+p["name"]==proc)))}.',
        f'Lemma write_effect_checked:compile_effect(statement_fuel {program})(process_body {proc})=Some write_effect.',
        'Proof. vm_compute. reflexivity. Qed.',
        f'Theorem actual_writer_updates s:process_updates {program} s {proc}=emitted_updates(eval_effect write_effect(initial_exec s)).',
        f'Proof. exact(checked_effect_updates {program} {proc} write_effect write_effect_checked s). Qed.',
        f'Lemma writer_registered:nth_error(processes {program}){writer_index}=Some {proc}.',
        'Proof. vm_compute. reflexivity. Qed.',
        f'Lemma stage_frame:comb_root_unwrittenb {program} {stage}=true.',
        'Proof. vm_compute. reflexivity. Qed.',
        f'Local Opaque {program}.',
        'Definition operation_enabled(s:State):bool:='+operation_bool(candidate['write']['operation_conditions'])+'.',
        'Definition cut_fires ev pre:=',
        f' andb(process_matches_states pre(phase_driven_state {program} ev pre){proc})',
        f' (operation_enabled(phase_driven_state {program} ev pre)).',
        'Theorem cut_selects_actual_process ev pre:cut_fires ev pre=true ->',
        f' In {proc}(selected_on_transition {program} pre(phase_driven_state {program} ev pre)).',
        'Proof. intro H;apply andb_true_iff in H as[HP HO];unfold selected_on_transition;apply filter_In;split;',
        f' [exact(nth_error_In(processes {program}){writer_index} writer_registered)|exact HP]. Qed.',
        'Theorem operation_envelope_exact s:',
        f' operation_enabled s=false <->process_updates {program} s {proc}=',
        f' [resolve_update s(LVar {candidate["write"]["total"]} {candidate["write"]["root"]})0].',
        'Proof. rewrite actual_writer_updates;unfold operation_enabled;',
        ' repeat(cbn[write_effect eval_effect initial_exec fold_left blocking_state pending_nba emitted_updates app];',
        ' match goal with|-context[if ?test then _ else _]=>destruct test end);',
        ' cbn;split;intro H;try discriminate;try reflexivity. Qed.',
        'Definition retiring_candidate ev pre(g:J.JointGhost):option(list Token):=',
        f' if cut_fires ev pre then if Z.eqb(norm 1(read_signal pre {valid}))0 then Some[]',
        f' else match J.joint_tag_{i} g with Some token=>Some[token]|None=>None end else Some[].',
        'Theorem nonoperational_path_cannot_retire ev pre g:',
        f' operation_enabled(phase_driven_state {program} ev pre)=false ->retiring_candidate ev pre g=Some[].',
        'Proof. intro H;unfold retiring_candidate,cut_fires;rewrite H,andb_false_r;reflexivity. Qed.',
        'Theorem candidate_defined ev pre g:J.AuthenticInv pre g ->exists tokens,retiring_candidate ev pre g=Some tokens.',
        'Proof. intros[[HB HM]HR].',
        ' destruct HM as '+joint.nested([f'Value{s["index"]}'for s in jd['slots']])+'.',
        f' destruct Value{i} as[HC HV]. unfold retiring_candidate.',
        f' destruct(cut_fires ev pre);[|exists[];reflexivity]. destruct(Z.eqb(norm 1(read_signal pre {valid}))0)eqn:HE;',
        ' [exists[];reflexivity|]. apply Z.eqb_neq in HE;destruct(HC HE)as[token HT]. rewrite HT;exists[token];reflexivity. Qed.',
        'Theorem candidate_origin_metadata ev pre g token:J.AuthenticInv pre g ->',
        ' retiring_candidate ev pre g=Some[token] ->',
        f' norm 5(read_signal pre {stage})=J.{slot["ref"].replace(" l)"," token)")}.',
        'Proof. intros[[HB HM]HR]HT;',
        ' destruct HM as '+joint.nested([f'Value{s["index"]}'for s in jd['slots']])+'.',
        f' destruct Value{i} as[HC HV]. unfold retiring_candidate in HT.',
        f' destruct(cut_fires ev pre);[|discriminate]. destruct(Z.eqb(norm 1(read_signal pre {valid}))0);[discriminate|].',
        f' destruct(J.joint_tag_{i} g)as[label|]eqn:HG;[|discriminate];inversion HT;subst label;exact(HV token eq_refl). Qed.',
        'Theorem candidate_tokens_recorded ev pre g tokens:J.AuthenticInv pre g ->',
        ' retiring_candidate ev pre g=Some tokens ->Forall(fun token=>In token(history(J.joint_birth g)))tokens.',
        'Proof. intros[HI HR]HT;unfold J.JointRecorded in HR;',
        ' destruct HR as[HC '+joint.nested([f'RecordField{s["index"]}'for s in jd['slots']])+'].',
        ' unfold retiring_candidate in HT;destruct(cut_fires ev pre);[|inversion HT;constructor].',
        f' destruct(Z.eqb(norm 1(read_signal pre {valid}))0);[inversion HT;constructor|].',
        f' destruct(J.joint_tag_{i} g)as[token|]eqn:HG;[|discriminate];inversion HT;subst tokens;',
        f' constructor;[exact(RecordField{i} token eq_refl)|constructor]. Qed.',
        'Theorem actual_write_index_origin seed ev pre g token:',
        f' changed_signal ev<>{stage}%nat ->CombLFP {program} seed(phase_driven_state {program} ev pre) ->',
        ' J.AuthenticInv pre g ->retiring_candidate ev pre g=Some[token] ->',
        f' norm 5(read_signal(phase_driven_state {program} ev pre){r})=J.{slot["ref"].replace(" l)"," token)")}.',
        'Proof. intros HE HL HI HT.']
    for edge in edges:
        n=ports[edge['root']]
        lines += [f' rewrite(port_{n}_lfp _ _ HL). cbn[port_{n}_rhs eval_expr];rewrite norm_idempotent.']
    lines += [f' rewrite(sampled_root_preserved {program} ev pre {stage} stage_frame HE).',
        ' exact(candidate_origin_metadata ev pre g token HI HT). Qed.',
        'Definition automatic_queue_step ev pre g queue cancel:=match retiring_candidate ev pre g with',
        '| None=>None|Some tokens=>J.pending_step ev pre g queue tokens cancel end.',
        'Theorem automatic_queue_partition ev pre g queue cancel kept killed:',
        ' automatic_queue_step ev pre g queue cancel=Some(kept,killed) ->',
        ' exists tokens,retiring_candidate ev pre g=Some tokens /\\',
        ' queue++J.pending_admitted ev pre g=tokens++(kept++killed).',
        'Proof. unfold automatic_queue_step;destruct(retiring_candidate ev pre g)as[tokens|]eqn:HC;[|discriminate].',
        ' intro HS;exists tokens;split;[reflexivity|exact(J.pending_queue_partition ev pre g queue tokens cancel kept killed HS)]. Qed.',
        'Theorem automatic_queue_phase_candidate seed ev pre g queue cancel kept killed:J.EventAllowed ev ->',
        f' CombLFP {program} seed(phase_driven_state {program} ev pre) ->J.PendingInv pre g queue ->',
        ' automatic_queue_step ev pre g queue cancel=Some(kept,killed) ->',
        f' J.PendingInv(PhaseSemantics {program} ev pre)(J.joint_step ev pre g)kept.',
        'Proof. intros HE HL HI;unfold automatic_queue_step;',
        ' destruct(retiring_candidate ev pre g)as[tokens|]eqn:HC;[|discriminate].',
        ' intro HS;exact(J.pending_phase_candidate seed ev pre g queue tokens cancel kept killed HE HL HI HS). Qed.']
    base=birth.discover(ast)['captures'][0]
    birth_args=f'{program} {ast["module"]}.{base["process"]} {base["carrier"]} J.B.root_{base["carrier"]}_expression J.B.root_{base["valid_root"]}_expression J.B.capture_0_pc'
    lines += ['Definition AccountedInv pre g a:=J.AuthenticInv pre g /\\A.AccountsFor(history(J.joint_birth g))a.',
        'Definition accounted_step ev pre g a cancel:=match retiring_candidate ev pre g with',
        '| None=>None|Some tokens=>A.advance a(J.pending_admitted ev pre g)tokens cancel end.',
        'Theorem accounted_initialization:',
        f' AccountedInv(initialize {program} [])J.joint_empty A.empty.',
        'Proof. split;[exact J.joint_authentic_initialize|exact A.empty_accounts]. Qed.',
        'Theorem accounted_phase_candidate seed ev pre g a cancel next:J.EventAllowed ev ->',
        f' CombLFP {program} seed(phase_driven_state {program} ev pre) ->AccountedInv pre g a ->',
        ' accounted_step ev pre g a cancel=Some next ->',
        f' AccountedInv(PhaseSemantics {program} ev pre)(J.joint_step ev pre g)next.',
        'Proof. intros HE HL[HI HA];unfold accounted_step;destruct(retiring_candidate ev pre g)as[tokens|]eqn:HC;[|discriminate].',
        ' intro HS;split;[exact(J.joint_authentic_phase seed ev pre g HE HL HI)|].',
        f' exact(A.actual_birth_accounting {birth_args} ev pre(J.joint_birth g)a tokens cancel next HA HS). Qed.',
        'Theorem accounted_capture_coverage pre g a token:AccountedInv pre g a ->In token(history(J.joint_birth g)) ->',
        ' In token(A.retired a) \\/In token(A.waiting a) \\/In token(A.cancelled a).',
        'Proof. intros[HI HA]HT;exact(A.accounts_cover_capture _ a token HA HT). Qed.',
        'Theorem accounted_unfinished_is_pending pre g a token:AccountedInv pre g a ->',
        ' In token(history(J.joint_birth g)) ->~In token(A.retired a) ->~In token(A.cancelled a) ->In token(A.waiting a).',
        'Proof. intros[HI HA]HT HR HC;exact(A.uncompleted_capture_is_waiting _ a token HA HT HR HC). Qed.',
        'Theorem accounted_refines_weak_pending pre g a:AccountedInv pre g a ->J.PendingInv pre g(A.waiting a).',
        'Proof. intros[HI HA];split;[exact HI|]. destruct HI as[[HB HM]HR];destruct HB as[HV[HT[HH HN]]].',
        ' exact(A.accounted_pending _ a HA HN). Qed.']
    exports=['actual_writer_updates','cut_selects_actual_process','operation_envelope_exact',
        'nonoperational_path_cannot_retire','candidate_defined','candidate_origin_metadata','candidate_tokens_recorded',
        'actual_write_index_origin','automatic_queue_partition','automatic_queue_phase_candidate',
        'accounted_initialization','accounted_phase_candidate','accounted_capture_coverage',
        'accounted_unfinished_is_pending','accounted_refines_weak_pending']
    for name in exports:lines.append('Print Assumptions '+name+'.')
    return dict(**data,selected_candidate=candidate['id'],ast_sha256=ast['source_sha256'],coq_load_paths=loadpaths,provider_hash=report['object_sha256'],
        audited_exports=len(analysis['ports'])+len(exports)),comb_source+'\n'+'\n'.join(lines)+'\n'


def operation_bool(conditions):
    expr='true'
    for condition in reversed(conditions):
        test=f'(Z.eqb(eval_expr s {condition["expression"]})0)'
        if condition['positive']:test='(negb'+test+')'
        expr=f'andb {test}({expr})'
    return expr


def check(ast_path,ast_module,provider,output,timeout=1200,selected=None):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module,provider,selected)
    except ValueError as error:
        result=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,global_inv_proved=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result
    path=output/'RetirementCandidate.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    provider=Path(provider)
    for part,namespace in[('capture-birth','GeneratedCaptureBirth'),('coverage','GeneratedRecipeCoverage'),
        ('value','GeneratedConnectedProjections'),('copies','GeneratedMetadataCopies'),('joint','GeneratedCoveredFields'),
        ('joint-history','GeneratedJointHistory')]:flags+=['-R',str((provider/part).resolve()),namespace]
    flags+=['-R',str(output.resolve()),'GeneratedRetirementCandidate'];start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    result=dict(accepted=False,native_started=True,scope='physical retirement-cut candidate and actual write-index provenance, not ISA commit binding',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        ast_sha256=data['ast_sha256'],selected_candidate=data['selected_candidate'],
        old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,manual_retiring_list_input=False,
        retirement_binding_proved=False,pending_checker_never_fails_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout
        result['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedRetirementCandidate.RetirementCandidate'],
                output/'coqchk.log',deadline-time.monotonic())
            result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    result['overall_seconds']=time.monotonic()-start
    if result['accepted']:result['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in['ast','provider','output']:p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--ast-module',required=True);a=p.parse_args()
    result=check(a.ast,a.ast_module,a.provider,a.output);print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
