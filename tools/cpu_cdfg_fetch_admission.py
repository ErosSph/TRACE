"""Prove real IF/ID admission on the SAME valid ADD/PC-advance phase.

Discover guards from original paired word/valid updates. Preserve the full
controller's blocking order; never replace flush/enable by environment inputs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time
import cpu_cdfg_pc_admission as admission
import cpu_cdfg_pc_control as control
import cpu_blocking_observation as obs
from cpu_add_admission_ledger import checked_provider
from cpu_certificate_acceptance import run_stage

pc=admission.pc


def discover(c,raw,profile,graph):
    plan=admission.discover(c,raw,profile,graph)
    reference_plan=pc.admission.discover(c,raw,profile,graph);pair=reference_plan['pair']
    _,residuals,outputs,_,_=pc.scalar.proposal(profile,{pair['carrier'],pair['valid_root']})
    if residuals or len(outputs)!=2:raise ValueError('unsupported actual fetch capture')
    by={r['root']:r for r in outputs};we=by[pair['carrier']]['expression'];ve=by[pair['valid_root']]['expression']
    def guard_choice(e,width):
        if e.name!='ECond'or e.args[0].name!=str(width)or e.args[1].name!='EVar'or e.args[1].args[0].name!='1':
            raise ValueError('unsupported fetch capture guard/width')
        return int(e.args[1].args[1].name),e.args[2],e.args[3]
    reset,wy,wn=guard_choice(we,32);reset_v,vy,vn=guard_choice(ve,1)
    flush,wfy,wfn=guard_choice(wy,32);flush_v,vfy,vfn=guard_choice(vy,1)
    enable,wey,wen=guard_choice(wfn,32);enable_v,vey,ven=guard_choice(vfn,1)
    if (reset,flush,enable)!=(reset_v,flush_v,enable_v):
        raise ValueError('instruction/validity do not share the real priority guards')
    expected=[(vn,'(EConst 1 0)'),(vfy,'(EConst 1 0)'),(vey,'(EConst 1 1)'),
        (ven,f'(EVar 1 {pair["valid_root"]})'),(wey,f'(EVar 32 {pair["word_input"]})'),
        (wen,f'(EVar 32 {pair["carrier"]})')]
    if any(pc.rtl.render(term)!=text for term,text in expected):
        raise ValueError('fetch capture is not the actual copy/hold/drop pattern')
    proc=next(p for p in raw['processes']if p['name']==pair['process'])
    events=re.findall(r'event_edge := (Posedge|Negedge); event_signal := (\d+)',proc['events'])
    if len(events)!=2 or[e for e,_ in events]!=['Posedge','Negedge']or int(events[1][1])!=reset:
        raise ValueError('fetch clock/reset trigger mismatch')
    chains={name:pc.alias_chain(raw,root,1)for name,root in
        [('clock',int(events[0][1])),('reset',reset),('enable',enable),('flush',flush)]}
    for role in ['clock','reset']:
        if chains[role]['terminal']!=plan['timing']['head_'+role]['terminal']:
            raise ValueError('fetch and EX have different actual clock/reset sources')
    if chains['enable']['terminal']!=plan['chains']['enable']['terminal']:
        raise ValueError('fetch enable and PC enable are not actually connected')
    root=chains['flush']['terminal'];writers=[p for p in raw['processes']if root in p['writers']]
    control_report=json.loads((Path(c['pc_control'])/'plan.json').read_text())
    if len(writers)!=1 or writers[0]['name']!=control_report['process']:
        raise ValueError('flush is not produced by the same observed real controller')
    roots={e['root']for chain in chains.values()for e in chain['edges']}
    _,wires,_=pc.comb.proposal(profile,roots)
    if wires['residuals']:raise ValueError('unresolved actual fetch control connection')
    symbols=pc.unique_symbols(graph);queries={}
    for role,chain in chains.items():
        root=chain['source'];query=pc.admission.fetch.cdfg.backward_slice(graph,symbols[root]['path'])
        cone=pc.admission.fetch.cdfg.cone.cone(raw,1,root)
        cuts=pc.agree_open_cone(graph,query,cone)
        queries[role]=dict(query=query,coq_cone=cone,open_cuts=cuts)
    return dict(pc_plan=plan,pair=pair,chains=chains,roots=sorted(roots),queries=queries,
        flush_process=writers[0]['name'],flush_root=chains['flush']['terminal'],opcode=control_report['opcode'],
        ast_sha256=raw['source_sha256'],capacity=reference_plan['capacity'],offset_width=reference_plan['offset_width'])


def render(c,raw,profile,plan):
    p,am=profile['ast']['program'],raw['module'];pair=plan['pair'];old=plan['pc_plan']
    text,_,report=obs.render(c['ast'],c['ast_module'],plan['flush_process'],plan['flush_root'],1)
    _,wires,wsource=pc.comb.proposal(profile,plan['roots'])
    ports={r['output_root']:i for i,r in enumerate(wires['ports'])}
    source=f'Require Import {c["ast_module"]}.\nModule Flush.\n'+text+'\nEnd Flush.\n'
    source+='Module Wires.\n'+wsource+'\nEnd Wires.\n'
    source+=f'''From Coq Require Import List Bool ZArith Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVExpressionBinding Lang.ExtendedSVProjectionConnection
 Lang.ExtendedSVExpressionFold Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPending Lang.ExtendedSVInstructionOrigin
 Lang.ExtendedSVBootstrap Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVStallFlush
 GeneratedPCAdmission.PCAdmission GeneratedPCControl.PCControl GeneratedAdmissionReference.AdmissionReference.
Import ListNotations ExtendedSV ExtendedSVExpressionBinding ExtendedSVProjectionConnection ExtendedSVExpressionFold
 ExtendedSVWordInvariant ExtendedSVScalarHistory ExtendedSVCaptureBirth ExtendedSVCapturedPending ExtendedSVInstructionOrigin
 ExtendedSVBootstrap ExtendedSVBoundedCatalogPhase ExtendedSVDependencyCatalog.
'''
    root=plan['flush_root'];pn=am+'.'+plan['flush_process'];expr='Flush.expr_'+str(report['rules']-1)
    index=[p['name']for p in raw['processes']if p['kind']=='Combinational'].index(plan['flush_process'])
    source+=f'''Definition original_combs:=filter is_comb(processes {p}).
Lemma flush_registered:nth_error original_combs {index}=Some {pn}.
Proof. vm_compute;reflexivity. Qed.
Lemma flush_connected:expression_bindingb original_combs {index} {root} {expr}=true.
Proof. vm_compute;reflexivity. Qed.
Theorem actual_flush_lfp seed fixed:CombLFP {p} seed fixed ->
 norm 1(read_signal fixed {root})=norm 1(eval_expr fixed {expr}).
Proof. exact(checked_expression_binding {p} original_combs {index} {pn} 1 {root} {expr}
 seed fixed eq_refl flush_registered Flush.actual_observation flush_connected). Qed.
Definition flush_specialized:=fold_expression(substitute GeneratedPCControl.PCControl.opcode_binding {expr}).
Lemma flush_specialized_checked:flush_specialized=EConst 1 0.
Proof. vm_compute;reflexivity. Qed.
Theorem actual_opcode51_no_flush seed fixed:CombLFP {p} seed fixed ->
 norm 7(read_signal fixed {plan['opcode']})=51%Z ->norm 1(read_signal fixed {root})=0%Z.
Proof. intros HL HO;rewrite(actual_flush_lfp seed fixed HL).
 assert(HS:eval_expr fixed(substitute GeneratedPCControl.PCControl.opcode_binding {expr})=eval_expr fixed {expr}).
 {{ apply substitute_sound;intros w x rhs HB;unfold GeneratedPCControl.PCControl.opcode_binding in HB.
    destruct(Nat.eqb w 7&&Nat.eqb x {plan['opcode']})eqn:HC;[|discriminate].
    apply andb_true_iff in HC as[HW HX];apply Nat.eqb_eq in HW,HX;subst w x.
    inversion HB;subst rhs;cbn[eval_expr];change(norm 7(read_signal fixed {plan['opcode']})=51%Z);exact HO. }}
 rewrite <-HS,<-(fold_expression_sound(substitute GeneratedPCControl.PCControl.opcode_binding {expr})fixed).
 change(norm 1(eval_expr fixed flush_specialized)=0%Z);rewrite flush_specialized_checked;reflexivity. Qed.
Theorem actual_ADD_no_flush seed fixed code rd rs1 rs2:
 CombLFP {p} seed fixed ->norm 32(read_signal fixed {pair['carrier']})=norm 32 code ->
 Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Add rd rs1 rs2) ->norm 1(read_signal fixed {root})=0%Z.
Proof. intros HL HW HD;apply(actual_opcode51_no_flush seed fixed HL).
 pose proof(GeneratedPCControl.PCControl.Opcode.cone_{plan['opcode']}_actual seed fixed HL)as HO.
 let e:=eval cbv in GeneratedPCControl.PCControl.Opcode.cone_{plan['opcode']} in
 change(norm 7(read_signal fixed {plan['opcode']})=norm 7(eval_expr fixed e))in HO.
 cbn[eval_expr]in HO;rewrite HW in HO;repeat rewrite norm_idempotent in HO.
 exact(eq_trans HO(GeneratedPCControl.PCControl.original_ADD_opcode code rd rs1 rs2 HD)). Qed.
'''
    for name,chain in plan['chains'].items():
        term='eq_refl'
        for edge in reversed(chain['edges']):
            term=f'(eq_trans(eq_trans(Wires.port_{ports[edge["root"]]}_lfp seed fixed HL)(norm_idempotent 1(read_signal fixed {edge["parent"]}))){term})'
        source+=f'''Lemma {name}_wire seed fixed:CombLFP {p} seed fixed ->
 norm 1(read_signal fixed {chain['source']})=norm 1(read_signal fixed {chain['terminal']}).
Proof. intro HL;exact {term}. Qed.
'''
    catalog='GeneratedDependencyCatalog.Catalog.actual_catalog';cert='GeneratedBoundedPhase.Phase.actual_certificate'
    pa='GeneratedPCAdmission.PCAdmission';runtime='GeneratedCapturedHistoryBoot.CapturedHistoryBoot'
    for name in ['clock','reset']:
        x=plan['chains'][name]['source'];y=old['timing']['head_'+name]['source']
        source+=f'''Lemma {name}_catalog:In(1%nat,{x}%nat)(catalog_outputs {catalog}).
Proof. vm_compute;tauto. Qed.
Lemma {name}_raw seed fixed:CombLFP {p} seed fixed ->CatalogShape {p} {catalog} fixed ->
 read_signal fixed {x}=read_signal fixed {y}.
Proof. intros HL[HLength HWords];exact(eq_trans(HWords 1%nat {x}%nat {name}_catalog)
 (eq_trans({name}_wire seed fixed HL)(eq_trans(eq_sym({pa}.head_{name}_normalized seed fixed HL))
 (eq_sym(HWords 1%nat {y}%nat {pa}.head_{name}_catalog))))). Qed.
'''
    fc=plan['chains']['clock']['source'];fr=plan['chains']['reset']['source']
    ec=old['timing']['head_clock']['source'];er=old['timing']['head_reset']['source']
    source+=f'''Local Opaque {p} PhaseSemantics {catalog} {cert}.
Lemma same_fetch_match seed0 seed1 pre sampled:
 CombLFP {p} seed0 pre ->CatalogShape {p} {catalog} pre ->
 CombLFP {p} seed1 sampled ->CatalogShape {p} {catalog} sampled ->
 process_matches_states pre sampled {am}.{pair['process']}=process_matches_states pre sampled {am}.{old['head_process']}.
Proof. intros H0 S0 H1 S1.
 change((edge_fires Posedge(read_signal pre {fc})(read_signal sampled {fc})||
 (edge_fires Negedge(read_signal pre {fr})(read_signal sampled {fr})||false))%bool=
 (edge_fires Posedge(read_signal pre {ec})(read_signal sampled {ec})||
 (edge_fires Negedge(read_signal pre {er})(read_signal sampled {er})||false))%bool).
 rewrite(clock_raw seed0 pre H0 S0),(clock_raw seed1 sampled H1 S1),
 (reset_raw seed0 pre H0 S0),(reset_raw seed1 sampled H1 S1);reflexivity. Qed.
'''
    h=runtime;q='GeneratedAdmissionQueue.AdmissionQueue';r='GeneratedAdmissionReference.AdmissionReference'
    b=q+'.N.B';cap=h+'.C';packed=f'({h}.boot_history image events)'
    pre=f'(phase_run {p} events({h}.F.boot image))';sample=f'(phase_driven_state {p} ev pre)'
    post=f'(PhaseSemantics {p} ev pre)';wp=f'{b}.root_{pair["carrier"]}_expression';vp=f'{b}.root_{pair["valid_root"]}_expression'
    decision=f'(phase_decision {p} {am}.{pair["process"]} {pair["carrier"]} {wp} {vp} ev pre)'
    source+=f'''Lemma normal_capture_decision ev pre:
 process_matches_states pre {sample}{am}.{pair['process']}=true ->
 norm 1(read_signal {sample}{fr})=1%Z ->
 norm 1(read_signal {sample}{plan['chains']['flush']['source']})=0%Z ->
 norm 1(read_signal {sample}{plan['chains']['enable']['source']})=1%Z ->
 {decision}=Accept {pair['word_input']}.
Proof. intros HM HR HF HE;unfold phase_decision;rewrite HM.
 unfold decide,{wp},{vp};cbn[eval_expr copy_source];rewrite HR,HF,HE;reflexivity. Qed.
Theorem actual_valid_ADD_capture image events ev:
 let pre:={pre}in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->
 (forall token,current(fst {packed})=Some token ->exists rd rs1 rs2,
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2)) ->
 process_matches_states pre {sample}{am}.{old['head_process']}=true ->
 norm 1(read_signal {post}{old['valid']})<>0%Z ->{decision}=Accept {pair['word_input']}.
Proof. intros pre HE HEv HClass HM HV.
 destruct({pa}.runtime_shape_lfp events HE({h}.F.boot image)({h}.B.boot_runtime image))as[HShape[seed0 HPre]];fold pre in HShape,HPre.
 pose proof(input_shape {p} {catalog} ev pre(proj1 HEv)HShape)as HDShape.
 pose proof(candidate_shape {p} {catalog} {cert} _ HDShape)as HSampleShape.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 pose proof(GeneratedDerivedSources.DerivedSources.protect ev {old['valid']} HEv ltac:(simpl;tauto))as HP.
 pose proof(GeneratedAdmissionWrite.AdmissionWrite.actual_capture_reset ev pre HP HM HV)as HR.
 assert(HEnable:norm 1(read_signal {sample}{plan['chains']['enable']['terminal']})=1%Z).
 {{ destruct(ExtendedSVStallFlush.one_bit_cases {sample}{plan['chains']['enable']['terminal']})as[HZ|HZ];[|exact HZ].
    exfalso;apply HV;exact(GeneratedValidGate.ValidGate.blocked_actual_capture seed ev pre HL HP HM HZ). }}
 pose proof(GeneratedDerivedSources.DerivedSources.admitted_source_valid seed ev pre HEv HL HM HV)as HSource.
 destruct({h}.boot_and_runtime_related image events HE)as[[[HI HC]HCov]HW].
 destruct HI as[[HCover HValue]HRest];destruct(HCover HSource)as[token HT].
 destruct(HClass token HT)as[rd[rs1[rs2 HD]]].
 pose proof(GeneratedControlCones.ControlCones.sampled_word_{pair['carrier']} image events ev token HE HEv HT)as HWord;fold pre in HWord.
 pose proof(actual_ADD_no_flush seed {sample}(token_word token)rd rs1 rs2 HL HWord HD)as HFlush.
 apply normal_capture_decision.
 - exact(eq_trans(same_fetch_match seed0 seed pre {sample} HPre HShape HL HSampleShape)HM).
 - exact(eq_trans(reset_wire seed _ HL)(eq_trans(eq_sym({pa}.head_reset_normalized seed _ HL))HR)).
 - exact(eq_trans(flush_wire seed _ HL)HFlush).
 - exact(eq_trans(enable_wire seed _ HL)HEnable). Qed.
Theorem actual_admission_singleton image events ev:
 let pre:={pre}in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->
 (forall token,current(fst {packed})=Some token ->exists rd rs1 rs2,
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2)) ->
 process_matches_states pre {sample}{am}.{old['head_process']}=true ->
 norm 1(read_signal {post}{old['valid']})<>0%Z ->
 exists token,{q}.admitted ev pre {packed}=[token] /\\
 token_pc token=Some(norm 32(read_signal pre {old['pc']})).
Proof. intros pre HE HEv HClass HM HV.
 pose proof(actual_valid_ADD_capture image events ev HE HEv HClass HM HV)as HD;fold pre in HD.
 assert(HList:{q}.admitted ev pre {packed}=
 [fresh(serial(fst {packed})){sample}{pair['word_input']} {b}.capture_0_pc]).
 {{ rewrite {r}.admitted_as_births,HD;reflexivity. }}
 exists(fresh(serial(fst {packed})){sample}{pair['word_input']} {b}.capture_0_pc);split;[exact HList|].
 assert(HT:In(fresh(serial(fst {packed})){sample}{pair['word_input']} {b}.capture_0_pc)({q}.admitted ev pre {packed}))by(rewrite HList;now left).
 pose proof({r}.admitted_pc ev pre {packed} _ HT)as HToken.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 exact(eq_trans HToken(f_equal(@Some Z)({r}.sampled_address_at_current_pc seed ev pre HEv HL))). Qed.
Goal True. idtac "FETCH_ADMISSION_AUDIT". exact I. Qed.
'''
    exports=['actual_flush_lfp','flush_specialized_checked','actual_opcode51_no_flush','actual_ADD_no_flush',
        'clock_raw','reset_raw','same_fetch_match','normal_capture_decision','actual_valid_ADD_capture','actual_admission_singleton']
    source+=''.join(f'Print Assumptions {name}.\n'for name in exports)
    return source,len(exports)


def check(c,output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    graph=pc.admission.fetch.cdfg.checked_graph(c['graph'],c['ast'],out/'replayed')
    raw,profile,_=pc.admission.fetch.cdfg.raw_binding(c['ast'],c['ast_module'])
    plan=discover(c,raw,profile,graph);source,count=render(c,raw,profile,plan);file=out/'FetchAdmission.v';file.write_text(source)
    paths=admission.checked(c['pc_admission'],'PCAdmission.v',raw)
    paths+=checked_provider(c['admission_reference'],'AdmissionReference.v',raw['source_sha256'],['actual_admitted_original_ADD_chain_proved'])
    paths += [dict(directory=str(Path(c[key]).resolve()),namespace=ns)for key,ns in
        [('pc_admission','GeneratedPCAdmission'),('admission_reference','GeneratedAdmissionReference')]]
    bindings={}
    for row in paths:
        if row['namespace']in bindings and bindings[row['namespace']]!=row['directory']:raise ValueError('conflicting actual history providers')
        bindings[row['namespace']]=row['directory']
    paths=[dict(namespace=k,directory=v)for k,v in bindings.items()];paths.sort(key=lambda row:len(Path(row['directory']).parts))
    for name,data in [('plan',plan),('providers',paths)]:
        (out/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
    flags=list(pc.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedFetchAdmission']
    start=time.monotonic();cc,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqc.resources').resolve()),
        str(pc.rtl.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=timed,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        ast_sha256=raw['source_sha256'],graph_sha256=hashlib.sha256(Path(c['graph']).read_bytes()).hexdigest(),
        old_inv_read=False,actual_valid_ADD_admission_nonempty_proved=False,caller_flush_enable_or_fetch_match_required=False,
        frontier_relation_restored=False,complete_R_generated=False,itree_refinement_proved=False,external_llm_api_calls=0)
    if cc.returncode==0:
        audit=cc.stdout.split('FETCH_ADMISSION_AUDIT')[-1];closed=audit.count('Closed under the global context')==count and 'Axioms:'not in cc.stdout
        kk,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqchk.resources').resolve()),
            str(pc.rtl.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedFetchAdmission.FetchAdmission'],
            out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        ok=closed and kk.returncode==0;report.update(accepted=ok,coqchk_exit=kk.returncode,coqchk_timed_out=timed,
            assumptions_closed=closed,actual_valid_ADD_admission_nonempty_proved=ok)
    report['seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(file.with_suffix('.vo').read_bytes()).hexdigest()
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ['inputs','output']:parser.add_argument('--'+key,required=True)
    a=parser.parse_args()
    try:r=check(json.loads(Path(a.inputs).read_text()),a.output)
    except Exception as exc:
        out=Path(a.output)
        if out.is_dir()and not(out/'report.json').exists():
            (out/'report.json').write_text(json.dumps(dict(accepted=False,stage='preflight',error=str(exc),cli_exit=1),indent=2)+'\n')
        raise
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
