"""Bind reset-derived ADD write/memory/destination fields to real forwarders.

Reuse the checked original writeback-selector history for mem2reg; do not
confuse it with an ALU input selector or build another CPU behavior model.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_add_write_history as history
from cpu_add_control_certificate import verified
from cpu_certificate_acceptance import run_stage
rtl=history.rtl


def discover(raw, writes, selection):
    physical,_=history.admission.ready.discover(raw)
    result=[]
    for stage,key in enumerate(['first','second']):
        routes={}
        for role in ['write','load','rd']:
            roots={r['row']['binding'][key][role]for r in physical['rows']}
            if len(roots)!=1:raise ValueError('ambiguous actual producer '+role)
            route=history.admission.wires.trace(raw,5 if role=='rd'else 1,next(iter(roots)))
            if route['kind']!='sequential':raise ValueError('producer field not sequential')
            routes[role]=route
        row=writes['rows'][stage]
        sel=selection['rows'][stage]
        if row['root']!=routes['write']['terminal']or sel['root']!=routes['load']['terminal']:
            raise ValueError('actual forwarder is not the checked write/memory-selection field')
        if any(r['process']!=row['process']for r in routes.values())or sel['recipe']!=row['recipe']:
            raise ValueError('control/destination/token capture identity mismatch')
        result.append(dict(stage=stage,valid=row['valid'],routes=routes,write=row,selection=sel))
    return dict(rows=result,ast_sha256=raw['source_sha256'])


def render(c,raw,profile,plan):
    p=profile['ast']['program'];sample=f'(phase_driven_state {p} ev pre)'
    roots={e['root']for row in plan['rows']for r in row['routes'].values()for e in r['edges']}
    _,wp,ws=history.admission.comb.proposal(profile,roots)
    if wp['residuals']:raise ValueError('unproved actual forwarding aliases')
    ports={r['output_root']:i for i,r in enumerate(wp['ports'])}
    source='Module ProducerWires.\n'+ws+'\nEnd ProducerWires.\n'
    source+=f'''From Coq Require Import List ZArith Bool.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression Lang.ExtendedSVWordInvariant Lang.ExtendedSVRootProjection
 Lang.ExtendedSVCaptureBirth Lang.ExtendedSVWriteValidity Ex.External.CPUInstructionFields
 Ex.External.CPUISAAddOperandFields Ex.External.CPUTwoStageReadySelection
 GeneratedAddWriteHistory.AddWriteHistory GeneratedWritebackSelector.WritebackSelector
 GeneratedCapturedReads.CapturedReadAddresses GeneratedCoveredDestination.CoveredDestination
 GeneratedReadySelector.ReadySelector.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVWordInvariant ExtendedSVRootProjection ExtendedSVCaptureBirth
 ExtendedSVWriteValidity CPUInstructionFields CPUISAAddOperandFields CPUTwoStageReadySelection.
Module Writes:=GeneratedAddWriteHistory.AddWriteHistory.
Module Selection:=GeneratedWritebackSelector.WritebackSelector.
Module Runtime:=Writes.Runtime. Module Covered:=Runtime.C.
Local Opaque {p} PhaseSemantics.
'''
    protected=sorted({r[k]for row in plan['rows']for r in row['routes'].values()for k in ['terminal']}|{r['valid']for r in plan['rows']})
    source+='Lemma protect ev root:Runtime.W.Environment ev ->In root ['+';'.join(str(x)+'%nat'for x in protected)+'] ->changed_signal ev<>root.\n'
    source+='''Proof. intros[_ HE]HI;unfold Runtime.W.ExternalEvent in HE;apply existsb_exists in HE;
 destruct HE as[x[HX HE]];apply Nat.eqb_eq in HE;rewrite HE;unfold Runtime.W.external_roots in HX;
 cbn in HX,HI;repeat destruct HX as[<-|HX];try contradiction;
 repeat destruct HI as[<-|HI];try contradiction;discriminate. Qed.
'''
    for root in protected:
        source+=f'''Lemma frame_{root}:comb_root_unwrittenb {p} {root}=true.
Proof. vm_compute;reflexivity. Qed.
'''
    exports=[]
    for row in plan['rows']:
        stage,vr=row['stage'],row['valid'];wr,ld,rd=[row['routes'][x]['terminal']for x in ['write','load','rd']]
        source+=f'''Theorem actual_add_producer_fields_{stage} image events token dest rs1 rs2:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->norm 1(read_signal pre {vr})<>0%Z ->
 Covered.C.chain_tag{stage}(snd(Runtime.boot_history image events))=Some token ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add dest rs1 rs2) ->
 norm 1(read_signal pre {wr})=1%Z /\\norm 1(read_signal pre {ld})=0%Z /\\norm 5(read_signal pre {rd})=dest.
Proof. intros pre HE HV HT HD.
 pose proof(Writes.reset_reachable_add_write_controls image events HE)as[HC[H0[H1 H2]]].
 assert(HS:Writes.is_add token=true)by(unfold Writes.is_add;rewrite HD;reflexivity).
 split.
 - pose proof(H{stage} token HT HS HV)as HW;unfold Writes.write_reference in HW;injection HW as HW;exact(eq_sym HW).
 - split.
   + pose proof(Selection.boot image events HE)as[HH[HM HW]].
'''
        field = '(proj2 HH)' if stage==0 else 'HM'
        head=plan['rows'][0]['routes']['load']['terminal']
        source+=f'''     pose proof({field} token HT)as HL;unfold Selection.Head.reference_{head} in HL;
     rewrite(Selection.head_add_zero _ dest rs1 rs2 HD)in HL;injection HL as HL;exact(eq_sym HL).
   + destruct(Covered.valid_field_{stage}_has_value pre(Runtime.boot_history image events)HC HV)as[t[HT' HVrd]].
     assert(t=token)by congruence;subst t.
     destruct(original_decode_add_registers _ _ _ _ HD)as[HRD _].
     exact(eq_trans HVrd(eq_trans(GeneratedCoveredDestination.CoveredDestination.captured_head_rd(token_word token))HRD)). Qed.
'''
        exports.append(f'actual_add_producer_fields_{stage}')
        for role,route in row['routes'].items():
            w=5 if role=='rd'else 1;root=route['input'];leaf=route['terminal']
            source+=f'''Lemma sampled_{stage}_{role} image events ev:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->
 norm {w}(read_signal {sample}{root})=norm {w}(read_signal pre {leaf}).
Proof. intros pre HE HEv;destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
'''
            for edge in route['edges']:
                k=ports[edge['root']]
                source+=f'rewrite(ProducerWires.port_{k}_lfp seed _ HL);unfold ProducerWires.port_{k}_rhs;cbn[eval_expr];rewrite norm_idempotent.\n'
            source+=f'exact(f_equal(norm {w})(sampled_root_preserved {p} ev pre {leaf} frame_{leaf}(protect ev {leaf} HEv ltac:(simpl;tauto)))). Qed.\n'
        inputs={k:r['input']for k,r in row['routes'].items()}
        source+=f'''Theorem sampled_token_destination_{stage} image events ev token:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->norm 1(read_signal pre {vr})<>0%Z ->
 Covered.C.chain_tag{stage}(snd(Runtime.boot_history image events))=Some token ->
 norm 5(read_signal {sample}{inputs['rd']})=field_reference(token_word token)Rd.
Proof. intros pre HE HEv HV HT.
 pose proof(Writes.reset_reachable_add_write_controls image events HE)as[HC _].
 destruct(Covered.valid_field_{stage}_has_value pre(Runtime.boot_history image events)HC HV)as[t[HT' HR]].
 assert(t=token)by congruence;subst t.
 exact(eq_trans(sampled_{stage}_rd image events ev HE HEv)
  (eq_trans HR(GeneratedCoveredDestination.CoveredDestination.captured_head_rd(token_word token)))). Qed.
'''
        source+=f'''Theorem actual_add_sampled_controls_{stage} image events ev token dest rs1 rs2:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->norm 1(read_signal pre {vr})<>0%Z ->
 Covered.C.chain_tag{stage}(snd(Runtime.boot_history image events))=Some token ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add dest rs1 rs2) ->
 GeneratedReadySelector.ReadySelector.bit {sample}{inputs['write']}=true /\\
 GeneratedReadySelector.ReadySelector.bit {sample}{inputs['load']}=false /\\
 norm 5(read_signal {sample}{inputs['rd']})=dest.
Proof. intros pre HE HEv HV HT HD.
 destruct(actual_add_producer_fields_{stage} image events token dest rs1 rs2 HE HV HT HD)as[HW[HL HR]].
 exact(conj(f_equal(fun value=>Z.eqb value 1%Z)(eq_trans(sampled_{stage}_write image events ev HE HEv)HW))
 (conj(f_equal(fun value=>Z.eqb value 1%Z)(eq_trans(sampled_{stage}_load image events ev HE HEv)HL))
 (eq_trans(sampled_{stage}_rd image events ev HE HEv)HR))). Qed.
Theorem invalid_sampled_slot_{stage} image events ev ready value:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->norm 1(read_signal pre {vr})=0%Z ->
 slot(GeneratedReadySelector.ReadySelector.bit {sample}{inputs['write']})
 (norm 5(read_signal {sample}{inputs['rd']}))ready value=None.
Proof. intros pre HE HEv HV.
 pose proof(sampled_{stage}_write image events ev HE HEv)as HSampleWrite;fold pre in HSampleWrite.
 pose proof(sampled_{stage}_rd image events ev HE HEv)as HSampleRd;fold pre in HSampleRd.
 assert(HNoWrite:(Z.eqb(norm 1(read_signal pre {wr}))1%Z &&
  negb(Z.eqb(norm 5(read_signal pre {rd}))0%Z))%bool=false).
 {{ destruct(Z.eqb(norm 1(read_signal pre {wr}))1%Z &&
    negb(Z.eqb(norm 5(read_signal pre {rd}))0%Z))%bool eqn:HG;[|reflexivity].
    apply Bool.andb_true_iff in HG as[HW HR];apply Z.eqb_eq in HW.
    apply Bool.negb_true_iff in HR;apply Z.eqb_neq in HR.
    pose proof(proj2(proj2(Runtime.boot_and_runtime_related image events HE)))as HP.
    assert(HNZ:norm 1(read_signal pre {wr})<>0%Z)by(congruence).
    pose proof({'(proj1 HP)'if stage==0 else'(proj1(proj2 HP))'} HNZ HR)as HValid.
    exfalso;apply HValid;exact HV. }}
 unfold slot,GeneratedReadySelector.ReadySelector.bit;rewrite HSampleWrite,HSampleRd.
 change((if(Z.eqb(norm 1(read_signal pre {wr}))1%Z &&negb(Z.eqb(norm 5(read_signal pre {rd}))0%Z))%bool
 then Some(norm 5(read_signal pre {rd}),if ready then Some value else None)else None)=None).
 rewrite HNoWrite;reflexivity.
Qed.
'''
        exports += [f'sampled_token_destination_{stage}',f'actual_add_sampled_controls_{stage}',f'invalid_sampled_slot_{stage}']
    source+='Goal True. idtac "READY_CONTROL_AUDIT". exact I. Qed.\n'+''.join(f'Print Assumptions {n}.\n'for n in exports)
    return source


def check(c,context,output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    raw,profile,_=history.admission.observation.origin.raw_binding(c['ast'],c['ast_module'])
    wp=history.admission.checked(c['write_history'],'AddWriteHistory',raw['source_sha256'])
    paths=json.loads((Path(context)/'providers.json').read_text())
    selector=next(r['directory']for r in paths if r['namespace']=='GeneratedWritebackSelector')
    sp=history.admission.checked(selector,'WritebackSelector',raw['source_sha256'])
    plan=discover(raw,wp,sp)
    graph=history.admission.checked_graph(c['graph'],c['ast'],out/'replayed')
    evidence=history.companions.capture_graph_evidence(graph,raw,[r['selection']for r in plan['rows']])
    (out/'graph-evidence.json').write_text(json.dumps(evidence,indent=2)+'\n')
    source=render(c,raw,profile,plan);file=out/'ReadyControls.v';file.write_text(source)
    (out/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    paths+=json.loads((Path(c['write_history'])/'providers.json').read_text())
    paths.append(dict(directory=str(Path(c['write_history']).resolve()),namespace='GeneratedAddWriteHistory'))
    paths=list({(r['namespace'],r['directory']):r for r in paths}.values())
    history.admission.verify_environment_paths(paths)
    (out/'providers.json').write_text(json.dumps(paths,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedReadyControls'];start=time.monotonic()
    cc,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqc.resources').resolve()),
        str(history.admission.observation.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=timed,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        ast_sha256=raw['source_sha256'],old_inv_read=False,complete_R_generated=False,
        actual_ready_producer_controls_proved=False,external_llm_api_calls=0)
    if cc.returncode==0:
        tail=cc.stdout.split('READY_CONTROL_AUDIT')[-1];closed=tail.count('Closed under the global context')==8 and 'Axioms:'not in tail
        kk,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqchk.resources').resolve()),
            str(history.admission.observation.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedReadyControls.ReadyControls'],out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        report.update(coqchk_exit=kk.returncode,coqchk_timed_out=timed,assumptions_closed=closed,
            accepted=closed and kk.returncode==0,actual_ready_producer_controls_proved=closed and kk.returncode==0)
    report['seconds']=time.monotonic()-start;(out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for x in ['inputs','context','output']:p.add_argument('--'+x,required=True)
    a=p.parse_args()
    try:r=check(json.loads(Path(a.inputs).read_text()),a.context,a.output)
    except Exception as e:
        out=Path(a.output)
        if out.is_dir()and not(out/'report.json').exists():
            (out/'report.json').write_text(json.dumps(dict(accepted=False,stage='preflight',error=str(e),cli_exit=1),indent=2)+'\n')
        raise
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
