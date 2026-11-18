"""Recover the real invalid IF/ID payload from paired AST updates and reset.

The certificate preserves both guards and their order; a graph query alone is
never treated as proof. Runtime starts after the actual resetting clock edge,
not from a silently changed seed. The result is consumed by prefill controls.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_cdfg_fetch_admission as fetch
from cpu_add_admission_ledger import checked_provider
from cpu_certificate_acceptance import run_stage


def pair_rule(rtl,word,valid,width,root,validroot,bubble):
    """A proposal tree for the checked Pair relation, not a trusted evaluator."""
    if word.name=='ECond'and valid.name=='ECond':
        if (word.args[0].name!=str(width)or valid.args[0].name!='1'
                or rtl.render(word.args[1])!=rtl.render(valid.args[1])):
            raise ValueError('invalid-payload pair has different guards or widths')
        y=pair_rule(rtl,word.args[2],valid.args[2],width,root,validroot,bubble)
        n=pair_rule(rtl,word.args[3],valid.args[3],width,root,validroot,bubble)
        return dict(kind='select',guard=rtl.render(word.args[1]),yes=y,no=n)
    if rtl.render(valid)=='(EConst 1 0)':
        if (word.name!='EConst'or word.args[0].name!=str(width)
                or (int(word.args[1].name)&((1<<width)-1))!=(bubble&((1<<width)-1))):
            raise ValueError('invalid branch does not write the same bubble payload')
        return dict(kind='drop',literal=int(word.args[1].name))
    if rtl.render(valid)=='(EConst 1 1)':return dict(kind='fresh')
    if (rtl.render(word)==f'(EVar {width} {root})'and rtl.render(valid)==f'(EVar 1 {validroot})'):
        return dict(kind='hold')
    raise ValueError('unmatched paired invalid-payload update')


def pair_proof(rule):
    if rule['kind']=='select':return 'apply PairSelect.\n{ '+pair_proof(rule['yes'])+' }\n{ '+pair_proof(rule['no'])+' }'
    if rule['kind']=='drop':return 'apply PairDrop;vm_compute;reflexivity.'
    if rule['kind']=='fresh':return 'apply PairFresh.'
    if rule['kind']=='hold':return 'apply PairHold.'
    raise ValueError('unknown checked pair rule')


def discover(c,raw,profile,graph):
    plan=fetch.discover(c,raw,profile,graph);pair=plan['pair'];pc=fetch.pc
    _,residuals,outputs,_,_=pc.scalar.proposal(profile,{pair['carrier'],pair['valid_root']})
    by={r['root']:r['expression']for r in outputs}
    word,valid=by[pair['carrier']],by[pair['valid_root']]
    if residuals or word.name!='ECond'or word.args[3].name!='EConst':
        raise ValueError('invalid-payload reset is not a constant-clear pair')
    bubble=int(word.args[3].args[1].name)
    rule=pair_rule(pc.rtl,word,valid,32,pair['carrier'],pair['valid_root'],bubble)
    symbols=pc.unique_symbols(graph);queries={}
    for root in [pair['carrier'],pair['valid_root']]:
        query=pc.admission.fetch.cdfg.backward_slice(graph,symbols[root]['path'])
        if query['boundaries'].get(symbols[root]['path'])!='sequential':
            raise ValueError('paired payload/valid field has wrong clock boundary')
        if symbols[root]['width']!=(32 if root==pair['carrier']else 1):
            raise ValueError('paired CDFG field has wrong width')
        queries[str(root)]=query
    plan.update(bubble=bubble,pair_rule=rule,payload_query=queries,
        word_expression=pc.rtl.render(word),valid_expression=pc.rtl.render(valid))
    return plan


def render(c,raw,profile,plan,shallow_boot=False):
    p,am=profile['ast']['program'],raw['module'];pair=plan['pair'];root=pair['carrier'];valid=pair['valid_root']
    proc=am+'.'+pair['process'];b='GeneratedAdmissionQueue.AdmissionQueue.N.B'
    h='GeneratedCapturedHistoryBoot.CapturedHistoryBoot';f=h+'.F';a='GeneratedFetchAdmission.FetchAdmission'
    cat='GeneratedDependencyCatalog.Catalog.actual_catalog';cert='GeneratedBoundedPhase.Phase.actual_certificate'
    bc=f'{b}.root_{root}_birth_certificate';vc=f'{b}.root_{valid}_birth_certificate'
    word=f'{b}.root_{root}_expression';ve=f'{b}.root_{valid}_expression'
    clock=plan['chains']['clock']['source'];reset=plan['chains']['reset']['source']
    extclock=plan['chains']['clock']['terminal'];extreset=plan['chains']['reset']['terminal']
    sample=f'(phase_driven_state {p} ev pre)'
    source=f'''From Coq Require Import List ZArith Bool Lia.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVScalarExpression Lang.ExtendedSVInvalidPayload Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVConstantRoot
 Lang.ExtendedSVBootstrap Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVBoundedCatalogPhase
 GeneratedFetchAdmission.FetchAdmission GeneratedAdmissionQueue.AdmissionQueue.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory ExtendedSVScalarExpression
 ExtendedSVInvalidPayload ExtendedSVEmptyPipeline ExtendedSVConstantRoot ExtendedSVBootstrap ExtendedSVDependencyCatalog ExtendedSVBoundedCatalogPhase.
Local Opaque {p} PhaseSemantics {cat} {cert}.
Definition InvalidWord:=Related 32 {root}%nat {valid}%nat {plan['bubble']}%Z.
Lemma actual_pair:Pair 32 {root}%nat {valid}%nat {plan['bubble']}%Z {word} {ve}.
Proof. unfold {word},{ve}.
{pair_proof(plan['pair_rule'])}
Qed.
Lemma protects ev:{h}.W.Environment ev ->changed_signal ev<>{root}%nat /\\changed_signal ev<>{valid}%nat.
Proof. intro HE;split;apply(GeneratedAdmissionQueue.AdmissionQueue.internal_event ev _ HE);lia. Qed.
Theorem actual_invalid_word_phase ev pre:
 {h}.W.Environment ev ->InvalidWord pre ->InvalidWord(PhaseSemantics {p} ev pre).
Proof. intros HE HI;destruct(protects ev HE)as[HW HV].
 exact(actual_phase {p} 32 {root}%nat {valid}%nat {plan['bubble']}%Z {proc} {word} {ve} {bc} {vc} actual_pair ev pre HW HV HI). Qed.
Lemma input_clock_unwritten:roots_unwrittenb {extclock}%nat(processes {p})=true.
Proof. vm_compute;reflexivity. Qed.
Lemma input_reset_unwritten:roots_unwrittenb {extreset}%nat(processes {p})=true.
Proof. vm_compute;reflexivity. Qed.
Lemma seed_clock image:read_signal({f}.seed image){extclock}%nat=0%Z.
Proof. unfold {f}.seed,{f}.writes,ExtendedSVBootstrap.seed_writes;cbn[fold_left fst snd].
 rewrite read_signal_write_other by discriminate.
 rewrite read_signal_write_other by discriminate.
 apply read_zero_seed. Qed.
Definition reset_prefix image:=PhaseSemantics {p} {f}.reset_assert({f}.seed image).
Lemma reset_prefix_inputs image:read_signal(reset_prefix image){extclock}%nat=0%Z /\\read_signal(reset_prefix image){extreset}%nat=0%Z.
Proof. split;unfold reset_prefix;rewrite phase_input by(exact input_clock_unwritten||exact input_reset_unwritten).
 - change(read_signal(write_signal({f}.seed image){extreset}%nat 0%Z){extclock}%nat=0%Z).
   rewrite read_signal_write_other by discriminate;apply seed_clock.
 - apply read_signal_write_same. Qed.
Theorem actual_boot_reset_payload image:
 let pre:=reset_prefix image in
 norm 32(read_signal(PhaseSemantics {p} {f}.rise pre){root}%nat)=norm 32 {plan['bubble']}%Z /\\
 norm 1(read_signal(PhaseSemantics {p} {f}.rise pre){valid}%nat)=0%Z.
Proof. intro pre.
 assert(HE0:CatalogEvent {p} {cat} {f}.reset_assert).
 {{ exact(ExtendedSVBootstrap.checked_input_root {p} {cat} {extreset}%nat 1%Z 0%Z {h}.B.root_1_safe). }}
 assert(HE1:CatalogEvent {p} {cat} {f}.rise).
 {{ exact(ExtendedSVBootstrap.checked_input_root {p} {cat} {extclock}%nat 0%Z 1%Z {h}.B.root_0_safe). }}
 destruct(catalog_phase_evidence {p} {cat} {cert} {f}.reset_assert({f}.seed image)HE0({h}.B.seed_shape image))
 as[HL0[[seed0 HLPre]HShape]];fold pre in HLPre,HShape.
 destruct(catalog_phase_evidence {p} {cat} {cert} {f}.rise pre HE1 HShape)as[HLSample HUnused].
 pose proof(candidate_shape {p} {cat} {cert} _ (input_shape {p} {cat} {f}.rise pre HE1 HShape))as HSampleShape.
 destruct(reset_prefix_inputs image)as[HClock HReset];fold pre in HClock,HReset.
 assert(HOldClock:read_signal pre {clock}%nat=0%Z).
 {{ exact(eq_trans(proj2 HShape 1%nat {clock}%nat {a}.clock_catalog)
   (eq_trans({a}.clock_wire seed0 pre HLPre)(f_equal(norm 1)HClock))). }}
 assert(HNewClock:read_signal(phase_driven_state {p} {f}.rise pre){clock}%nat=1%Z).
 {{ assert(HInput:norm 1(read_signal(phase_driven_state {p} {f}.rise pre){extclock}%nat)=1%Z).
   {{ rewrite(sampled_input {p} {extclock}%nat {f}.rise pre input_clock_unwritten).
      change(norm 1(read_signal(write_signal pre {extclock}%nat 1%Z){extclock}%nat)=1%Z).
      rewrite read_signal_write_same;reflexivity. }}
   exact(eq_trans(proj2 HSampleShape 1%nat {clock}%nat {a}.clock_catalog)
     (eq_trans({a}.clock_wire _ _ HLSample)HInput)). }}
 assert(HResetSample:eval_expr(phase_driven_state {p} {f}.rise pre)(EVar 1 {reset}%nat)=0%Z).
 {{ cbn[eval_expr];rewrite({a}.reset_wire _ _ HLSample),(sampled_input {p} {extreset}%nat {f}.rise pre input_reset_unwritten).
   change(norm 1(read_signal(write_signal pre {extclock}%nat 1%Z){extreset}%nat)=0%Z).
   rewrite read_signal_write_other by discriminate;rewrite HReset;reflexivity. }}
 assert(HMatch:process_matches_states pre(phase_driven_state {p} {f}.rise pre){proc}=true).
 {{ change((edge_fires Posedge(read_signal pre {clock}%nat)(read_signal(phase_driven_state {p} {f}.rise pre){clock}%nat)||
   (edge_fires Negedge(read_signal pre {reset}%nat)(read_signal(phase_driven_state {p} {f}.rise pre){reset}%nat)||false))%bool=true).
   rewrite HOldClock,HNewClock;reflexivity. }}
 exact(actual_reset {p} 32 {root}%nat {valid}%nat {plan['bubble']}%Z {proc}(EVar 1 {reset}%nat)
  _ _ {bc} {vc} {f}.rise pre ltac:(discriminate)ltac:(discriminate)HMatch HResetSample). Qed.
Theorem actual_boot_invalid_word image:InvalidWord({f}.boot image).
Proof.
 pose proof(actual_boot_reset_payload image)as[HW HV].
 assert(HI:InvalidWord(PhaseSemantics {p} {f}.rise(reset_prefix image)))by(intro H;exact HW).
 change(InvalidWord(phase_run {p}[{f}.fall;{f}.reset_release]
  (PhaseSemantics {p} {f}.rise(reset_prefix image)))).
 apply(history {p} 32 {root}%nat {valid}%nat {plan['bubble']}%Z {proc} {word} {ve}
  {bc} {vc} actual_pair);[repeat constructor;discriminate|exact HI]. Qed.
Theorem reset_reachable_invalid_word image events:
 Forall {h}.W.Environment events ->InvalidWord(phase_run {p} events({f}.boot image)).
Proof. intro HE;apply(history {p} 32 {root}%nat {valid}%nat {plan['bubble']}%Z {proc} {word} {ve}
 {bc} {vc} actual_pair);[eapply Forall_impl;[exact protects|exact HE]|exact(actual_boot_invalid_word image)]. Qed.
Theorem actual_sampled_invalid_word image events ev:
 let pre:=phase_run {p} events({f}.boot image)in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->norm 1(read_signal pre {valid}%nat)=0%Z ->
 norm 32(read_signal {sample}{root}%nat)=norm 32 {plan['bubble']}%Z.
Proof. intros pre HE HEv HV.
 rewrite(sampled_root_preserved {p} ev pre {root}%nat(history_comb_frame _ _ _ _ _ {bc})(proj1(protects ev HEv))).
 exact(reset_reachable_invalid_word image events HE HV). Qed.
Goal True. idtac "INVALID_FETCH_AUDIT". exact I. Qed.
Print Assumptions actual_pair.
Print Assumptions actual_invalid_word_phase.
Print Assumptions actual_boot_reset_payload.
Print Assumptions actual_boot_invalid_word.
Print Assumptions reset_reachable_invalid_word.
Print Assumptions actual_sampled_invalid_word.
'''
    if shallow_boot:
        old=f''' change(InvalidWord(phase_run {p}[{f}.fall;{f}.reset_release]
  (PhaseSemantics {p} {f}.rise(reset_prefix image)))).
 apply(history {p} 32 {root}%nat {valid}%nat {plan['bubble']}%Z {proc} {word} {ve}
  {bc} {vc} actual_pair);[repeat constructor;discriminate|exact HI]. Qed.'''
        suffix=f'''Local Opaque phase_run.
Lemma boot_suffix image:{f}.boot image=phase_run {p}[{f}.fall;{f}.reset_release]
 (PhaseSemantics {p} {f}.rise(reset_prefix image)).
Proof. exact(ExtendedSVInvalidPayload.four_phases {p} {f}.reset_assert {f}.rise {f}.fall {f}.reset_release({f}.seed image)). Qed.
'''
        new=f''' assert(HResult:InvalidWord(phase_run {p}[{f}.fall;{f}.reset_release]
  (PhaseSemantics {p} {f}.rise(reset_prefix image)))).
 {{ exact(ExtendedSVInvalidPayload.history {p} 32 {root}%nat {valid}%nat {plan['bubble']}%Z {proc} {word} {ve}
  {bc} {vc} actual_pair [{f}.fall;{f}.reset_release] ltac:(repeat constructor;discriminate)
  (PhaseSemantics {p} {f}.rise(reset_prefix image))HI). }}
 exact(eq_rect _ InvalidWord HResult _ (eq_sym(boot_suffix image))). Qed.'''
        if source.count(old)!=1:raise ValueError('original boot transport shape changed')
        source=source.replace('Theorem actual_boot_invalid_word',suffix+'Theorem actual_boot_invalid_word',1).replace(old,new,1)
        source+='Print Assumptions boot_suffix.\n'
    return source


def check(c,output,shallow_boot=False,baseline=None,budget_seconds=1200):
    if not 0<budget_seconds<=1200:raise ValueError('native attempt budget must be within 20 minutes')
    out=Path(output);out.mkdir(parents=True,exist_ok=False);pc=fetch.pc
    graph=pc.admission.fetch.cdfg.checked_graph(c['graph'],c['ast'],out/'replayed')
    raw,profile,_=pc.admission.fetch.cdfg.raw_binding(c['ast'],c['ast_module']);plan=discover(c,raw,profile,graph)
    paths=checked_provider(c['normal_write'],'NormalWrite.v',raw['source_sha256'],['all_normal_ADD_RF_phase_branches_proved'])
    paths +=[dict(namespace='GeneratedNormalWrite',directory=str(Path(c['normal_write']).resolve()))]
    source=render(c,raw,profile,plan,shallow_boot);file=out/'InvalidFetch.v';file.write_text(source)
    if shallow_boot:
        if baseline is None:raise ValueError('an actual native 20-minute timeout is required before this repair')
        old_dir=Path(baseline);old=json.loads((old_dir/'report.json').read_text())
        original=render(c,raw,profile,plan)
        if not(old.get('coqc_timed_out')is True and old.get('coqc_exit')==124 and old.get('seconds',0)>=1200
            and old.get('source_sha256')==hashlib.sha256(original.encode()).hexdigest()
            and (old_dir/'InvalidFetch.v').read_text()==original):
            raise ValueError('unchanged real 20-minute baseline required')
        targets=['actual_boot_invalid_word','reset_reachable_invalid_word','actual_sampled_invalid_word']
        pins=[]
        for target in targets:
            before=original.split('Theorem '+target)[1].split('Proof.')[0]
            after_header=source.split('Theorem '+target)[1].split('Proof.')[0]
            if before!=after_header:raise ValueError('boot repair changed a target')
            pins.append(dict(target=target,signature_sha256=hashlib.sha256(before.encode()).hexdigest()))
        (out/'same-target-repair.json').write_text(json.dumps(dict(baseline=str(old_dir),
            baseline_coqc_exit=old['coqc_exit'],baseline_seconds=old['seconds'],targets=pins,
            repair='checked shallow boot state equality and explicit eq_rect; no RTL/ISA/environment/target change'),indent=2)+'\n')
    for name,data in [('plan',plan),('providers',paths)]:
        (out/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
    flags=list(pc.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedInvalidFetch'];start=time.monotonic()
    cc,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqc.resources').resolve()),
        str(pc.rtl.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',budget_seconds)
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=timed,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        ast_sha256=raw['source_sha256'],graph_sha256=hashlib.sha256(Path(c['graph']).read_bytes()).hexdigest(),old_inv_read=False,
        reset_reachable_invalid_payload_proved=False,shallow_boot_repair=shallow_boot,native_budget_seconds=budget_seconds,full_R_generated=False,full_cycle_preservation_proved=False,
        itree_refinement_proved=False,external_llm_api_calls=0)
    if cc.returncode==0:
        audit=cc.stdout.split('INVALID_FETCH_AUDIT')[-1]
        closed=audit.count('Closed under the global context')==(7 if shallow_boot else 6) and'Axioms:'not in audit
        kk,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqchk.resources').resolve()),
            str(pc.rtl.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedInvalidFetch.InvalidFetch'],
            out/'coqchk.log',max(.1,budget_seconds-(time.monotonic()-start)))
        ok=closed and kk.returncode==0
        report.update(accepted=ok,coqchk_exit=kk.returncode,coqchk_timed_out=timed,
            assumptions_closed=closed,reset_reachable_invalid_payload_proved=ok)
    report['seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(file.with_suffix('.vo').read_bytes()).hexdigest()
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['inputs','output']:p.add_argument('--'+key,required=True)
    p.add_argument('--shallow-boot',action='store_true');p.add_argument('--baseline')
    p.add_argument('--budget-seconds',type=float,default=1200)
    a=p.parse_args()
    try:r=check(json.loads(Path(a.inputs).read_text()),a.output,a.shallow_boot,a.baseline,a.budget_seconds)
    except Exception as exc:
        out=Path(a.output)
        if out.is_dir()and not(out/'report.json').exists():
            (out/'report.json').write_text(json.dumps(dict(accepted=False,stage='preflight',error=str(exc),cli_exit=1),indent=2)+'\n')
        raise
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
