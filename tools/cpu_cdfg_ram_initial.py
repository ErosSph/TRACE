"""Establish the generated RAM relation along the unchanged real reset run.

Uses actual phase projections and the original frozen four-event bootstrap.
No pre-existing CPU initialization/INV theorem, new reset or changed seed is
read. The separate unfinished RF initialization proof is not rerun here.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_cdfg_ram_joint as ram
from cpu_certificate_acceptance import run_stage

pc = ram.pc


def discover(c, raw, profile, graph):
    plan=ram.discover(c,raw,profile,graph)
    history=json.loads((Path(c['history'])/'plan.json').read_text())
    folder=next(Path(row['directory']) for row in history['paths'] if row['namespace']=='GeneratedSeedBoot')
    text=(folder/'FrozenEnvironment.v').read_text()
    frozen_hash=hashlib.sha256(text.encode()).hexdigest()
    previous=json.loads((Path(c['cycle_joint'])/'plan.json').read_text())['scheduler']
    if frozen_hash!=previous['frozen_source_sha256']:
        raise ValueError('original frozen environment source changed')
    reset=plan['chains']['reset']['terminal']
    for name,old,new in [('reset_assert',1,0),('reset_release',0,1)]:
        expected=f'Definition {name}:Event:={{|changed_signal:={reset}%nat;old_value:={old}%Z;new_value:={new}%Z|}}.'
        if text.count(expected)!=1:
            raise ValueError('unsupported original bootstrap reset event: '+name)
    sequence='Definition boot_events:list Event:=[reset_assert;rise;fall;reset_release].'
    if text.count(sequence)!=1:
        raise ValueError('original bootstrap event order changed')
    plan.update(bootstrap=dict(source=str(folder/'FrozenEnvironment.v'),source_sha256=frozen_hash,
        events=['reset_assert','rise','fall','reset_release'],new_environment=False,
        preexisting_CPU_initialization_theorem_read=False))
    return plan


def render(c, raw, profile, plan):
    p,am=profile['ast']['program'],raw['module'];bank=plan['byte_bank'];root=bank['root'];width=bank['width']
    h='GeneratedCapturedHistoryBoot.CapturedHistoryBoot';f=h+'.F';cap=h+'.C'
    aq='GeneratedAdmissionQueue.AdmissionQueue';rq='GeneratedRAMJoint.RAMJoint';cl='GeneratedClockCycleJoint.CycleJoint'
    inf='GeneratedInvalidFetch.InvalidFetch';fa='GeneratedFetchAdmission.FetchAdmission'
    cat='GeneratedDependencyCatalog.Catalog.actual_catalog';cert='GeneratedBoundedPhase.Phase.actual_certificate'
    reset=plan['chains']['reset']['terminal'];clock=plan['chains']['clock']['terminal']
    stages=plan['store_stages'];pair=plan['pair'];word=pair['carrier'];valid=pair['valid_root'];bubble=plan['bubble']
    source=f'''From Coq Require Import List ZArith Bool Lia.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVScalarExpression Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVBootstrap
 Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVInvalidPayload
 Ex.External.CPUByteBankRelation Ex.RvCore.FormalSpec coqutil.Word.Interface coqutil.Word.Properties
 coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 GeneratedRAMJoint.RAMJoint GeneratedClockCycleJoint.CycleJoint GeneratedInvalidFetch.InvalidFetch.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory ExtendedSVScalarExpression
 ExtendedSVEmptyPipeline ExtendedSVBootstrap ExtendedSVBoundedCatalogPhase.
Local Open Scope Z_scope.
Local Opaque {p} PhaseSemantics phase_run {cat} {cert}.
Definition after_assert image:={inf}.reset_prefix image.
Definition after_reset_rise image:=PhaseSemantics {p} {f}.rise(after_assert image).
Definition before_release image:=PhaseSemantics {p} {f}.fall(after_reset_rise image).
Definition boot_finish image:=PhaseSemantics {p} {f}.reset_release(before_release image).
Definition sample_seed ev pre:=write_signal pre(changed_signal ev)(new_value ev).
Lemma actual_boot_finish image:{f}.boot image=boot_finish image.
Proof. exact(eq_trans({inf}.boot_suffix image)
 ({cl}.run_two {p} {f}.fall {f}.reset_release(after_reset_rise image))). Qed.
Lemma original_boot_event ev:In ev {f}.boot_events ->{h}.W.Environment ev.
Proof. exact(proj1(@List.Forall_forall Event {h}.W.Environment {f}.boot_events){h}.W.boot_environment ev). Qed.
Theorem actual_boot_sample_evidence image:
 CombLFP {p}(sample_seed {f}.reset_assert({f}.seed image))
  (phase_driven_state {p} {f}.reset_assert({f}.seed image)) /\\
 CombLFP {p}(sample_seed {f}.rise(after_assert image))
  (phase_driven_state {p} {f}.rise(after_assert image)) /\\
 CombLFP {p}(sample_seed {f}.fall(after_reset_rise image))
  (phase_driven_state {p} {f}.fall(after_reset_rise image)) /\\
 CombLFP {p}(sample_seed {f}.reset_release(before_release image))
  (phase_driven_state {p} {f}.reset_release(before_release image)).
Proof.
 assert(HA:{h}.W.Environment {f}.reset_assert)by(apply original_boot_event;cbn;tauto).
 assert(HR:{h}.W.Environment {f}.rise)by(apply original_boot_event;cbn;tauto).
 assert(HF:{h}.W.Environment {f}.fall)by(apply original_boot_event;cbn;tauto).
 assert(HE:{h}.W.Environment {f}.reset_release)by(apply original_boot_event;cbn;tauto).
 destruct(catalog_phase_evidence {p} {cat} {cert} {f}.reset_assert({f}.seed image)(proj1 HA)({h}.B.seed_shape image))as[HLA[_ HSA]].
 change(CatalogShape {p} {cat}(after_assert image))in HSA.
 destruct(catalog_phase_evidence {p} {cat} {cert} {f}.rise(after_assert image)(proj1 HR)HSA)as[HLR[_ HSR]].
 change(CatalogShape {p} {cat}(after_reset_rise image))in HSR.
 destruct(catalog_phase_evidence {p} {cat} {cert} {f}.fall(after_reset_rise image)(proj1 HF)HSR)as[HLF[_ HSF]].
 change(CatalogShape {p} {cat}(before_release image))in HSF.
 destruct(catalog_phase_evidence {p} {cat} {cert} {f}.reset_release(before_release image)(proj1 HE)HSF)as[HLE _].
 exact(conj HLA(conj HLR(conj HLF HLE))). Qed.
'''
    for r in [row['root'] for row in stages]+[root]:
        source+=f'''Lemma actual_seed_zero_{r} image:read_signal({f}.seed image){r}%nat=0.
Proof. unfold {f}.seed,{f}.writes,ExtendedSVBootstrap.seed_writes;cbn[fold_left fst snd].
 repeat(rewrite read_signal_write_other by discriminate);apply read_zero_seed. Qed.
'''
    source+=f'''Lemma actual_seed_quiet image:{rq}.StoreQuiet({f}.seed image).
Proof. split;[rewrite actual_seed_zero_{stages[0]['root']}|rewrite actual_seed_zero_{stages[1]['root']}];reflexivity. Qed.
Lemma external_reset_assert_sample pre:
 read_signal(phase_driven_state {p} {f}.reset_assert pre){reset}%nat=0.
Proof. rewrite(sampled_input {p} {reset}%nat {f}.reset_assert pre {inf}.input_reset_unwritten);apply read_signal_write_same. Qed.
Lemma reset_unchanged_sample ev pre:
 changed_signal ev<>{reset}%nat ->read_signal pre {reset}%nat=0 ->
 read_signal(phase_driven_state {p} ev pre){reset}%nat=0.
Proof. intros HE HR;rewrite(sampled_input {p} {reset}%nat ev pre {inf}.input_reset_unwritten).
 rewrite read_signal_write_other by congruence;exact HR. Qed.
Lemma actual_reset_prefix_inputs image:
 read_signal(after_assert image){reset}%nat=0 /\\
 read_signal(after_reset_rise image){reset}%nat=0 /\\
 read_signal(before_release image){reset}%nat=0.
Proof.
 assert(HA:read_signal(after_assert image){reset}%nat=0).
 {{ unfold after_assert,{inf}.reset_prefix;rewrite(phase_input {p} {reset}%nat {f}.reset_assert({f}.seed image){inf}.input_reset_unwritten).
    apply read_signal_write_same. }}
 assert(HR:read_signal(after_reset_rise image){reset}%nat=0).
 {{ unfold after_reset_rise;rewrite(phase_input {p} {reset}%nat {f}.rise(after_assert image){inf}.input_reset_unwritten).
    change(read_signal(write_signal(after_assert image){clock}%nat 1){reset}%nat=0).
    rewrite read_signal_write_other by discriminate;exact HA. }}
 assert(HF:read_signal(before_release image){reset}%nat=0).
 {{ unfold before_release;rewrite(phase_input {p} {reset}%nat {f}.fall(after_reset_rise image){inf}.input_reset_unwritten).
    change(read_signal(write_signal(after_reset_rise image){clock}%nat 0){reset}%nat=0).
    rewrite read_signal_write_other by discriminate;exact HR. }}
 exact(conj HA(conj HR HF)). Qed.
Theorem actual_reset_quiet_phase ev pre seed:
 {h}.W.Environment ev ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->
 read_signal(phase_driven_state {p} ev pre){reset}%nat=0 ->{rq}.StoreQuiet pre ->
 {rq}.StoreQuiet(PhaseSemantics {p} ev pre).
Proof. intros HE HL HR[HX HY];split.
'''
    for row,old in zip(stages,['HX','HY']):
        r=row['root'];rst=row['reset']
        source+=f''' - assert(HReset:norm 1(read_signal(phase_driven_state {p} ev pre){rst}%nat)=0).
   {{ exact(eq_trans({rq}.wire_{rst} seed _ HL)(f_equal(norm 1)HR)). }}
   rewrite({rq}.Scalar.root_{r}_expression_phase ev pre({rq}.protects ev {r}%nat HE ltac:(cbn;tauto))).
   destruct(process_matches_states pre(phase_driven_state {p} ev pre){am}.{row['process']});[|exact {old}].
   unfold {rq}.Scalar.root_{r}_expression;cbn[eval_expr];rewrite HReset;reflexivity.
'''
    source+=f'''Qed.
Definition Bubble pre:=norm 32(read_signal pre {word}%nat)=norm 32 {bubble} /\\norm 1(read_signal pre {valid}%nat)=0.
Theorem actual_reset_bubble_phase ev pre seed:
 {h}.W.Environment ev ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->
 read_signal(phase_driven_state {p} ev pre){reset}%nat=0 ->Bubble pre ->
 Bubble(PhaseSemantics {p} ev pre).
Proof. intros HE HL HR[HW HV].
 assert(HReset:norm 1(read_signal(phase_driven_state {p} ev pre){plan['chains']['reset']['source']}%nat)=0).
 {{ exact(eq_trans({fa}.reset_wire seed _ HL)(f_equal(norm 1)HR)). }}
 split.
 - rewrite(history_phase_projection _ _ _ _ _ {cap}.B.root_{word}_birth_certificate ev pre
    ({aq}.internal_event ev {word}%nat HE ltac:(lia))).
   destruct(process_matches_states pre(phase_driven_state {p} ev pre){am}.{pair['process']});[|exact HW].
   unfold {cap}.B.root_{word}_expression;cbn[eval_expr];rewrite HReset;reflexivity.
 - rewrite(history_phase_projection _ _ _ _ _ {cap}.B.root_{valid}_birth_certificate ev pre
    ({aq}.internal_event ev {valid}%nat HE ltac:(lia))).
   destruct(process_matches_states pre(phase_driven_state {p} ev pre){am}.{pair['process']});[|exact HV].
   unfold {cap}.B.root_{valid}_expression;cbn[eval_expr];rewrite HReset;reflexivity. Qed.
Theorem actual_boot_store_and_RAM image:
 {rq}.StoreQuiet({f}.boot image) /\\read_signal({f}.boot image){root}%nat=0.
Proof.
 assert(HA:{h}.W.Environment {f}.reset_assert)by(apply original_boot_event;cbn;tauto).
 assert(HR:{h}.W.Environment {f}.rise)by(apply original_boot_event;cbn;tauto).
 assert(HF:{h}.W.Environment {f}.fall)by(apply original_boot_event;cbn;tauto).
 assert(HE:{h}.W.Environment {f}.reset_release)by(apply original_boot_event;cbn;tauto).
 destruct(actual_boot_sample_evidence image)as[HLA[HLR[HLF HLE]]].
 destruct(actual_reset_prefix_inputs image)as[HRA[HRR HRF]].
 pose proof(external_reset_assert_sample({f}.seed image))as HSA.
 pose proof(reset_unchanged_sample {f}.rise(after_assert image)ltac:(discriminate)HRA)as HSR.
 pose proof(reset_unchanged_sample {f}.fall(after_reset_rise image)ltac:(discriminate)HRR)as HSF.
 pose proof(actual_seed_quiet image)as HQ0.
 pose proof(actual_reset_quiet_phase {f}.reset_assert({f}.seed image)_ HA HLA HSA HQ0)as HQ1.
 change({rq}.StoreQuiet(after_assert image))in HQ1.
 pose proof(actual_reset_quiet_phase {f}.rise(after_assert image)_ HR HLR HSR HQ1)as HQ2.
 change({rq}.StoreQuiet(after_reset_rise image))in HQ2.
 pose proof(actual_reset_quiet_phase {f}.fall(after_reset_rise image)_ HF HLF HSF HQ2)as HQ3.
 change({rq}.StoreQuiet(before_release image))in HQ3.
 pose proof({inf}.actual_boot_reset_payload image)as HBR.
 change(Bubble(after_reset_rise image))in HBR.
 pose proof(actual_reset_bubble_phase {f}.fall(after_reset_rise image)_ HF HLF HSF HBR)as HBF.
 change(Bubble(before_release image))in HBF.
 assert(HWord:norm 32(read_signal(phase_driven_state {p} {f}.reset_release(before_release image)){word}%nat)=norm 32 {bubble}).
 {{ rewrite(sampled_root_preserved {p} {f}.reset_release(before_release image){word}%nat
   {cap}.B.root_{word}_comb_frame({aq}.internal_event {f}.reset_release {word}%nat HE ltac:(lia)));exact(proj1 HBF). }}
 pose proof(GeneratedStoreControl.StoreControl.actual_bubble_nonstore _ _ HLE HWord)as HC.
 pose proof({rq}.actual_quiet_phase {f}.reset_release(before_release image)_ HE HLE HQ3 HC)as HQ4.
 pose proof({rq}.actual_quiet_RAM_phase {f}.reset_assert({f}.seed image)_ HA HLA HQ0)as HM1.
 change(read_signal(after_assert image){root}%nat=read_signal({f}.seed image){root}%nat)in HM1.
 pose proof({rq}.actual_quiet_RAM_phase {f}.rise(after_assert image)_ HR HLR HQ1)as HM2.
 change(read_signal(after_reset_rise image){root}%nat=read_signal(after_assert image){root}%nat)in HM2.
 pose proof({rq}.actual_quiet_RAM_phase {f}.fall(after_reset_rise image)_ HF HLF HQ2)as HM3.
 change(read_signal(before_release image){root}%nat=read_signal(after_reset_rise image){root}%nat)in HM3.
 pose proof({rq}.actual_quiet_RAM_phase {f}.reset_release(before_release image)_ HE HLE HQ3)as HM4.
 assert(HDone:{rq}.StoreQuiet(boot_finish image) /\\read_signal(boot_finish image){root}%nat=0).
 {{ exact(conj HQ4(eq_trans HM4(eq_trans HM3(eq_trans HM2(eq_trans HM1(actual_seed_zero_{root} image)))))). }}
 exact(eq_rect _ (fun state=>{rq}.StoreQuiet state /\\read_signal state {root}%nat=0)HDone _ (eq_sym(actual_boot_finish image))). Qed.
Section OriginalISA.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{registers_ok:map.ok Registers}}{{mem_ok:map.ok Mem}}.
Theorem actual_boot_original_memory image initial_imem:
 {rq}.StoreQuiet({f}.boot image) /\\
 CPUByteBankRelation.Related {width} {root}%nat {width//8}%nat({f}.boot image)
  (getDataMem(FormalSpec.initial_state initial_imem)).
Proof. destruct(actual_boot_store_and_RAM image)as[HQ HM];split;[exact HQ|].
 change(CPUByteBankRelation.Related {width} {root}%nat {width//8}%nat({f}.boot image)FormalSpec.zeroed).
 exact(CPUByteBankRelation.zeroed_bank {width} {root}%nat {width//8}%nat({f}.boot image)HM). Qed.
End OriginalISA.
Goal True. idtac "RAM_INITIAL_AUDIT". exact I. Qed.
'''
    exports=['actual_boot_finish','actual_boot_sample_evidence','actual_reset_quiet_phase',
        'actual_reset_bubble_phase','actual_boot_store_and_RAM','actual_boot_original_memory']
    source+=''.join(f'Print Assumptions {name}.\n' for name in exports)
    return source,exports


def check(c, output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    graph=pc.admission.fetch.cdfg.checked_graph(c['graph'],c['ast'],out/'replayed')
    raw,profile,_=pc.admission.fetch.cdfg.raw_binding(c['ast'],c['ast_module']);plan=discover(c,raw,profile,graph)
    provider=Path(c['ram_joint']);receipt=json.loads((provider/'report.json').read_text());expected,_=ram.render(c,raw,profile,plan)
    if not(receipt.get('accepted') and receipt.get('coqc_exit')==receipt.get('coqchk_exit')==0
        and receipt.get('assumptions_closed') and receipt.get('ast_sha256')==raw['source_sha256']
        and(provider/'RAMJoint.v').read_text()==expected
        and hashlib.sha256(expected.encode()).hexdigest()==receipt['source_sha256']
        and hashlib.sha256((provider/'RAMJoint.vo').read_bytes()).hexdigest()==receipt['object_sha256']):
        raise ValueError('unchanged checked actual RAM phase provider required')
    paths=json.loads((provider/'providers.json').read_text())+[dict(namespace='GeneratedRAMJoint',directory=str(provider.resolve()))]
    source,exports=render(c,raw,profile,plan);file=out/'RAMInitial.v';file.write_text(source)
    for key,value in [('plan',plan),('providers',paths),('exports',exports)]:
        (out/(key+'.json')).write_text(json.dumps(value,indent=2)+'\n')
    flags=list(pc.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedRAMInitial'];start=time.monotonic()
    cc,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqc.resources').resolve()),str(pc.rtl.ROOT/'_opam/bin/coqc'),
        '-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=timed,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),ast_sha256=raw['source_sha256'],
        graph_sha256=hashlib.sha256(Path(c['graph']).read_bytes()).hexdigest(),old_inv_read=False,
        actual_boot_establishes_store_and_original_memory_relation=False,register_initialization_retried=False,
        full_R_generated=False,full_reset_R_proved=False,itree_refinement_proved=False,external_llm_api_calls=0)
    if cc.returncode==0:
        audit=cc.stdout.split('RAM_INITIAL_AUDIT')[-1]
        closed=audit.count('Closed under the global context')==len(exports) and 'Axioms:'not in audit
        kk,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqchk.resources').resolve()),str(pc.rtl.ROOT/'_opam/bin/coqchk'),
            '-silent',*flags,'-norec','GeneratedRAMInitial.RAMInitial'],out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        ok=closed and kk.returncode==0
        report.update(accepted=ok,coqchk_exit=kk.returncode,coqchk_timed_out=timed,assumptions_closed=closed,
            actual_boot_establishes_store_and_original_memory_relation=ok)
    report['seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(file.with_suffix('.vo').read_bytes()).hexdigest()
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ['inputs','output']:parser.add_argument('--'+key,required=True)
    args=parser.parse_args()
    try:result=check(json.loads(Path(args.inputs).read_text()),args.output)
    except Exception as exc:
        out=Path(args.output)
        if out.is_dir() and not(out/'report.json').exists():
            (out/'report.json').write_text(json.dumps(dict(accepted=False,stage='preflight',error=str(exc),cli_exit=1),indent=2)+'\n')
        raise
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
