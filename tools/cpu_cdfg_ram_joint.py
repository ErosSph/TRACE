"""Consume the discovered real store path in ADD-cycle physical RAM proofs.

Quiet store controls are present-state fields of R, not new environment axioms.
Their next values are proved from the actual controller, captured instruction,
and the original rise/fall schedule. Byte-bank updates remain original NbPlans.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_cdfg_store_control as control
from cpu_certificate_acceptance import run_stage

pc = control.pc


def discover(c, raw, profile, graph):
    plan = control.discover(c, raw, profile, graph)
    bank = plan['byte_bank']; head = plan['pc_plan']; stages = list(reversed(plan['store_captures']))
    # This milestone handles in-order two-stage store controls. Unknown lengths
    # are obligations, never silently truncated to match this proof template.
    if len(stages) != 2 or stages[0]['process'] != head['head_process']:
        raise ValueError('unsupported store pipeline depth or head phase')
    clock = plan['chains']['clock']['terminal']; reset = plan['chains']['reset']['terminal']
    routes = []
    for row in stages + [bank]:
        edges = re.findall(r'event_edge := (Posedge|Negedge); event_signal := (\d+)', row['events'])
        expected = ['Posedge'] if row is bank else ['Posedge', 'Negedge']
        if [e for e, _ in edges] != expected:
            raise ValueError('store or RAM has a different original event phase')
        row['clock'] = int(edges[0][1]); row['clock_route'] = pc.alias_chain(raw, row['clock'], 1)
        if row['clock_route']['terminal'] != clock:
            raise ValueError('RAM and store controls do not share the original clock')
        routes.append(row['clock_route'])
        if row is not bank:
            row['reset_route'] = pc.alias_chain(raw, row['reset'], 1)
            if row['reset_route']['terminal'] != reset or int(edges[1][1]) != row['reset']:
                raise ValueError('store control reset mismatch')
            routes.append(row['reset_route'])
    routes += [row['aliases'] for row in plan['store_captures']]
    routes.append(plan['store_controller']['alias_tail'])
    roots = {edge['root'] for route in routes for edge in route['edges']}
    wires = pc.comb.analyze(raw, roots)
    if wires['residuals']:
        raise ValueError('unresolved actual store timing or data aliases')
    plan.update(store_stages=stages, ram_wire_roots=sorted(roots),
        ram_wire_ports=[{k:v for k,v in row.items() if k != 'rhs'} for row in wires['ports']])
    return plan


def render(c, raw, profile, plan):
    p, am = profile['ast']['program'], raw['module']; bank = plan['byte_bank']; stages = plan['store_stages']
    x, y = stages; ctl = plan['store_controller']; root = bank['root']; width = bank['width']
    _, residuals, _, scalar, _ = pc.scalar.proposal(profile, {x['root'], y['root']})
    if residuals:
        raise ValueError('original store scalar compilation has residuals')
    analysis = pc.rtl.analyze(raw)
    analysis['plans'] = [(proc, nb) for proc, nb in analysis['plans'] if proc['name'] == bank['process']]
    analysis.update(effects=[], residual=[], roots=[root], plan_roots=[root])
    ram = pc.rtl.render_adapter(c['ast_module'], p, raw, analysis)
    wires = pc.comb.analyze(raw, plan['ram_wire_roots'])
    ws = pc.comb.ports.render(profile['ast'], raw, wires)
    ports = {row['output_root']:i for i,row in enumerate(wires['ports'])}
    h = 'GeneratedCapturedHistoryBoot.CapturedHistoryBoot'; f = h + '.F'; cap = h + '.C'
    q = 'GeneratedPhasePendingCommit.PhasePendingCommit'; aq = 'GeneratedAdmissionQueue.AdmissionQueue'
    cl = 'GeneratedClockCycleJoint.CycleJoint'; inf = 'GeneratedInvalidFetch.InvalidFetch'
    cat = 'GeneratedDependencyCatalog.Catalog.actual_catalog'; cert = 'GeneratedBoundedPhase.Phase.actual_certificate'
    source = 'Module Scalar.\n' + scalar + '\nEnd Scalar.\nModule RAM.\n' + ram + '\nEnd RAM.\nModule Wires.\n' + ws + '\nEnd Wires.\n'
    source += f'''From Coq Require Import List ZArith Bool Lia.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVScalarExpression Lang.ExtendedSVRootProjection Lang.ExtendedSVAutoAdapterPlan Lang.ExtendedSVAutoAdapterPhase
 Lang.ExtendedSVBootstrap Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVEmptyPipeline
 Lang.ExtendedSVCaptureBirth Lang.ExtendedSVStallFlush Lang.ExtendedSVRuntimeHistory
 GeneratedStoreControl.StoreControl GeneratedClockCycleJoint.CycleJoint GeneratedInvalidFetch.InvalidFetch.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory ExtendedSVScalarExpression
 ExtendedSVRootProjection ExtendedSVAutoAdapterPlan ExtendedSVAutoAdapterPhase ExtendedSVBootstrap
 ExtendedSVBoundedCatalogPhase ExtendedSVDependencyCatalog ExtendedSVEmptyPipeline ExtendedSVCaptureBirth ExtendedSVRuntimeHistory.
Local Open Scope Z_scope.
Local Opaque {p} PhaseSemantics phase_run {cat} {cert}.
Definition StoreQuiet pre:=norm 1(read_signal pre {x['root']}%nat)=0 /\\norm 1(read_signal pre {y['root']}%nat)=0.
'''
    routes = [row['aliases'] for row in plan['store_captures']] + [ctl['alias_tail']]
    routes += [row['clock_route'] for row in stages + [bank]] + [row['reset_route'] for row in stages]
    for route in routes:
        stem = f'wire_{route["source"]}'
        if f'Lemma {stem} ' in source:
            continue
        source += f'''Lemma {stem} seed fixed:CombLFP {p} seed fixed ->
 norm 1(read_signal fixed {route['source']}%nat)=norm 1(read_signal fixed {route['terminal']}%nat).
Proof. intro HL.
'''
        for edge in route['edges']:
            k = ports[edge['root']]
            source += f'rewrite(Wires.port_{k}_lfp seed fixed HL);unfold Wires.port_{k}_rhs;cbn[eval_expr];rewrite norm_idempotent.\n'
        source += 'reflexivity. Qed.\n'
    source += f'''Lemma protects ev r:{h}.W.Environment ev ->In r[{x['root']}%nat;{y['root']}%nat;{root}%nat] ->changed_signal ev<>r.
Proof. intros HE HI;apply({aq}.internal_event ev r HE);cbn in HI;lia. Qed.
Theorem actual_store_controls_zero image events ev:
 let pre:=phase_run {p} events({f}.boot image)in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->
 (norm 1(read_signal pre {plan['pair']['valid_root']}%nat)<>0 ->
  forall token,current(fst({h}.boot_history image events))=Some token ->exists d s1 s2,
  Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add d s1 s2)) ->
 norm 1(read_signal(phase_driven_state {p} ev pre){ctl['root']}%nat)=0.
Proof. intros pre HE HEv HClass.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 destruct(ExtendedSVStallFlush.one_bit_cases pre {plan['pair']['valid_root']}%nat)as[HV|HV].
 - pose proof({inf}.actual_sampled_invalid_word image events ev HE HEv HV)as HW;fold pre in HW.
   exact(GeneratedStoreControl.StoreControl.actual_bubble_nonstore seed _ HL HW).
 - assert(HValid:norm 1(read_signal pre {plan['pair']['valid_root']}%nat)<>0)by congruence.
   pose proof(proj1({h}.boot_and_runtime_related image events HE))as HC;fold pre in HC.
   destruct(proj1(proj1(proj1 HC)))as[HCurrent HW].
   destruct(HCurrent HValid)as[token HT].
   destruct(HClass HValid token HT)as[d[s1[s2 HD]]].
   assert(HWord:norm 32(read_signal(phase_driven_state {p} ev pre){plan['pair']['carrier']}%nat)=norm 32(token_word token)).
   {{ rewrite(sampled_root_preserved {p} ev pre {plan['pair']['carrier']}%nat
      {cap}.B.root_{plan['pair']['carrier']}_comb_frame({aq}.internal_event ev {plan['pair']['carrier']}%nat HEv ltac:(lia))).
     exact(HW token HT). }}
   exact(GeneratedStoreControl.StoreControl.actual_original_ADD_nonstore seed _ (token_word token)d s1 s2 HL HWord HD). Qed.
Theorem actual_quiet_phase ev pre seed:
 {h}.W.Environment ev ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->StoreQuiet pre ->
 norm 1(read_signal(phase_driven_state {p} ev pre){ctl['root']}%nat)=0 ->
 StoreQuiet(PhaseSemantics {p} ev pre).
Proof. intros HE HL[HX HY]HC;split.
'''
    for row, old, incoming, route in [(x,'HX','HC',ctl['alias_tail']), (y,'HY','HX',x['aliases'])]:
        # MEM input aliases source x, while EX input aliases the controller.
        route = ctl['alias_tail'] if row is x else x['aliases']
        r = row['root']; inp = row['input']
        source += f''' - rewrite(Scalar.root_{r}_expression_phase ev pre(protects ev {r}%nat HE ltac:(cbn;tauto))).
   destruct(process_matches_states pre(phase_driven_state {p} ev pre){am}.{row['process']});[|exact {old}].
   unfold Scalar.root_{r}_expression;cbn[eval_expr];rewrite(wire_{inp} seed _ HL).
'''
        if row is y:
            source += f'''   rewrite(sampled_root_preserved {p} ev pre {x['root']}%nat Scalar.root_{x['root']}_comb_frame
     (protects ev {x['root']}%nat HE ltac:(cbn;tauto))).
'''
        source += f'''   rewrite {incoming};repeat match goal with|-context[if ?flag then _ else _]=>destruct flag eqn:? end;reflexivity.
'''
    source += f'''Qed.
Theorem actual_quiet_idle_phase ev pre:
 {h}.W.Environment ev ->StoreQuiet pre ->
 process_matches_states pre(phase_driven_state {p} ev pre){am}.{x['process']}=false ->
 process_matches_states pre(phase_driven_state {p} ev pre){am}.{y['process']}=false ->
 StoreQuiet(PhaseSemantics {p} ev pre).
Proof. intros HE[HX HY]HM HN;split.
 - rewrite(Scalar.root_{x['root']}_expression_phase ev pre(protects ev {x['root']}%nat HE ltac:(cbn;tauto))),HM;exact HX.
 - rewrite(Scalar.root_{y['root']}_expression_phase ev pre(protects ev {y['root']}%nat HE ltac:(cbn;tauto))),HN;exact HY. Qed.
Theorem actual_quiet_RAM_phase ev pre seed:
 {h}.W.Environment ev ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->StoreQuiet pre ->
 read_signal(PhaseSemantics {p} ev pre){root}%nat=read_signal pre {root}%nat.
Proof. intros HE HL[HX HY].
 assert(HW:norm 1(read_signal(phase_driven_state {p} ev pre){bank['guard']}%nat)=0).
 {{ rewrite(wire_{bank['guard']} seed _ HL),(sampled_root_preserved {p} ev pre {y['root']}%nat
    Scalar.root_{y['root']}_comb_frame(protects ev {y['root']}%nat HE ltac:(cbn;tauto)));exact HY. }}
 rewrite(RAM.root_{root}_compiled_phase ev pre(protects ev {root}%nat HE ltac:(cbn;tauto))).
 unfold plan_transition_updates,RAM.root_{root}_plan_entries;cbn[flat_map fst snd].
 destruct(process_matches_states pre(phase_driven_state {p} ev pre){am}.{bank['process']});[|reflexivity].
 unfold RAM.{bank['process']}_plan;cbn[eval_plan flat_map eval_expr];rewrite HW;reflexivity. Qed.
'''
    # Real falling-edge sampling, including both levels of clock/reset aliases.
    source += f'''Theorem actual_store_fall_idle image events:
 let pre:=phase_run {p} events({f}.boot image)in
 Forall {h}.W.Environment events ->read_signal pre {plan['chains']['clock']['terminal']}%nat=1 ->
 read_signal pre {plan['chains']['reset']['terminal']}%nat=1 ->
 process_matches_states pre(phase_driven_state {p} {f}.fall pre){am}.{x['process']}=false /\\
 process_matches_states pre(phase_driven_state {p} {f}.fall pre){am}.{y['process']}=false.
Proof. intros pre HE HC HR;pose proof({cl}.scheduled_event_allowed {f}.fall ltac:(right;now left))as HEv.
 destruct({q}.E.runtime_evidence image events HE)as[HS[seed0 HL0]];fold pre in HS,HL0.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events {f}.fall HE HEv)as[seed HL];fold pre in HL.
 pose proof(candidate_shape {p} {cat} {cert} _(input_shape {p} {cat} {f}.fall pre(proj1 HEv)HS))as HSS.
 destruct({cl}.sampled_clock_inputs {f}.fall pre 0 eq_refl eq_refl HR)as[HSC HSR].
'''
    for row in stages:
        rclk, rst = row['clock'], row['reset']
        source += f''' assert(HOld_{rclk}:read_signal pre {rclk}%nat=1).
 {{ assert(HCat:In(1%nat,{rclk}%nat)(catalog_outputs {cat})).
    {{ vm_compute;repeat first[left;reflexivity|right]. }}
    exact(eq_trans(proj2 HS 1%nat {rclk}%nat HCat)(eq_trans(wire_{rclk} seed0 pre HL0)(f_equal(norm 1)HC))). }}
 assert(HNew_{rclk}:read_signal(phase_driven_state {p} {f}.fall pre){rclk}%nat=0).
 {{ assert(HCat:In(1%nat,{rclk}%nat)(catalog_outputs {cat})).
    {{ vm_compute;repeat first[left;reflexivity|right]. }}
    exact(eq_trans(proj2 HSS 1%nat {rclk}%nat HCat)(eq_trans(wire_{rclk} seed _ HL)(f_equal(norm 1)HSC))). }}
 assert(HOld_{rst}:read_signal pre {rst}%nat=1).
 {{ assert(HCat:In(1%nat,{rst}%nat)(catalog_outputs {cat})).
    {{ vm_compute;repeat first[left;reflexivity|right]. }}
    exact(eq_trans(proj2 HS 1%nat {rst}%nat HCat)(eq_trans(wire_{rst} seed0 pre HL0)(f_equal(norm 1)HR))). }}
 assert(HNew_{rst}:read_signal(phase_driven_state {p} {f}.fall pre){rst}%nat=1).
 {{ assert(HCat:In(1%nat,{rst}%nat)(catalog_outputs {cat})).
    {{ vm_compute;repeat first[left;reflexivity|right]. }}
    exact(eq_trans(proj2 HSS 1%nat {rst}%nat HCat)(eq_trans(wire_{rst} seed _ HL)(f_equal(norm 1)HSR))). }}
'''
    source += ' split.\n'
    for row in stages:
        rclk, rst = row['clock'], row['reset']
        source += f''' - change((edge_fires Posedge(read_signal pre {rclk}%nat)(read_signal(phase_driven_state {p} {f}.fall pre){rclk}%nat)||
   (edge_fires Negedge(read_signal pre {rst}%nat)(read_signal(phase_driven_state {p} {f}.fall pre){rst}%nat)||false))%bool=false).
   rewrite HOld_{rclk},HNew_{rclk},HOld_{rst},HNew_{rst};reflexivity.
'''
    source += f'''Qed.
Theorem actual_ADD_cycle_RAM image events:
 let pre:=phase_run {p} events({f}.boot image)in
 let mid:=phase_run {p}(events++[{f}.rise])({f}.boot image)in
 let post:=phase_run {p}((events++[{f}.rise])++[{f}.fall])({f}.boot image)in
 Forall {h}.W.Environment events ->{cl}.ClockBoundary pre ->StoreQuiet pre ->
 (norm 1(read_signal pre {plan['pair']['valid_root']}%nat)<>0 ->
  forall token,current(fst({h}.boot_history image events))=Some token ->exists d s1 s2,
  Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add d s1 s2)) ->
 StoreQuiet post /\\read_signal post {root}%nat=read_signal pre {root}%nat.
Proof. intros pre mid post HE HB HQ HClass.
 pose proof({cl}.scheduled_event_allowed {f}.rise ltac:(now left))as HER.
 pose proof({cl}.scheduled_event_allowed {f}.fall ltac:(right;now left))as HEF.
 assert(HERun:Forall {h}.W.Environment(events++[{f}.rise]))by(apply Forall_app;split;[exact HE|constructor;[exact HER|constructor]]).
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events {f}.rise HE HER)as[seed HL];fold pre in HL.
 pose proof(actual_store_controls_zero image events {f}.rise HE HER HClass)as HC;fold pre in HC.
 pose proof(actual_quiet_phase {f}.rise pre seed HER HL HQ HC)as HQMid.
 pose proof(actual_quiet_RAM_phase {f}.rise pre seed HER HL HQ)as HRMid.
 assert(HMid:mid=PhaseSemantics {p} {f}.rise pre)by(exact({cl}.run_snoc _ _ _ _)).
 assert(HEnd:post=PhaseSemantics {p} {f}.fall mid)by(exact({cl}.run_snoc _ _ _ _)).
 assert(HQuietMid:StoreQuiet mid)by(exact(eq_rect _ StoreQuiet HQMid _ (eq_sym HMid))).
 destruct({cl}.actual_scheduled_rise image events HE HB)as[_[_[HMC HMR]]];fold pre in HMC,HMR.
 assert(HMC':read_signal mid {plan['chains']['clock']['terminal']}%nat=1)by(exact(eq_trans(f_equal(fun s=>read_signal s {plan['chains']['clock']['terminal']}%nat)HMid)HMC)).
 assert(HMR':read_signal mid {plan['chains']['reset']['terminal']}%nat=1)by(exact(eq_trans(f_equal(fun s=>read_signal s {plan['chains']['reset']['terminal']}%nat)HMid)HMR)).
 destruct(actual_store_fall_idle image(events++[{f}.rise])HERun HMC' HMR')as[HIdleX HIdleY];fold mid in HIdleX,HIdleY.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image(events++[{f}.rise]){f}.fall HERun HEF)as[seedF HLF];fold mid in HLF.
 pose proof(actual_quiet_idle_phase {f}.fall mid HEF HQuietMid HIdleX HIdleY)as HQPost.
 pose proof(actual_quiet_RAM_phase {f}.fall mid seedF HEF HLF HQuietMid)as HRPost.
 split;[exact(eq_rect _ StoreQuiet HQPost _ (eq_sym HEnd))|].
 exact(eq_trans(f_equal(fun s=>read_signal s {root}%nat)HEnd)
  (eq_trans HRPost(eq_trans(f_equal(fun s=>read_signal s {root}%nat)HMid)HRMid))). Qed.
Goal True. idtac "RAM_JOINT_AUDIT". exact I. Qed.
'''
    exports = ['actual_store_controls_zero', 'actual_quiet_phase', 'actual_quiet_idle_phase',
        'actual_quiet_RAM_phase', 'actual_store_fall_idle', 'actual_ADD_cycle_RAM']
    source += ''.join(f'Print Assumptions {target}.\n' for target in exports)
    return source, exports


def check(c, store_control, output):
    out = Path(output); out.mkdir(parents=True, exist_ok=False)
    graph = pc.admission.fetch.cdfg.checked_graph(c['graph'], c['ast'], out / 'replayed')
    raw, profile, _ = pc.admission.fetch.cdfg.raw_binding(c['ast'], c['ast_module'])
    plan = discover(c, raw, profile, graph)
    cp = Path(store_control); cr = json.loads((cp/'report.json').read_text())
    expected, _ = control.render(c, raw, profile, plan, bool(cr.get('shallow_specialization_repair')))
    if not (cr.get('accepted') and cr.get('coqc_exit') == cr.get('coqchk_exit') == 0
            and cr.get('ast_sha256') == raw['source_sha256'] and cr.get('assumptions_closed')
            and (cp/'StoreControl.v').read_text() == expected and (cp/'StoreControl.vo').is_file()
            and hashlib.sha256(expected.encode()).hexdigest() == cr['source_sha256']
            and hashlib.sha256((cp/'StoreControl.vo').read_bytes()).hexdigest() == cr['object_sha256']):
        raise ValueError('same-source checked original store-controller provider required')
    paths = json.loads((cp/'providers.json').read_text())
    paths += [dict(namespace='GeneratedStoreControl', directory=str(cp.resolve()))]
    source, exports = render(c, raw, profile, plan); file = out/'RAMJoint.v'; file.write_text(source)
    for key, value in [('plan', plan), ('providers', paths), ('exports', exports)]:
        (out/(key+'.json')).write_text(json.dumps(value, indent=2)+'\n')
    flags = list(pc.rtl.framework.FLAGS)
    for row in paths:
        flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(out.resolve()), 'GeneratedRAMJoint']; start = time.monotonic()
    cc, timed = run_stage(['/usr/bin/time','-v','-o',str((out/'coqc.resources').resolve()),
        str(pc.rtl.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report = dict(accepted=False, coqc_exit=cc.returncode, coqc_timed_out=timed,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(), ast_sha256=raw['source_sha256'],
        graph_sha256=hashlib.sha256(Path(c['graph']).read_bytes()).hexdigest(), old_inv_read=False,
        actual_ADD_cycle_preserves_RAM_and_store_controls=False, full_R_generated=False,
        full_cycle_preservation_proved=False, itree_refinement_proved=False, external_llm_api_calls=0)
    if cc.returncode == 0:
        audit = cc.stdout.split('RAM_JOINT_AUDIT')[-1]
        closed = audit.count('Closed under the global context') == len(exports) and 'Axioms:' not in audit
        kk, timed = run_stage(['/usr/bin/time','-v','-o',str((out/'coqchk.resources').resolve()),
            str(pc.rtl.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedRAMJoint.RAMJoint'],
            out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        ok = closed and kk.returncode == 0
        report.update(accepted=ok, coqchk_exit=kk.returncode, coqchk_timed_out=timed,
            assumptions_closed=closed, actual_ADD_cycle_preserves_RAM_and_store_controls=ok)
    report['seconds'] = time.monotonic()-start
    if report['accepted']:
        report['object_sha256'] = hashlib.sha256(file.with_suffix('.vo').read_bytes()).hexdigest()
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n'); return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ['inputs', 'store-control', 'output']:
        parser.add_argument('--'+key,required=True)
    args = parser.parse_args()
    try:
        result = check(json.loads(Path(args.inputs).read_text()), args.store_control, args.output)
    except Exception as exc:
        out=Path(args.output)
        if out.is_dir() and not (out/'report.json').exists():
            (out/'report.json').write_text(json.dumps(dict(accepted=False,stage='preflight',error=str(exc),cli_exit=1),indent=2)+'\n')
        raise
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted'] else 1)
