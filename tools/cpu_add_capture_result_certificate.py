"""Join actual ADD admission/capture to the subsequent original-ISA result.

Consumes current-R RF/producer clauses, never a supplied operand-value or
control-correctness premise, and keeps the actual boot/runtime history.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_ready_rf_certificate as rf
from cpu_cdfg_result_consumer import checked_graph
from cpu_certificate_acceptance import run_stage, parse_assumptions, ALLOWED_AXIOMS


NAMESPACES = {
    'selectors': ('GeneratedReadySelector', 'ReadySelector'),
    'ready_data': ('GeneratedReadyData', 'ReadyData'),
    'ready_rf': ('GeneratedReadyRF', 'ReadyRF'),
    'capture': ('GeneratedReadyCapture', 'ReadyCapture'),
    'current_fields': ('GeneratedCurrentControlFields', 'CurrentControlFields'),
    'use': ('GeneratedHazardSourceUse', 'HazardSourceUse'),
    'reader': ('GeneratedCapturedReads', 'CapturedReadAddresses'),
    'operands': ('GeneratedResultCompanions', 'ResultCompanions'),
    'pipeline': ('GeneratedPipelineAdd', 'PipelineAdd'),
    'add_control': ('GeneratedAddControl', 'AddControl'),
    'add_result': ('GeneratedAddResult', 'AddResult'),
    'controls': ('GeneratedControlCones', 'ControlCones'),
    'control_history': ('GeneratedControlHistory', 'ControlHistory'),
    'cone': ('GeneratedCDFGResult', 'CDFGResult')
}


def verified(folder, file):
    folder = Path(folder)
    report = json.loads((folder / 'report.json').read_text())
    axioms = set(report.get('isa_assumptions', report.get('assumptions', [])))
    if not(report.get('accepted') and report.get('coqc_exit') == report.get('coqchk_exit') == 0 and
           (report.get('assumptions_closed') or report.get('assumptions_audit_passed')) and
           not(axioms - ALLOWED_AXIOMS) and
           hashlib.sha256((folder / (file + '.v')).read_bytes()).hexdigest() == report['source_sha256'] and
           (folder / (file + '.vo')).is_file()):
        raise ValueError('native checked unchanged provider required: ' + str(folder))
    return report


def render(a, raw, profile, plan):
    p, am = profile['ast']['program'], raw['module']
    sample = f'(phase_driven_state {p} ev pre)'
    post = f'(PhaseSemantics {p} ev pre)'
    source = f'''From Coq Require Import List ZArith.
Require Import {a['ast_module']} Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression
 Lang.ExtendedSVRuntimeHistory Lang.ExtendedSVRuntimeAppend Lang.ExtendedSVProjectionOrigin
 Lang.ExtendedSVCompanionField Lang.ExtendedSVCaptureBirth Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVRegisterBank Ex.External.CPUReadySlotCompaction Ex.External.CPUTwoStageReadySelection
 Ex.External.CPUReadyOperand Ex.External.CPUISAReadyBatches Ex.External.CPUISAOwnedEffects
 Ex.External.CPUOriginalISAReference Ex.External.CPURegisterEffectRelation Ex.External.CPUISARegisterUpdate
 Ex.External.CPUISAInstructionExecution Ex.External.CPUISAExecutionEffects
 Ex.RvCore.FormalSpec Ex.RvCore.Machine coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility
 GeneratedReadyCapture.ReadyCapture GeneratedPipelineAdd.PipelineAdd.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVRuntimeHistory
 ExtendedSVRuntimeAppend ExtendedSVProjectionOrigin ExtendedSVCompanionField ExtendedSVCaptureBirth
 ExtendedSVWordInvariant ExtendedSVRegisterBank CPUReadySlotCompaction CPUTwoStageReadySelection CPUReadyOperand
 CPUISAReadyBatches CPUISAOwnedEffects CPUOriginalISAReference CPURegisterEffectRelation CPUISARegisterUpdate
 CPUISAInstructionExecution CPUISAExecutionEffects.
Module N:=GeneratedReadyCapture.ReadyCapture. Module H:=N.H. Module P:=GeneratedPipelineAdd.PipelineAdd.
Local Opaque {p} PhaseSemantics.
Lemma history_one_more image events ev:
 H.boot_history image(events++[ev])=
 H.C.advance_capture_fields ev(phase_run {p} events(H.F.boot image))(H.boot_history image events)tt.
Proof. unfold H.boot_history,H.history;rewrite app_assoc,replay_one_more,phase_run_append;reflexivity. Qed.
'''
    captures = sorted(plan['captures'], key=lambda r: r['joined']['port']['field'])
    if [r['joined']['port']['field'] for r in captures] != ['Rs1', 'Rs2']:
        raise ValueError('two distinct original ADD source identities required')
    # The stage/process/reset come from the checked capture recipes and valid plan.
    valid_plan = json.loads((Path(next(x['directory'] for x in json.loads((Path(a['use']) / 'providers.json').read_text())
        if x['namespace'] == 'GeneratedValidGate')) / 'plan.json').read_text())
    valid, proc = valid_plan['valid'], valid_plan['process']
    reset = captures[0]['reset_routes'][0]['input']
    source += f'''Theorem accepted_token_is_next_stage image events ev token:
 let pre:=phase_run {p} events(H.F.boot image)in
 Forall H.W.Environment events ->H.W.Environment ev ->
 current(fst(H.boot_history image events))=Some token ->changed_signal ev<>{valid}%nat ->
 process_matches_states pre {sample}{am}.{proc}=true ->
 norm 1(read_signal {post}{valid})<>0%Z ->
 H.C.C.chain_tag0(snd(H.boot_history image(events++[ev])))=Some token.
Proof. intros pre HE HEv HT HX HM HV;rewrite history_one_more;fold pre.
 unfold H.C.advance_capture_fields,H.C.C.advance_tags;cbn[snd H.C.C.chain_tag0].
 unfold H.C.C.projection_0_origin,projection_phase_origin,H.C.C.projection_0_recipe;rewrite HM,HT.
 change((if Z.eqb(norm 1(read_signal {sample}{reset}))0%Z then None else Some token)=Some token).
 pose proof(N.active_reset image events ev HE HEv HX HM HV)as HR;fold pre in HR;rewrite HR;reflexivity. Qed.
Section OriginalISA.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{registers_ok:map.ok Registers}}.
Theorem actual_captured_add_result(token_pc:Token->Z) image events ev next_ev token rd rs1 rs2 initial batches before after:
 let pre:=phase_run {p} events(H.F.boot image)in
 Forall H.W.Environment events ->H.W.Environment ev ->H.W.Environment next_ev ->
 current(fst(H.boot_history image events))=Some token ->changed_signal ev<>{valid}%nat ->
 process_matches_states pre {sample}{am}.{proc}=true ->norm 1(read_signal {post}{valid})<>0%Z ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 instruction_effect token_pc token_word token before=Some after ->
 CertifiedBatches token_pc token_word initial batches before ->
'''
    banks = {r['joined']['port']['bank'] for r in captures}
    if len(banks) != 1:
        raise ValueError('single original physical RF relation required')
    bank = next(iter(banks))
    source += f'RegisterRelated(lane_read 32(read_signal pre {bank}))initial ->\n'
    for r in captures:
        row = r['joined']['row']
        first, second = row['binding']['first'], row['binding']['second']
        paths = {path['code']: path for path in row['paths']}
        young, old, load = [paths[c]['data']['terminal'] for c in [1, 2, 3]]
        args = (f"(N.S.bit {sample}{second['write']})(norm 5(read_signal {sample}{second['rd']}))(N.S.bit {sample}{second['load']})"
                f"(norm 32(read_signal {sample}{old}))(norm 32(read_signal {sample}{load}))"
                f"(N.S.bit {sample}{first['write']})(norm 5(read_signal {sample}{first['rd']}))(N.S.bit {sample}{first['load']})"
                f"(norm 32(read_signal {sample}{young}))")
        source += f'Forall2 SlotRelated(compact(slots {args}))(batch_writes 32(norm 5(read_signal {sample}{first["rs"]}))batches) ->\n'
    after_sample = f'(phase_driven_state {p} next_ev {post})'
    result_root = json.loads((Path(a['cone']) / 'plan.json').read_text())['root']
    source += f'''exists x y,Machine.getRegister rs1 before=(Some x,before) /\\Machine.getRegister rs2 before=(Some y,before) /\\
 norm 32(read_signal {after_sample}{result_root})=word.unsigned(Utility.add x y) /\\
 ISAProjectedRegisterEffects before after(register_operations rd(Utility.add x y)).
Proof. intros pre HE HEv HNext HT HX HM HV HD HSTEP HB HP HS0 HS1.
 destruct(token_execute token_pc token_word token before after _ HSTEP HD)as[middle[HExec HEnd]].
 destruct(original_add_effect before middle rd rs1 rs2 HExec)as[x[y[HR1[HR2 HEffect]]]].
 pose proof(N.captured_source_add_{captures[0]['joined']['row']['selector']['root']} token_pc image events ev token rd rs1 rs2 initial batches before x
 HE HEv HT HX HM HV HD HB HP HR1 HS0)as HC0;fold pre in HC0.
 pose proof(N.captured_source_add_{captures[1]['joined']['row']['selector']['root']} token_pc image events ev token rd rs1 rs2 initial batches before y
 HE HEv HT HX HM HV HD HB HP HR2 HS1)as HC1;fold pre in HC1.
 assert(HEall:Forall H.W.Environment(events++[ev]))by(apply Forall_app;split;[exact HE|constructor;[exact HEv|constructor]]).
 pose proof(accepted_token_is_next_stage image events ev token HE HEv HT HX HM HV)as HTNext.
 assert(HState:phase_run {p}(events++[ev])(H.F.boot image)={post}).
 {{ rewrite phase_run_append;reflexivity. }}
 pose proof(P.actual_pipeline_add_result token_pc image(events++[ev])next_ev token before after rd rs1 rs2
 HEall HNext HTNext HSTEP HD)as HResult.
 rewrite HState in HResult;apply HResult.
 intros x' y' HX' HY';assert(x'=x)by(congruence);assert(y'=y)by(congruence);subst x' y';split.
'''
    for r, which in zip(captures, ['HC0', 'HC1']):
        stored = r['capture']['root']
        source += f'''- rewrite(sampled_root_preserved {p} next_ev {post}{stored}
 (history_comb_frame _ _ _ _ _ N.O.scalar_{stored})(N.protected_{stored} next_ev HNext));exact {which}.
'''
    source += '''Qed.
End OriginalISA.
Goal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.
Print Assumptions history_one_more.
Print Assumptions accepted_token_is_next_stage.
Goal True. idtac "REFINEMENT_ASSUMPTIONS". exact I. Qed.
Print Assumptions actual_captured_add_result.
'''
    return source


def check(a, output):
    raw, profile, _ = rf.data.selectors.selectors.origin.raw_binding(a['ast'], a['ast_module'])
    out = Path(output)
    out.mkdir(parents=True, exist_ok=False)
    graph = checked_graph(a['graph'], a['ast'], out / 'replayed')
    reports = {key: verified(a[key], file) for key, (_, file) in NAMESPACES.items()}
    if not reports['capture'].get('actual_source_and_capture_connected'):
        raise ValueError('actual original-ISA source capture certificate required')
    plan = json.loads((Path(a['capture']) / 'plan.json').read_text())
    if plan['ast_sha256'] != raw['source_sha256']:
        raise ValueError('capture configuration mismatch')
    source = render(a, raw, profile, plan)
    file = out / 'AddCaptureResult.v'
    file.write_text(source)
    providers = json.loads((Path(a['history']) / 'plan.json').read_text())['paths']
    providers += json.loads((Path(a['use']) / 'providers.json').read_text())
    providers += [dict(directory=str(Path(a[key]).resolve()), namespace=ns) for key, (ns, _) in NAMESPACES.items()]
    providers += [dict(directory=str(out.resolve()), namespace='GeneratedAddCaptureResult')]
    (out / 'providers.json').write_text(json.dumps(providers, indent=2) + '\n')
    (out / 'inputs.json').write_text(json.dumps(a, indent=2) + '\n')
    (out / 'target.json').write_text(json.dumps(dict(ast_sha256=raw['source_sha256'],
        graph_sha256=hashlib.sha256(Path(a['graph']).read_bytes()).hexdigest(),
        source_replay_matched=True, translation_equivalence_proved=False,
        graph_nodes_bound=len(graph['symbols'])), indent=2) + '\n')
    flags = list(rf.rtl.framework.FLAGS)
    for row in providers:
        flags += ['-R', row['directory'], row['namespace']]
    start = time.monotonic()
    cc, timed = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqc.resources').resolve()),
        str(rf.data.selectors.selectors.origin.ROOT / '_opam/bin/coqc'), '-time', *flags, str(file.resolve())], out / 'coqc.log', 1200)
    report = dict(accepted=False, coqc_exit=cc.returncode, coqc_timed_out=timed,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(), complete_R_generated=False,
        reachable_RF_and_producer_relations_proved=False, global_operand_freshness_proved=False,
        operand_value_premises_eliminated=False, control_correctness_premises_eliminated=False,
        llm_calls=0, old_inv_read=False)
    if cc.returncode == 0 and time.monotonic() - start < 1200:
        tail = cc.stdout.split('ACCEPTANCE_ASSUMPTIONS')[-1].split('REFINEMENT_ASSUMPTIONS')[0]
        closed = tail.count('Closed under the global context') == 2 and 'Axioms:' not in tail
        axioms = parse_assumptions(cc.stdout, 'REFINEMENT_ASSUMPTIONS')
        audit = closed and not(axioms - set(reports['capture']['isa_assumptions'])) and not(axioms - ALLOWED_AXIOMS)
        kk, timed = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqchk.resources').resolve()),
            str(rf.data.selectors.selectors.origin.ROOT / '_opam/bin/coqchk'), '-silent', *flags, '-norec', 'GeneratedAddCaptureResult.AddCaptureResult'],
            out / 'coqchk.log', max(.1, 1200 - (time.monotonic() - start)))
        ok = audit and kk.returncode == 0
        report.update(coqchk_exit=kk.returncode, coqchk_timed_out=timed, local_assumptions_closed=closed,
            isa_assumptions=sorted(axioms), assumptions_audit_passed=audit, accepted=ok,
            operand_value_premises_eliminated=ok, control_correctness_premises_eliminated=ok)
    report['seconds'] = time.monotonic() - start
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--inputs', required=True)
    p.add_argument('--output', required=True)
    a = p.parse_args()
    try:
        r = check(json.loads(Path(a.inputs).read_text()), a.output)
    except ValueError as error:
        out = Path(a.output)
        out.mkdir(parents=True, exist_ok=True)
        r = dict(accepted=False, stage='admission_or_generation', error=str(error), complete_R_generated=False)
        if (out / 'report.json').exists():
            raise
        (out / 'report.json').write_text(json.dumps(r, indent=2) + '\n')
    print(json.dumps(r, indent=2))
    raise SystemExit(0 if r['accepted'] else 1)
