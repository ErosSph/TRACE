"""Consume the actual admission certificate in a reset/runtime write invariant.

Selection restricts only the data assertion to ADD. It does not remove any
physical valid slot, original token, queue entry or coverage obligation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_add_admission_write as admission
import cpu_result_companions as companions
from cpu_certificate_acceptance import run_stage

rtl = admission.rtl


def discover(raw, admission_plan, covered):
    fields = covered['coverage']['covered_fields']
    scalars = admission.observation.origin.pending.analyze(raw)['scalar_transitions']
    rows = []
    root = admission_plan['write']
    for index, field in enumerate(fields):
        candidates = []
        for scalar in scalars:
            if scalar['width'] != 1 or scalar['process'] != field['process']:
                continue
            match = companions.match(rtl.Parser(scalar['next_expression']).complete(),
                companions.companion.RecipeParser(field['recipe']).complete(), 1, scalar['root'])
            if not match or len(set(match[0])) != 1 or match[0][0].name != 'EVar':
                continue
            incoming = int(match[0][0].args[1].name)
            route = admission.wires.trace(raw, 1, incoming)
            if (index == 0 and scalar['root'] == root) or (index > 0 and route['terminal'] == root):
                candidates.append(dict(scalar, stage=index, valid=field['valid_root'],
                    input_valid=field['source_valid'], recipe=field['recipe'],
                    capture=rtl.render(match[0][0]), proof=match[1], route=route))
        if len(candidates) != 1:
            raise ValueError('no unique actual write predecessor at stage ' + str(index))
        rows += candidates
        root = candidates[0]['root']
    if len(rows) != 3 or rows[0]['root'] != admission_plan['write']:
        raise ValueError('current template needs three actual ordered write stages')
    return dict(rows=rows, ast_sha256=raw['source_sha256'])


def render(config, raw, profile, plan, admission_plan):
    p, am = profile['ast']['program'], raw['module']
    rows = plan['rows']
    carrier = admission_plan['fields'][0]['source']
    profile['coq_load_paths'] = json.loads((Path(config['history']) / 'plan.json').read_text())['paths']
    _, residuals, _, scalar_source, _ = admission.observation.origin.expressions.proposal(profile, {r['root'] for r in rows})
    if residuals:
        raise ValueError('actual write expressions have unsupported structure')
    roots = {e['root'] for r in rows[1:] for e in r['route']['edges']}
    _, wp, ws = admission.comb.proposal(profile, roots)
    if wp['residuals']:
        raise ValueError('write transfer aliases have unresolved obligations')
    ports = {r['output_root']: i for i, r in enumerate(wp['ports'])}
    source = 'Module Scalar.\n' + scalar_source + '\nEnd Scalar.\nModule WriteWires.\n' + ws + '\nEnd WriteWires.\n'
    source += f'''From Coq Require Import List ZArith Bool.
Require Import {config['ast_module']} Lang.ExtendedSV Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVScalarExpression Lang.ExtendedSVWordInvariant Lang.ExtendedSVProjectionOrigin
 Lang.ExtendedSVCompanionField Lang.ExtendedSVValidCompanion Lang.ExtendedSVSelectedCompanion
 Lang.ExtendedSVProjectionConnection Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPC
 Lang.ExtendedSVRuntimeHistory Lang.ExtendedSVBoundedCatalogPhase
 GeneratedAdmissionWrite.AdmissionWrite GeneratedCapturedHistoryBoot.CapturedHistoryBoot
 Ex.External.CPUISAAddControlFields.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVWordInvariant
 ExtendedSVProjectionOrigin ExtendedSVCompanionField ExtendedSVValidCompanion ExtendedSVSelectedCompanion
 ExtendedSVProjectionConnection ExtendedSVCaptureBirth ExtendedSVCapturedPC ExtendedSVRuntimeHistory
 ExtendedSVBoundedCatalogPhase.
Module Runtime:=GeneratedCapturedHistoryBoot.CapturedHistoryBoot.
Module Covered:=Runtime.C.
Local Opaque {p} PhaseSemantics.
Definition is_add(token:Token):bool:=match Decode.decode Decode.RV32I(token_word token)with
 |Decode.IInstruction(Decode.Add _ _ _)=>true|_=>false end.
Lemma is_add_decode token:is_add token=true ->exists rd rs1 rs2,
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2).
Proof. unfold is_add;destruct(Decode.decode Decode.RV32I(token_word token))eqn:HD;
 try discriminate;match goal with instruction:Decode.InstructionI |- _=>destruct instruction end;
 try discriminate;intro H;eauto. Qed.
Definition write_reference(_:Token):option Z:=Some 1%Z.
'''
    protected = sorted({carrier} | {r[k] for r in rows for k in ['root', 'valid', 'input_valid']})
    source += 'Lemma protect ev root:Runtime.W.Environment ev ->In root [' + ';'.join(str(x) + '%nat' for x in protected) + '] ->changed_signal ev<>root.\n'
    source += '''Proof. intros[_ HE]HI;unfold Runtime.W.ExternalEvent in HE;apply existsb_exists in HE;
 destruct HE as[x[HX HE]];apply Nat.eqb_eq in HE;rewrite HE;unfold Runtime.W.external_roots in HX;
 cbn in HX,HI;repeat destruct HX as[<-|HX];try contradiction;
 repeat destruct HI as[<-|HI];try contradiction;discriminate. Qed.
'''
    sample, post = f'(phase_driven_state {p} ev pre)', f'(PhaseSemantics {p} ev pre)'
    for r in rows:
        x, k = r['root'], r['stage']
        source += f'''Lemma self_{x}:self_widthb 1 {x} Scalar.root_{x}_expression=true.
Proof. vm_compute;reflexivity. Qed.
Definition scalar_{x}:ScalarCertificate {p} {x} 1 {am}.{r['process']} Scalar.root_{x}_expression:=
 Build_ScalarCertificate _ _ _ _ _ Scalar.root_{x}_comb_frame self_{x} Scalar.root_{x}_expression_phase.
Lemma match_{x}:RecipeMatches 1 {x} {r['capture']} Scalar.root_{x}_expression Covered.C.projection_{k}_recipe.
Proof. unfold Scalar.root_{x}_expression,Covered.C.projection_{k}_recipe. {r['proof']} Qed.
'''
    head = rows[0]
    x, vr = head['root'], head['valid']
    source += f'''Theorem head_phase seed ev pre packed:
 Runtime.W.Environment ev ->CombLFP {p} seed {sample} ->Covered.CoveredCapturedFields pre packed ->
 SelectedValidField is_add write_reference 1 {x} {vr} pre(Covered.C.chain_tag0(snd packed)) ->
 SelectedValidField is_add write_reference 1 {x} {vr} {post}
 (Covered.C.chain_tag0(snd(Covered.advance_capture_fields ev pre packed tt))).
Proof. intros HE HL HC HO token HT HSelected HV.
 cbn[Covered.advance_capture_fields snd Covered.C.advance_tags Covered.C.chain_tag0]in HT.
 unfold Covered.C.projection_0_origin,projection_phase_origin in HT.
 destruct(process_matches_states pre {sample}{am}.{head['process']})eqn:HM.
 - pose proof(GeneratedAdmissionWrite.AdmissionWrite.actual_capture_reset ev pre
    (protect ev {vr} HE ltac:(simpl;tauto))HM HV)as HR.
   change((if Z.eqb(norm 1(read_signal {sample}{admission_plan['reset']}))0%Z then None
     else current(fst packed))=Some token)in HT.
   rewrite HR in HT;cbn in HT.
   destruct(is_add_decode token HSelected)as[rd[rs1[rs2 HD]]].
   assert(HWord:norm 32(read_signal {sample}{carrier})=norm 32(token_word token)).
   {{ rewrite(sampled_root_preserved {p} ev pre {carrier} Covered.B.root_{carrier}_comb_frame
       (protect ev {carrier} HE ltac:(simpl;tauto))).
      destruct(proj1(proj1(proj1 HC)))as[HCoverage HValue];exact(HValue token HT). }}
   unfold write_reference;f_equal;symmetry.
   exact(GeneratedAdmissionWrite.AdmissionWrite.actual_add_capture_write seed ev pre(token_word token)rd rs1 rs2
     HL(protect ev {vr} HE ltac:(simpl;tauto))(protect ev {x} HE ltac:(simpl;tauto))HM HV HWord HD).
 - rewrite(history_phase_projection _ _ _ _ _ Covered.V.root_{vr}_valid_certificate ev pre
      (protect ev {vr} HE ltac:(simpl;tauto))),HM in HV.
   rewrite(history_phase_projection _ _ _ _ _ scalar_{x} ev pre
      (protect ev {x} HE ltac:(simpl;tauto))),HM.
   exact(HO token HT HSelected HV).
Qed.
'''
    for row in rows[1:]:
        x, vr, iv, k = row['root'], row['valid'], row['input_valid'], row['stage']
        parent = row['route']['terminal']
        source += f'''Lemma expanded_{vr} seed sample:CombLFP {p} seed sample ->
 norm 1(eval_expr sample Covered.V.root_{vr}_expression)=norm 1(eval_expr sample Covered.V.coverage_{k}_expanded).
Proof. intro HL;pose proof(bindings_substitute_sound Covered.V.coverage_{k}_bindings Covered.V.root_{vr}_expression sample
 (Covered.V.coverage_{k}_bindings_agree seed sample HL))as HX;
 rewrite Covered.V.coverage_{k}_expansion_checked in HX;exact(f_equal(norm 1)(eq_sym HX)). Qed.
Theorem transfer_{x} seed ev pre old incoming:
 Runtime.W.Environment ev ->CombLFP {p} seed {sample} ->
 SelectedValidField is_add write_reference 1 {x} {vr} pre old ->
 SelectedValidField is_add write_reference 1 {parent} {iv} pre incoming ->
 SelectedValidField is_add write_reference 1 {x} {vr} {post}
 (projection_phase_origin {p} {am}.{row['process']} Covered.C.projection_{k}_recipe ev pre old incoming).
Proof. intros HE HL HO HI.
 eapply actual_selected_valid_expression_phase;[exact scalar_{x}|exact Covered.V.root_{vr}_valid_certificate|
 exact match_{x}|exact Covered.V.coverage_{k}_checked|
 exact(protect ev {x} HE ltac:(simpl;tauto))|exact(protect ev {vr} HE ltac:(simpl;tauto))|
 exact(expanded_{vr} seed _ HL)|exact HO|].
 intros HV token HT HS.
 rewrite(sampled_root_preserved {p} ev pre {iv} Covered.V.root_{iv}_comb_frame
  (protect ev {iv} HE ltac:(simpl;tauto)))in HV.
 cbn[eval_expr];rewrite norm_idempotent.
'''
        for edge in row['route']['edges']:
            i = ports[edge['root']]
            source += f'rewrite(WriteWires.port_{i}_lfp seed _ HL);unfold WriteWires.port_{i}_rhs;cbn[eval_expr];rewrite norm_idempotent.\n'
        source += f'''rewrite(sampled_root_preserved {p} ev pre {parent}(history_comb_frame _ _ _ _ _ scalar_{parent})
 (protect ev {parent} HE ltac:(simpl;tauto))).
 exact(HI token HT HS HV). Qed.
'''
    source += 'Definition Joint pre(packed:Covered.Packed):Prop:=Covered.CoveredCapturedFields pre packed /\\\n' + ' /\\\n'.join(
        f"SelectedValidField is_add write_reference 1 {r['root']} {r['valid']} pre(Covered.C.chain_tag{r['stage']}(snd packed))" for r in rows) + '.\n'
    source += f'''Theorem actual_phase seed ev pre packed:
 Runtime.W.Environment ev ->CombLFP {p} seed {sample} ->Joint pre packed ->
 Joint {post}(Covered.advance_capture_fields ev pre packed tt).
Proof. intros HE HL[HC[H0[H1 H2]]];split.
 - exact(Covered.covered_capture_step ev pre packed tt HC(Runtime.boundary seed ev pre HE HL)).
 - split;[exact(head_phase seed ev pre packed HE HL HC H0)|];split.
   + cbn[Covered.advance_capture_fields snd Covered.C.advance_tags Covered.C.chain_tag1].
     exact(transfer_{rows[1]['root']} seed ev pre _ _ HE HL H1 H0).
   + cbn[Covered.advance_capture_fields snd Covered.C.advance_tags Covered.C.chain_tag2].
     exact(transfer_{rows[2]['root']} seed ev pre _ _ HE HL H2 H1).
Qed.
Theorem seed_joint image:Joint(Runtime.F.seed image)Runtime.empty.
Proof. split;[exact(Runtime.seed_covered image)|];unfold Runtime.empty;cbn;
 repeat split;intros token HT;discriminate. Qed.
Theorem runtime events:Forall Runtime.W.Environment events ->forall pre packed,
 CatalogShape {p} Catalog.actual_catalog pre ->Joint pre packed ->
 Joint(phase_run {p} events pre)(Runtime.history events pre packed).
Proof. exact(checked_history {p} Catalog.actual_catalog Phase.actual_certificate Covered.Packed
 Covered.advance_capture_fields Joint Runtime.W.Environment(fun ev HE=>proj1 HE)actual_phase events). Qed.
Theorem reset_reachable_add_write_controls image events:Forall Runtime.W.Environment events ->
 Joint(phase_run {p} events(Runtime.F.boot image))(Runtime.boot_history image events).
Proof. intro HE;assert(HA:Forall Runtime.W.Environment(Runtime.F.boot_events++events))
 by(apply Forall_app;split;[exact Runtime.W.boot_environment|exact HE]).
 pose proof(runtime _ HA(Runtime.F.seed image)Runtime.empty(Runtime.B.seed_shape image)(seed_joint image))as HR.
 rewrite phase_run_append in HR;exact HR. Qed.
Goal True. idtac "ADD_WRITE_HISTORY_AUDIT". exact I. Qed.
Print Assumptions head_phase. Print Assumptions transfer_{rows[1]['root']}.
Print Assumptions transfer_{rows[2]['root']}. Print Assumptions actual_phase.
Print Assumptions seed_joint. Print Assumptions runtime.
Print Assumptions reset_reachable_add_write_controls.
'''
    return source


def check(config, provider, output):
    out = Path(output)
    out.mkdir(parents=True, exist_ok=False)
    raw, profile, _ = admission.observation.origin.raw_binding(config['ast'], config['ast_module'])
    ap = admission.checked(provider, 'AdmissionWrite', raw['source_sha256'])
    if 'fields' not in ap or ap.get('proof_count') != 7:
        raise ValueError('actual generic capture consumer is required')
    paths = json.loads((Path(provider) / 'providers.json').read_text())
    environment_hashes = admission.verify_environment_paths(paths)
    covered = next(r['directory'] for r in paths if r['namespace'] == 'GeneratedCoveredCapture')
    coverage = json.loads((Path(covered) / 'plan.json').read_text())
    plan = discover(raw, ap, coverage)
    graph = admission.checked_graph(config['graph'], config['ast'], out / 'replayed')
    evidence = companions.capture_graph_evidence(graph, raw, plan['rows'])
    (out / 'graph-evidence.json').write_text(json.dumps(evidence, indent=2) + '\n')
    source = render(config, raw, profile, plan, ap)
    path = out / 'AddWriteHistory.v'
    path.write_text(source)
    (out / 'plan.json').write_text(json.dumps(plan, indent=2) + '\n')
    paths += [dict(directory=str(Path(provider).resolve()), namespace='GeneratedAdmissionWrite')]
    (out / 'providers.json').write_text(json.dumps(paths, indent=2) + '\n')
    flags = list(rtl.framework.FLAGS)
    for row in paths:
        flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(out.resolve()), 'GeneratedAddWriteHistory']
    start = time.monotonic()
    c, timed = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqc.resources').resolve()),
        str(admission.observation.origin.ROOT / '_opam/bin/coqc'), '-time', *flags, str(path.resolve())], out / 'coqc.log', 1200)
    report = dict(accepted=False, coqc_exit=c.returncode, coqc_timed_out=timed, old_inv_read=False,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(), ast_sha256=raw['source_sha256'],
        complete_R_generated=False, infinite_itree_refinement_proved=False,
        reset_reachable_add_write_controls_proved=False, llm_calls=0,
        original_environment_input_hashes=environment_hashes)
    if c.returncode == 0:
        tail = c.stdout.split('ADD_WRITE_HISTORY_AUDIT')[-1]
        closed = tail.count('Closed under the global context') == 7 and 'Axioms:' not in tail
        k, timed = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqchk.resources').resolve()),
            str(admission.observation.origin.ROOT / '_opam/bin/coqchk'), '-silent', *flags, '-norec',
            'GeneratedAddWriteHistory.AddWriteHistory'], out / 'coqchk.log', max(.1, 1200-(time.monotonic()-start)))
        report.update(coqchk_exit=k.returncode, coqchk_timed_out=timed, assumptions_closed=closed,
            accepted=closed and k.returncode == 0, reset_reachable_add_write_controls_proved=closed and k.returncode == 0)
    report['seconds'] = time.monotonic()-start
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for x in ['inputs', 'provider', 'output']:
        parser.add_argument('--'+x, required=True)
    args = parser.parse_args()
    try:
        result = check(json.loads(Path(args.inputs).read_text()), args.provider, args.output)
    except Exception as error:
        directory = Path(args.output)
        if directory.is_dir() and not(directory / 'report.json').exists():
            (directory / 'report.json').write_text(json.dumps(dict(accepted=False, stage='preflight',
                error_type=type(error).__name__, error=str(error), cli_exit=1,
                complete_R_generated=False, infinite_itree_refinement_proved=False), indent=2) + '\n')
        raise
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['accepted'] else 1)
