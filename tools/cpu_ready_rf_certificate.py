"""Connect actual ready muxes to zero-guarded physical RF reads.

The original ISA batch/producer relations remain explicit; this closes actual
read-port and address wiring rather than assuming physical reads are correct.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_ready_data_certificate as data
import cpu_captured_read_addresses as reads
from cpu_certificate_acceptance import run_stage, parse_assumptions, ALLOWED_AXIOMS

rtl = data.rtl


def discover(raw):
    rows = data.discover(raw)
    analysis = reads.origins.readers.analyze(raw)
    addresses, residuals, _, _ = reads.origins.discover(raw)
    if residuals:
        raise ValueError('unresolved physical RF read addresses')
    classified = []
    for row in addresses:
        layout = reads.fields.match_field(reads.strip_identity_extensions(rtl.Parser(row['expanded']).complete()), row['width'])
        if not layout or layout['field'] not in ['Rs1', 'Rs2']:
            raise ValueError('unclassified physical source address')
        classified.append(dict(row, field=layout['field']))
    ports = reads.match_read_ports(analysis, classified)
    requested = {(5, row['binding']['first']['rs']) for row in rows}
    requested.update((5, port['address']) for port in ports)
    origins, residuals, _, _ = reads.origins.discover(raw, requested)
    if residuals:
        raise ValueError('unresolved selector/RF source identity')
    by_root = {}
    for row in origins:
        field = reads.fields.match_field(reads.strip_identity_extensions(rtl.Parser(row['expanded']).complete()), row['width'])
        if not field or field['source'] != row['source']:
            raise ValueError('source identity does not have a checked instruction layout')
        by_root[row['root']] = dict(row, field=field['field'])
    joined = []
    for row in rows:
        fallback = next(p for p in row['paths'] if p['code'] == 0)
        matches = [p for p in ports if p['output'] == fallback['data']['terminal']]
        if len(matches) != 1:
            raise ValueError('fallback does not select a unique physical RF read')
        port = matches[0]
        actual, index = by_root[row['binding']['first']['rs']], by_root[port['address']]
        if (actual['source'], actual['field']) != (index['source'], index['field']):
            raise ValueError('selector/RF read identity mismatch')
        joined.append(dict(row=row, port=port))
    return dict(rows=joined, addresses=list(by_root.values())), analysis


def render(a, raw, profile, plan, analysis):
    p = profile['ast']['program']
    requested = {(r['width'], r['root']) for r in plan['addresses']}
    addr, text, _, _ = reads.origins.render(a.ast, a.ast_module, requested)
    if addr['residuals'] or text is None:
        raise ValueError('address proof generator has unresolved obligations')
    source = 'Module A.\n' + text + '\nEnd A.\n'
    source += 'Module B.\n' + reads.origins.readers.render(profile['ast'], raw, analysis) + '\nEnd B.\n'
    source += f'''From Coq Require Import ZArith List Lia.
Require Import {a.ast_module} Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVBankAlignment
 Lang.ExtendedSVZeroGuardedRead Lang.ExtendedSVRegisterBank Ex.External.CPUInstructionFields
 Ex.External.CPUTwoStageReadySelection Ex.External.CPUISAReadyBatches Ex.External.CPUISAOwnedEffects
 Ex.External.CPUReadyOperand Ex.External.CPURegisterEffectRelation Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 GeneratedReadySelector.ReadySelector GeneratedReadyData.ReadyData.
Import ListNotations ExtendedSV ExtendedSVWordInvariant CPUInstructionFields ExtendedSVBankAlignment ExtendedSVRegisterBank
 CPUTwoStageReadySelection CPUReadyOperand CPUISAReadyBatches CPUISAOwnedEffects CPURegisterEffectRelation.
Module D:=GeneratedReadyData.ReadyData. Module S:=GeneratedReadySelector.ReadySelector.
Local Opaque {p}.
'''
    exports = []
    for row in plan['addresses']:
        x, w, carrier, field = row['root'], row['width'], row['source'], row['field']
        source += f'''Lemma field_{x}_layout code:A.address_{x}_reference code=field_reference code {field}.
Proof. let e:=eval cbv in A.address_{x}_expanded in
 change(norm {w}(eval_expr(write_signal [] {carrier} code)e)=field_reference code {field}).
 pose proof(native_field_reference(write_signal [] {carrier} code){carrier} {field})as HF.
 unfold field_expr in HF;cbn[field_width field_offset eval_expr]in HF.
 cbn[eval_expr];repeat rewrite norm_idempotent in *;rewrite read_signal_write_same in *;exact HF. Qed.
Theorem field_{x}_at_lfp seed fixed:CombLFP {p} seed fixed ->
 norm {w}(read_signal fixed {x})=field_reference(read_signal fixed {carrier}){field}.
Proof. intro HL;exact(eq_trans(A.address_{x}_instruction seed fixed (read_signal fixed {carrier})HL eq_refl)
 (field_{x}_layout _)). Qed.
'''
        exports += [f'field_{x}_at_lfp']
    for joined in plan['rows']:
        row, port = joined['row'], joined['port']
        sr = row['selector']['root']
        first, second = row['binding']['first'], row['binding']['second']
        by_code = {p['code']: p for p in row['paths']}
        bank, total, root, address = port['bank'], port['total'], port['output'], port['address']
        index = first['rs']
        source += f'''Definition physical_{sr} fixed:=ExtendedSVZeroGuardedRead.value(read_signal fixed {bank}).
Lemma physical_{sr}_zero fixed:physical_{sr} fixed 0%Z=0%Z.
Proof. reflexivity. Qed.
Theorem physical_read_{sr} seed fixed:CombLFP {p} seed fixed ->
 physical_{sr} fixed(norm 5(read_signal fixed {index}))=norm 32(read_signal fixed {root}).
Proof. intro HL;rewrite(B.port_{port['port']}_lfp seed fixed HL).
 change(physical_{sr} fixed(norm 5(read_signal fixed {index}))=
 norm 32(eval_expr fixed(ExtendedSVZeroGuardedRead.expression {total} {bank} {address}))).
 rewrite(ExtendedSVZeroGuardedRead.read_value {total} {bank} {address} fixed ltac:(lia)).
 unfold physical_{sr};pose proof(eq_trans(field_{address}_at_lfp seed fixed HL)
 (eq_sym(field_{index}_at_lfp seed fixed HL)))as HA;now rewrite HA. Qed.
'''
        young, old, load = [by_code[c]['data']['terminal'] for c in [1, 2, 3]]
        args = (f"(S.bit fixed {second['write']}%nat)(norm 5(read_signal fixed {second['rd']}%nat))(S.bit fixed {second['load']}%nat)"
                f"(norm 32(read_signal fixed {old}%nat))(norm 32(read_signal fixed {load}%nat))"
                f"(S.bit fixed {first['write']}%nat)(norm 5(read_signal fixed {first['rd']}%nat))(S.bit fixed {first['load']}%nat)"
                f"(norm 32(read_signal fixed {young}%nat))")
        addr = f'(norm 5(read_signal fixed {index}%nat))'
        admitted = (f"(eligible(S.bit fixed {first['write']}%nat)(norm 5(read_signal fixed {first['rd']}%nat)){addr}"
                    f" && S.bit fixed {first['load']}%nat)%bool=false")
        output = by_code[0]['output']
        source += f'''Theorem actual_physical_ready_{sr} seed fixed:CombLFP {p} seed fixed ->
 {admitted} ->
 resolve 0%Z(physical_{sr} fixed){addr}(slots {args})=Some(norm 32(read_signal fixed {output})).
Proof. intros HL HA;exact(D.actual_ready_resolution_{sr} seed fixed _ HL
 (physical_read_{sr} seed fixed HL)(physical_{sr}_zero fixed)HA). Qed.
Section ISA_{sr}.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{Token:Type}}.
Lemma physical_{sr}_related fixed initial:
 RegisterRelated(lane_read 32(read_signal fixed {bank}))initial ->RegisterRelated(physical_{sr} fixed)initial.
Proof. intros HR i HI;specialize(HR i HI).
 change((if Z.eqb i 0%Z then 0%Z else physical_{sr} fixed i)=ISAView initial i).
 change((if Z.eqb i 0%Z then 0%Z else lane_read 32(read_signal fixed {bank})i)=ISAView initial i)in HR.
 change((if Z.eqb i 0%Z then 0%Z else if Z.eqb i 0%Z then 0%Z
 else lane_read 32(read_signal fixed {bank})i)=ISAView initial i).
 destruct(Z.eqb i 0%Z);exact HR. Qed.
Theorem actual_source_matches_original_read_{sr} (token_pc token_word:Token->Z)
 seed fixed initial batches before after value:
 CombLFP {p} seed fixed ->CertifiedBatches token_pc token_word initial batches before ->
 RegisterRelated(lane_read 32(read_signal fixed {bank}))initial ->
 Machine.getRegister {addr} before=(Some value,after) ->
 Forall2 SlotRelated(slots {args})(batch_writes 32 {addr} batches) ->{admitted} ->
 norm 32(read_signal fixed {output})=word.unsigned value.
Proof. intros HL HB HP HR HS HA.
 pose proof(norm_bounds 5(read_signal fixed {index}))as Hbounds.
 change((0<={addr}<32)%Z)in Hbounds.
 exact(D.actual_operand_matches_original_read_{sr} token_pc token_word seed fixed _ initial batches before after value
 HL(physical_read_{sr} seed fixed HL)HB(physical_{sr}_related fixed initial HP)Hbounds HR HS(physical_{sr}_zero fixed)HA). Qed.
End ISA_{sr}.
'''
        exports += [f'physical_read_{sr}', f'actual_physical_ready_{sr}']
    source += 'Goal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\n'
    source += ''.join(f'Print Assumptions {name}.\n' for name in exports)
    source += 'Goal True. idtac "REFINEMENT_ASSUMPTIONS". exact I. Qed.\n'
    source += ''.join(f'Print Assumptions actual_source_matches_original_read_{r["row"]["selector"]["root"]}.\n' for r in plan['rows'])
    return source, len(exports)


def check(a):
    raw, profile, paths = data.selectors.selectors.origin.raw_binding(a.ast, a.ast_module)
    provider = Path(a.data)
    report = json.loads((provider / 'report.json').read_text())
    if not(report.get('accepted') and report.get('coqc_exit') == report.get('coqchk_exit') == 0 and
           report.get('assumptions_audit_passed') and report['ast_sha256'] == raw['source_sha256'] and
           hashlib.sha256((provider / 'ReadyData.v').read_bytes()).hexdigest() == report['source_sha256'] and
           (provider / 'ReadyData.vo').is_file() and not(set(report['isa_assumptions']) - ALLOWED_AXIOMS)):
        raise ValueError('checked same-configuration ready data provider required')
    data.verified(a.selectors, 'ReadySelector')
    plan, analysis = discover(raw)
    source, count = render(a, raw, profile, plan, analysis)
    out = Path(a.output)
    out.mkdir(parents=True, exist_ok=False)
    file = out / 'ReadyRF.v'
    file.write_text(source)
    (out / 'plan.json').write_text(json.dumps(dict(plan, ast_sha256=raw['source_sha256']), indent=2) + '\n')
    flags = list(rtl.framework.FLAGS)
    for path in paths:
        flags += ['-R', path['directory'], path['namespace']]
    for folder, ns in [(a.data, 'GeneratedReadyData'), (a.selectors, 'GeneratedReadySelector'), (out, 'GeneratedReadyRF')]:
        flags += ['-R', str(Path(folder).resolve()), ns]
    start = time.monotonic()
    cc, timed = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqc.resources').resolve()),
        str(data.selectors.selectors.origin.ROOT / '_opam/bin/coqc'), '-time', *flags, str(file.resolve())], out / 'coqc.log', 1200)
    result = dict(accepted=False, coqc_exit=cc.returncode, coqc_timed_out=timed,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(), complete_R_generated=False,
        operand_freshness_proved=False, physical_read_wiring_proved=False, old_inv_read=False, llm_calls=0)
    if cc.returncode == 0 and time.monotonic() - start < 1200:
        tail = cc.stdout.split('ACCEPTANCE_ASSUMPTIONS')[-1].split('REFINEMENT_ASSUMPTIONS')[0]
        closed = tail.count('Closed under the global context') == count and 'Axioms:' not in tail
        axioms = parse_assumptions(cc.stdout, 'REFINEMENT_ASSUMPTIONS')
        audit = closed and not(axioms - set(report['baseline_assumptions'])) and not(axioms - ALLOWED_AXIOMS)
        kk, timed = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqchk.resources').resolve()),
            str(data.selectors.selectors.origin.ROOT / '_opam/bin/coqchk'), '-silent', *flags, '-norec', 'GeneratedReadyRF.ReadyRF'],
            out / 'coqchk.log', max(.1, 1200 - (time.monotonic() - start)))
        result.update(coqchk_exit=kk.returncode, coqchk_timed_out=timed, local_assumptions_closed=closed,
            isa_assumptions=sorted(axioms), assumptions_audit_passed=audit,
            accepted=audit and kk.returncode == 0, physical_read_wiring_proved=audit and kk.returncode == 0)
    result['seconds'] = time.monotonic() - start
    (out / 'report.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    for key in ['ast', 'ast-module', 'selectors', 'data', 'output']:
        p.add_argument('--' + key, required=True)
    a = p.parse_args()
    r = check(a)
    print(json.dumps(r, indent=2))
    raise SystemExit(0 if r['accepted'] else 1)
