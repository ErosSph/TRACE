"""Extend the ORIGINAL ISA chain with the actual phase's newly captured ADD.

Present-state frontier PC, memory and address domain are explicit R obligations.
No caller-supplied effect/run1 success or future execution trace is accepted.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_cdfg_fetch_reference as fetch
import cpu_add_admission_queue as queue
from cpu_certificate_acceptance import run_stage, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports


def discover(c, raw, profile, graph):
    plan = fetch.discover(raw, graph)
    pair = plan['pair']; pc = pair['address_alias_chain']['terminal']
    captures = fetch.rom.pc.provenance.hb.coverage.capture.birth.discover(raw)['captures']
    matched = [row for row in captures if row['carrier'] == pair['carrier']]
    if len(matched) != 1:
        raise ValueError('unique original capture/validity pair required')
    pair['valid_root'] = matched[0]['valid_root']
    if pair['pc_alias_chain']['terminal'] != pc:
        raise ValueError('captured PC and ROM address do not share a state boundary')
    writers = [p for p in raw['processes'] if pc in p['writers']]
    if len(writers) != 1 or writers[0]['kind'] != 'Sequential':
        raise ValueError('frontier query needs a unique actual sequential PC boundary')
    chains = [pair[k] for k in ['pc_alias_chain', 'address_alias_chain']] + [pair['reader']['alias_chain']]
    roots = {edge['root'] for chain in chains for edge in chain['edges']} | {pair['reader']['terminal']}
    _, wires, _ = fetch.rom.pc.fetch.rom.comb.proposal(profile, roots)
    if wires['residuals']:
        raise ValueError('original fetch wiring has unresolved physical obligations')
    plan.update(pc_state_root=pc, alias_ports={str(r['output_root']): i for i, r in enumerate(wires['ports'])})
    return plan


def render(c, raw, profile, plan):
    p, am = profile['ast']['program'], raw['module']; pair = plan['pair']
    pc, addr, root, word_input = plan['pc_state_root'], pair['address_root'], pair['carrier'], pair['word_input']
    q = 'GeneratedAdmissionQueue.AdmissionQueue'
    h = 'GeneratedCapturedHistoryBoot.CapturedHistoryBoot'
    cap = h + '.C'; birth = q + '.N.B'
    r = 'GeneratedFetchReference.FetchReference'
    proc = am + '.' + pair['process']
    word = f'{birth}.root_{root}_expression'; valid = f'{birth}.root_{pair["valid_root"]}_expression'
    sample = f'(phase_driven_state {p} ev pre)'
    decision = f'(phase_decision {p} {proc} {root} {word} {valid} ev pre)'
    packed = f'({h}.boot_history image events)'
    pre = f'(phase_run {p} events({h}.F.boot image))'
    alias = fetch.rom.pc.fetch.alias_term(pair['address_alias_chain'], {int(k):v for k,v in plan['alias_ports'].items()})
    alias = re.sub(r'\b(port_\d+_lfp)\b', r'GeneratedFetchPairs.FetchPairs.\1', alias)
    capacity, offset = plan['capacity'], plan['offset_width']
    text = f'''From Coq Require Import List ZArith Bool Lia.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVRootProjection Lang.ExtendedSVRuntimeHistory Lang.ExtendedSVRuntimeAppend Lang.ExtendedSVScalarExpression
 Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPending Lang.ExtendedSVPackedROM Lang.ExtendedSVInstructionOrigin Lang.ExtendedSVCaptureRead
 Ex.External.CPUGeneratedJointTemplate Ex.External.CPUOriginalISAReference Ex.External.CPUProgramROM
 Ex.RvCore.FormalSpec coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 GeneratedAdmissionQueue.AdmissionQueue GeneratedFetchReference.FetchReference.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVWordInvariant ExtendedSVRootProjection
 ExtendedSVRuntimeHistory ExtendedSVRuntimeAppend ExtendedSVCaptureBirth ExtendedSVCapturedPending ExtendedSVInstructionOrigin
 ExtendedSVScalarExpression ExtendedSVCaptureRead CPUGeneratedJointTemplate.
Lemma pc_comb_frame:comb_root_unwrittenb {p} {pc}=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque {p} PhaseSemantics.
Lemma address_at_pc_boundary seed fixed:CombLFP {p} seed fixed ->
 norm 32(read_signal fixed {addr})=norm 32(read_signal fixed {pc}).
Proof. intro HL;exact {alias}. Qed.
Lemma sampled_address_at_current_pc seed ev pre:
 {h}.W.Environment ev ->CombLFP {p} seed {sample} ->
 norm 32(read_signal {sample}{addr})=norm 32(read_signal pre {pc}).
Proof. intros HE HL;exact(eq_trans(address_at_pc_boundary seed _ HL)
 (f_equal(norm 32)(sampled_root_preserved {p} ev pre {pc} pc_comb_frame
 ({q}.internal_event ev {pc} HE ltac:(lia))))). Qed.
Lemma boot_history_one_more image events ev:
 {h}.boot_history image(events++[ev])=
 {cap}.advance_capture_fields ev {pre} {packed} tt.
Proof. unfold {h}.boot_history,{h}.history.
 rewrite app_assoc,replay_one_more,phase_run_append;reflexivity. Qed.
Lemma admitted_as_births ev pre(packed:{cap}.Packed):
 {q}.admitted ev pre packed=NewTokens {decision}(serial(fst packed)){sample} {birth}.capture_0_pc.
Proof. destruct packed as[g tags];destruct tags;reflexivity. Qed.
Lemma actual_accept_source ev pre source:
 {decision}=Accept source ->source={word_input}%nat.
Proof. intro HD;destruct(phase_accept_copy {p} {proc} {root} {word} {valid} ev pre source HD)as[HC HN].
 unfold {word} in HC;cbn[copy_source]in HC;
 repeat match type of HC with context[if ?test then _ else _]=>destruct test end;
 try discriminate;inversion HC;subst;try contradiction;reflexivity. Qed.
Lemma admitted_pc ev pre(packed:{cap}.Packed)token:
 In token({q}.admitted ev pre packed) ->token_pc token=Some(norm 32(read_signal {sample}{addr})).
Proof. rewrite admitted_as_births;destruct {decision}as[| |source]eqn:HD;
 cbn[NewTokens birth];try contradiction;intros[HT|HF];[|contradiction];subst token.
 pose proof(actual_accept_source ev pre source HD)as HS;subst source.
 unfold fresh,{birth}.capture_0_pc;cbn[token_pc];rewrite Nat.eqb_refl;reflexivity. Qed.
Lemma admitted_recorded_after image events ev token:
 In token({q}.admitted ev {pre} {packed}) ->
 In token(history(fst({h}.boot_history image(events++[ev])))).
Proof. intro HI;rewrite boot_history_one_more.
 pose proof({q}.N.J.pending_admissions_recorded ev {pre}({q}.repack {packed}))as HA.
 apply Forall_forall with(x:=token)in HA;[|exact HI].
 rewrite<-({q}.repack_step ev {pre} {packed})in HA;exact HA. Qed.
Lemma admitted_empty_or_one ev pre(packed:{cap}.Packed):
 {q}.admitted ev pre packed=[] \\/exists token,{q}.admitted ev pre packed=[token].
Proof. rewrite admitted_as_births;destruct {decision};cbn[NewTokens birth];[now left|now left|right;eexists;reflexivity]. Qed.
Section OriginalISA.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{registers_ok:map.ok Registers}}{{mem_ok:map.ok Mem}}.
Local Open Scope Z_scope.
Definition FrontierAt pre(frontier:FormalSpec.State)i words:=
 norm 32(read_signal pre {pc}%nat)=word.unsigned(getPc frontier) /\\
 word.unsigned(getPc frontier)=4*Z.of_nat i /\\
 getInstMem frontier=FormalSpec.formal_initial_imem(CPUProgramROM.entries words).
Theorem actual_admitted_ADD_step words events ev token(frontier:FormalSpec.State)i rd rs1 rs2:
 let image:=ExtendedSVPackedROM.pack words in let pre:={pre}in
 Forall(Word 32)words ->Z.of_nat(length words)<=2^30 ->
 (i<{capacity})%nat ->Z.of_nat i<2^25 ->32*Z.of_nat i<2^Z.of_nat {offset} ->
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->
 FrontierAt pre frontier i words ->
 Decode.decode Decode.RV32I({r}.R.lookup image(word.unsigned(getPc frontier)))=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 In token({q}.admitted ev pre {packed}) ->
 exists after,CPUOriginalISAReference.instruction_effect {r}.recorded_pc token_word token frontier=Some after /\\
 FormalSpec.run1 frontier=(Some tt,after).
Proof. intros image pre HW HL HC HI HO HE HEv[HPC[HA HM]]HD HT.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HS];fold pre in HS.
 pose proof(admitted_pc ev pre {packed} token HT)as HP.
 pose proof(sampled_address_at_current_pc seed ev pre HEv HS)as HSample.
 assert(HActualPC:token_pc token=Some(4*Z.of_nat i)).
 {{ exact(eq_trans HP(f_equal (@Some Z)(eq_trans HSample(eq_trans HPC HA)))). }}
 assert(HAll:Forall {h}.W.Environment(events++[ev]))by(apply Forall_app;split;[exact HE|constructor;[exact HEv|constructor]]).
 pose proof(admitted_recorded_after image events ev token HT)as HRecorded;fold image in HRecorded.
 pose proof({r}.R.boot_recorded_content image(events++[ev])token HAll HRecorded)as HContent.
 destruct HContent as[address[HAddress HWord]].
 assert(HEq:address=word.unsigned(getPc frontier))by congruence;subst address.
 assert(HDecode:Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2)).
 {{ exact(eq_trans(f_equal(Decode.decode Decode.RV32I)HWord)HD). }}
 exact({r}.recorded_add_executes_original_isa words(events++[ev])token frontier i rd rs1 rs2
 HW HL HC HI HO HAll HRecorded HActualPC HA HM HDecode). Qed.
Theorem actual_admitted_ADD_chain words events ev(frontier:FormalSpec.State)i rd rs1 rs2:
 let image:=ExtendedSVPackedROM.pack words in let pre:={pre}in
 Forall(Word 32)words ->Z.of_nat(length words)<=2^30 ->
 (i<{capacity})%nat ->Z.of_nat i<2^25 ->32*Z.of_nat i<2^Z.of_nat {offset} ->
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->
 FrontierAt pre frontier i words ->
 Decode.decode Decode.RV32I({r}.R.lookup image(word.unsigned(getPc frontier)))=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 exists next,EffectChain(CPUOriginalISAReference.instruction_effect {r}.recorded_pc token_word)
 frontier({q}.admitted ev pre {packed})next.
Proof. intros image pre HW HL HC HI HO HE HEv HF HD.
 destruct(admitted_empty_or_one ev pre {packed})as[HN|[token HN]].
 - rewrite HN;exists frontier;constructor.
 - assert(HT:In token({q}.admitted ev pre {packed}))by(rewrite HN;now left).
   destruct(actual_admitted_ADD_step words events ev token frontier i rd rs1 rs2 HW HL HC HI HO HE HEv HF HD HT)as[next[HS HR]].
   rewrite HN;exists next;econstructor;[exact HS|constructor]. Qed.
End OriginalISA.
Goal True. idtac "ADMISSION_REFERENCE_LOCAL_AUDIT". exact I. Qed.
'''
    locals_ = ['pc_comb_frame', 'address_at_pc_boundary', 'sampled_address_at_current_pc', 'boot_history_one_more',
        'admitted_as_births', 'actual_accept_source', 'admitted_pc', 'admitted_recorded_after', 'admitted_empty_or_one']
    text += ''.join('Print Assumptions ' + name + '.\n' for name in locals_)
    text += '''Goal True. idtac "ADMISSION_REFERENCE_ISA_AUDIT". exact I. Qed.
Print Assumptions actual_admitted_ADD_step.
Print Assumptions actual_admitted_ADD_chain.
'''
    return text, len(locals_)


def check(c, output):
    out = Path(output); out.mkdir(parents=True, exist_ok=False)
    graph = fetch.cdfg.checked_graph(c['graph'], c['ast'], out / 'replayed')
    raw, profile, _ = fetch.cdfg.raw_binding(c['ast'], c['ast_module'])
    plan = discover(c, raw, profile, graph)
    fp = Path(c['fetch_reference']); fr = json.loads((fp / 'report.json').read_text())
    fs = fp / 'FetchReference.v'
    if not (fr.get('accepted') and fr['coqc_exit'] == fr['coqchk_exit'] == 0 and fr['assumptions_audit_passed']
            and fr.get('new_run1_success_proved') and fr['ast_sha256'] == raw['source_sha256']
            and fr['graph_sha256'] == hashlib.sha256(Path(c['graph']).read_bytes()).hexdigest()
            and fr['source_sha256'] == hashlib.sha256(fs.read_bytes()).hexdigest()
            and fr['object_sha256'] == hashlib.sha256(fs.with_suffix('.vo').read_bytes()).hexdigest()):
        raise ValueError('same-source accepted original-fetch/ADD provider required')
    from cpu_add_admission_ledger import checked_provider
    paths = checked_provider(c['admission_queue'], 'AdmissionQueue.v', raw['source_sha256'],
        ['actual_post_ledger_queue_equation_proved', 'actual_post_operand_clause_proved'])
    paths += json.loads((fp / 'providers.json').read_text())
    paths += [dict(directory=str(fp.resolve()), namespace='GeneratedFetchReference'),
        dict(directory=str(Path(c['admission_queue']).resolve()), namespace='GeneratedAdmissionQueue')]
    bindings = {}
    for row in paths:
        if row['namespace'] in bindings and bindings[row['namespace']] != row['directory']:
            raise ValueError('different original runtime or fetch providers')
        bindings[row['namespace']] = row['directory']
    paths = [dict(namespace=k, directory=v) for k,v in bindings.items()]
    # Coq -R is recursive: a parent added after its child erases the child's
    # logical namespace, even if the generated source is otherwise correct.
    paths.sort(key=lambda row: len(Path(row['directory']).parts))
    queue.sources.controls.history.admission.verify_environment_paths(paths)
    text, count = render(c, raw, profile, plan); file = out / 'AdmissionReference.v'; file.write_text(text)
    for name,data in [('plan',plan),('providers',paths)]:
        (out / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    flags = list(queue.sources.rtl.framework.FLAGS)
    flags += ['-R', str(out.resolve()), 'GeneratedAdmissionReference']
    for row in paths: flags += ['-R', row['directory'], row['namespace']]
    start = time.monotonic()
    cc,timed = run_stage(['/usr/bin/time','-v','-o',str((out/'coqc.resources').resolve()),
        str(fetch.cdfg.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report = dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=timed,
        source_sha256=hashlib.sha256(text.encode()).hexdigest(),ast_sha256=raw['source_sha256'],old_inv_read=False,
        actual_admitted_original_ADD_chain_proved=False,frontier_PC_preservation_proved=False,
        full_R_generated=False,itree_refinement_proved=False,external_llm_api_calls=0)
    if cc.returncode == 0:
        local=cc.stdout.split('ADMISSION_REFERENCE_LOCAL_AUDIT')[-1].split('ADMISSION_REFERENCE_ISA_AUDIT')[0]
        axioms=audit_all_exports(cc.stdout.split('ADMISSION_REFERENCE_ISA_AUDIT')[-1],2)
        closed=local.count('Closed under the global context')==count and 'Axioms:'not in local
        baseline=set(fr['baseline_assumptions']);audit=closed and not(axioms-baseline)and not(axioms-ALLOWED_AXIOMS)
        kk,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqchk.resources').resolve()),
            str(fetch.cdfg.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedAdmissionReference.AdmissionReference'],
            out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        ok=audit and kk.returncode==0
        report.update(accepted=ok,coqchk_exit=kk.returncode,coqchk_timed_out=timed,
            local_assumptions_closed=closed,assumptions_audit_passed=audit,
            isa_assumptions=sorted(axioms),baseline_assumptions=sorted(baseline),
            actual_admitted_original_ADD_chain_proved=ok)
    report['seconds']=time.monotonic()-start
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ['inputs','output']:parser.add_argument('--'+key,required=True)
    args=parser.parse_args()
    try:report=check(json.loads(Path(args.inputs).read_text()),args.output)
    except Exception as exc:
        out=Path(args.output)
        if out.is_dir()and not(out/'report.json').exists():
            (out/'report.json').write_text(json.dumps(dict(accepted=False,stage='preflight',error=str(exc),cli_exit=1),indent=2)+'\n')
        raise
    print(json.dumps(report,indent=2));raise SystemExit(0 if report['accepted']else 1)
