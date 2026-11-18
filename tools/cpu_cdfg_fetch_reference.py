"""Connect CDFG-selected, actually captured ROM words to the original ISA fetch.

PC order is deliberately not an environment assumption. The resulting rule
exposes the remaining frontier-PC/ROM-domain premises, to be discharged by R.
It does not assert a new run1 execution chain or a full invariant.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_cdfg_result_consumer as cdfg
import cpu_captured_rom as rom
from cpu_certificate_acceptance import run_stage, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports


def discover(raw, graph):
    pairs = rom.pc.fetch.discover(raw)
    if len(pairs['pairs']) != 1 or pairs['residuals']:
        raise ValueError('unique fully derived capture/ROM pair required')
    pair = pairs['pairs'][0]
    by_root = {}
    for symbol in graph['symbols']:
        by_root.setdefault(symbol['coq_root'], []).append(symbol)
    queries = {}
    for role in ['carrier', 'pc_root', 'address_root', 'word_input']:
        candidates = by_root.get(pair[role], [])
        if len(candidates) != 1 or candidates[0]['width'] != 32:
            raise ValueError('ambiguous or wrong-width graph role: ' + role)
        symbol = candidates[0]
        query = cdfg.backward_slice(graph, symbol['path'])
        cone = cdfg.cone.cone(raw, 32, pair[role])
        cdfg.agree(graph, query, cone)
        queries[role] = dict(symbol=symbol, query=query, coq_cone=cone)
    width = pair['reader']['bank_width']
    if width <= 0 or width % 32:
        raise ValueError('ROM capacity is not a whole number of 32-bit words')
    offset = rom.rtl.Parser(pair['reader']['offset']).complete()
    if offset.name != 'ESel':
        raise ValueError('unsupported ROM address offset expression')
    offset_width = int(offset.args[0].name)
    expression = rom.rtl.Parser(
        f'(ESel 32 (EVar {width} {pair["reader"]["bank_root"]}) '
        f'{pair["reader"]["offset"]})').complete()
    lookup = rom.abstract_read(expression, pair['reader']['bank_root'], pair['address_root'])
    expected = (f'(ESel 32 (EConst {width} image) (ESel {offset_width} '
        '(EBinary 32 BShiftL (EExtend 32 false (ESel 30 (EConst 32 address) '
        '(EConst 5 2))) (EConst 32 5)) (EConst 32 0)))')
    if lookup.split() != expected.split():
        raise ValueError('ROM lookup does not match the proved packed-image address rule')
    return dict(pair=pair, queries=queries, capacity=width // 32,
        offset_width=offset_width, lookup_expression=lookup,
        ast_sha256=raw['source_sha256'])


def render(plan):
    capacity, offset = plan['capacity'], plan['offset_width']
    return f'''From Coq Require Import List ZArith Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVPackedROM
 Lang.ExtendedSVCaptureBirth Ex.External.CPUPackedROMReference Ex.External.CPUProgramROM
 Ex.External.CPUOriginalISAReference Ex.RvCore.FormalSpec Ex.RvCore.Machine
 Ex.External.CPUOriginalInstructionSuccess Ex.External.CPUISADecodeInputs
 Ex.External.CV32E40PReq41Instruction
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 coqutil.Z.BitOps riscv.Utility.MkMachineWidth riscv.Utility.Utility riscv.Utility.Monads
 GeneratedCapturedROM.CapturedROM GeneratedISADestinations.ISADestinations.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVCaptureBirth.
Module R:=GeneratedCapturedROM.CapturedROM.
Local Open Scope Z_scope.
Local Opaque R.H.F.boot R.H.boot_history.
Definition recorded_pc(token:Token):Z:=match token_pc token with Some pc=>pc|None=>0 end.
Lemma lookup_is_original_expression image address:
 R.lookup image address=ExtendedSVPackedROM.lookup {capacity} {offset} image address.
Proof. reflexivity. Qed.
Section OriginalISA.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{registers_ok:map.ok Registers}}{{mem_ok:map.ok Mem}}.
Theorem recorded_word_matches_original_memory words events token pc i:
 Forall(Word 32)words ->Z.of_nat(length words)<=2^30 ->
 (i<{capacity})%nat ->Z.of_nat i<2^25 ->32*Z.of_nat i<2^Z.of_nat {offset} ->
 Forall R.H.W.Environment events ->
 In token(history(fst(R.H.boot_history(ExtendedSVPackedROM.pack words)events))) ->
 token_pc token=Some(4*Z.of_nat i) ->word.unsigned pc=4*Z.of_nat i ->
 exists bytes,Memory.load_bytes 4(FormalSpec.formal_initial_imem(CPUProgramROM.entries words))pc=Some bytes /\\
 token_word token=LittleEndian.combine 4 bytes.
Proof. intros HW HL HC HI HO HE HT HP HA.
 pose proof(R.boot_recorded_content _ events token HE HT)as HContent.
 destruct HContent as[address[HAddress HWord]].
 assert(HAddressEq:address=4*Z.of_nat i)by congruence;subst address.
 destruct(CPUPackedROMReference.image_matches_isa_load {capacity} {offset} words pc i
 HW HL HC HI HO HA)as[bytes[HF HB]].
 exists bytes;split;[exact HF|].
 exact(eq_trans HWord(eq_trans(lookup_is_original_expression _ _)
   (eq_trans(f_equal(ExtendedSVPackedROM.lookup {capacity} {offset}(ExtendedSVPackedROM.pack words))(eq_sym HA))(eq_sym HB)))).
Qed.
Theorem recorded_token_matches_original_fetch words events token (before:FormalSpec.State) i:
 Forall(Word 32)words ->Z.of_nat(length words)<=2^30 ->
 (i<{capacity})%nat ->Z.of_nat i<2^25 ->32*Z.of_nat i<2^Z.of_nat {offset} ->
 Forall R.H.W.Environment events ->
 In token(history(fst(R.H.boot_history(ExtendedSVPackedROM.pack words)events))) ->
 token_pc token=Some(4*Z.of_nat i) ->word.unsigned(getPc before)=4*Z.of_nat i ->
 getInstMem before=FormalSpec.formal_initial_imem(CPUProgramROM.entries words) ->
 exists bytes,Machine.loadWord Machine.Fetch(getPc before)before=(Some bytes,before) /\\
 recorded_pc token=word.unsigned(getPc before) /\\token_word token=LittleEndian.combine 4 bytes.
Proof. intros HW HL HC HI HO HE HT HP HA HM.
 destruct(recorded_word_matches_original_memory words events token(getPc before)i HW HL HC HI HO HE HT HP HA)
 as[bytes[HF HB]].
 exists bytes;split.
 - assert(HAL:negb(word.eqb(word.modu(getPc before)(word.of_Z 4))(word.of_Z 0))=false).
   {{ rewrite word.unsigned_eqb,word.unsigned_modu.
      2:{{ rewrite word.unsigned_of_Z;unfold word.wrap;change(4 mod 2^32)with 4;lia. }}
      rewrite !word.unsigned_of_Z;unfold word.wrap.
      change(4 mod 2^32)with 4;change(0 mod 2^32)with 0.
      rewrite HA,Z.mul_comm,Z.mod_mul by discriminate;reflexivity. }}
   unfold Machine.loadWord;cbn[IsRiscvProgram];unfold Machine.loadN,Machine.assert_aligned.
   change(negb(reg_eqb(remu(getPc before)(ZToReg 4))(ZToReg 0))=false)in HAL.
   rewrite HAL.
   cbn[Bind Return OState_Monad OStateOperations.get].
   unfold Machine.fail_if_None;rewrite HM,HF;reflexivity.
 - split;[unfold recorded_pc;rewrite HP;exact(eq_sym HA)|exact HB].
Qed.
Theorem recorded_original_effect_from_run1 words events token(before after:FormalSpec.State)i:
 Forall(Word 32)words ->Z.of_nat(length words)<=2^30 ->
 (i<{capacity})%nat ->Z.of_nat i<2^25 ->32*Z.of_nat i<2^Z.of_nat {offset} ->
 Forall R.H.W.Environment events ->
 In token(history(fst(R.H.boot_history(ExtendedSVPackedROM.pack words)events))) ->
 token_pc token=Some(4*Z.of_nat i) ->word.unsigned(getPc before)=4*Z.of_nat i ->
 getInstMem before=FormalSpec.formal_initial_imem(CPUProgramROM.entries words) ->
 FormalSpec.run1 before=(Some tt,after) ->
 CPUOriginalISAReference.instruction_effect recorded_pc token_word token before=Some after.
Proof. intros HW HL HC HI HO HE HT HP HA HM HR.
 destruct(recorded_token_matches_original_fetch words events token before i HW HL HC HI HO HE HT HP HA HM)
 as[bytes[HF[HPC HWord]]].
 exact(CPUOriginalISAReference.instruction_effect_complete recorded_pc token_word token before after bytes
 HPC(f_equal (@fst _ _)HF)HWord HR).
Qed.
Theorem recorded_add_executes_original_isa words events token(before:FormalSpec.State)i rd rs1 rs2:
 Forall(Word 32)words ->Z.of_nat(length words)<=2^30 ->
 (i<{capacity})%nat ->Z.of_nat i<2^25 ->32*Z.of_nat i<2^Z.of_nat {offset} ->
 Forall R.H.W.Environment events ->
 In token(history(fst(R.H.boot_history(ExtendedSVPackedROM.pack words)events))) ->
 token_pc token=Some(4*Z.of_nat i) ->word.unsigned(getPc before)=4*Z.of_nat i ->
 getInstMem before=FormalSpec.formal_initial_imem(CPUProgramROM.entries words) ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 exists after,CPUOriginalISAReference.instruction_effect recorded_pc token_word token before=Some after /\\
 FormalSpec.run1 before=(Some tt,after).
Proof. intros HW HL HC HI HO HE HT HP HA HM HD.
 destruct(recorded_word_matches_original_memory words events token(getPc before)i HW HL HC HI HO HE HT HP HA)
 as[bytes[HF HB]].
 assert(HCurrent:CV32E40PReq41Instruction.CurrentInstruction before(Decode.Add rd rs1 rs2)).
 {{ split.
    - rewrite HA,Z.mul_comm,Z.mod_mul by discriminate;reflexivity.
    - exists bytes;split;[rewrite HM;exact HF|].
      exact(eq_trans(f_equal(Decode.decode Decode.RV32I)(eq_sym HB))HD). }}
 pose proof(GeneratedISADestinations.ISADestinations.original_destination_address
   (token_word token)(Decode.Add rd rs1 rs2)rd [] HD eq_refl)as Hrd.
 pose proof(CPUISADecodeInputs.first_register_field(token_word token)(Decode.Add rd rs1 rs2)rs1[rs2]HD eq_refl)as Hrs1.
 pose proof(CPUISADecodeInputs.second_register_field(token_word token)(Decode.Add rd rs1 rs2)rs1 rs2[]HD eq_refl)as Hrs2.
 assert(HrdBound:0<=rd<32).
 {{ rewrite Hrd;change(0<=BitOps.bitSlice(token_word token)7 12<2^(12-7));apply BitOps.bitSlice_bounds;lia. }}
 assert(Hrs1Bound:0<=rs1<32).
 {{ rewrite Hrs1;change(0<=BitOps.bitSlice(token_word token)15 20<2^(20-15));apply BitOps.bitSlice_bounds;lia. }}
 assert(Hrs2Bound:0<=rs2<32).
 {{ rewrite Hrs2;change(0<=BitOps.bitSlice(token_word token)20 25<2^(25-20));apply BitOps.bitSlice_bounds;lia. }}
 destruct(CPUOriginalInstructionSuccess.original_add_run1_total before rd rs1 rs2 HCurrent HrdBound Hrs1Bound Hrs2Bound)
 as[after HR].
 exists after;split;[exact(recorded_original_effect_from_run1 words events token before after i HW HL HC HI HO HE HT HP HA HM HR)|exact HR].
Qed.
End OriginalISA.
Goal True. idtac "CDFG_FETCH_LOCAL_AUDIT". exact I. Qed.
Print Assumptions lookup_is_original_expression.
Goal True. idtac "CDFG_FETCH_ISA_AUDIT". exact I. Qed.
Print Assumptions recorded_word_matches_original_memory.
Print Assumptions recorded_token_matches_original_fetch.
Print Assumptions recorded_original_effect_from_run1.
Print Assumptions recorded_add_executes_original_isa.
'''


def check(c, pair_provider, output):
    out = Path(output); out.mkdir(parents=True, exist_ok=False)
    graph = cdfg.checked_graph(c['graph'], c['ast'], out / 'replayed')
    raw, _, _ = cdfg.raw_binding(c['ast'], c['ast_module'])
    plan = discover(raw, graph)
    # Rebuild this small raw-generated provider rather than trusting a historical
    # object without an object-hash receipt. No CPU invariant is an input.
    proof = rom.check(c['ast'], c['ast_module'], c['history'], pair_provider, out / 'rom')
    if not proof['accepted']:
        report = dict(accepted=False, stage='raw-rom-provider', provider=proof)
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        return report
    rp = json.loads((out / 'rom/plan.json').read_text())
    if any(rp['pair'][key] != value for key, value in plan['pair'].items()):
        raise ValueError('proved physical ROM path differs from graph-selected path')
    paths = list(rp['paths']) + [dict(directory=str(Path(pair_provider).resolve()), namespace='GeneratedFetchPairs'),
        dict(directory=str((out / 'rom').resolve()), namespace='GeneratedCapturedROM')]
    rules = json.loads((Path(c['original_success']) / 'report.json').read_text())
    module = 'Ex/External/CPUOriginalInstructionSuccess'
    row = next((r for r in rules['modules'] if r['module'] == module), None)
    success_source = cdfg.ROOT / ('src/' + module + '.v')
    if not (rules['accepted'] and row and row['accepted']
            and row['coqc_exit'] == row['coqchk_exit'] == 0 and row['assumptions_audit_passed']
            and set(row['assumptions']) <= set(rules['baseline_assumptions']) <= ALLOWED_AXIOMS
            and hashlib.sha256(success_source.read_bytes()).hexdigest() == row['source_sha256']):
        raise ValueError('native-checked original ISA success rules required')
    context = json.loads((Path(c['derived_sources']) / 'providers.json').read_text())
    destinations = [r for r in context if r['namespace'] == 'GeneratedISADestinations']
    if len(destinations) != 1:
        raise ValueError('same original ISA destination field provider required')
    paths += destinations
    source = render(plan); file = out / 'FetchReference.v'; file.write_text(source)
    for name, data in [('plan', plan), ('providers', paths)]:
        (out / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    flags = list(rom.rtl.framework.FLAGS)
    flags += ['-R', str(out.resolve()), 'GeneratedFetchReference']
    for path in paths: flags += ['-R', path['directory'], path['namespace']]
    start = time.monotonic()
    cc, timed = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqc.resources').resolve()),
        str(cdfg.ROOT / '_opam/bin/coqc'), '-time', *flags, str(file.resolve())], out / 'coqc.log', 1200)
    report = dict(accepted=False, coqc_exit=cc.returncode, coqc_timed_out=timed,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(), ast_sha256=raw['source_sha256'],
        graph_sha256=hashlib.sha256(Path(c['graph']).read_bytes()).hexdigest(), old_inv_read=False,
        translation_equivalence_proved=False, complete_R_generated=False, itree_refinement_proved=False,
        actual_capture_to_original_fetch_proved=False, ISA_frontier_PC_order_proved=False,
        new_run1_success_proved=False, external_llm_api_calls=0, provider=proof)
    if cc.returncode == 0:
        local = cc.stdout.split('CDFG_FETCH_LOCAL_AUDIT')[-1].split('CDFG_FETCH_ISA_AUDIT')[0]
        axioms = audit_all_exports(cc.stdout.split('CDFG_FETCH_ISA_AUDIT')[-1], 4)
        closed = local.count('Closed under the global context') == 1 and 'Axioms:' not in local
        baseline = set(json.loads((Path(c['derived_sources']) / 'report.json').read_text())['baseline_assumptions'])
        audit = closed and not (axioms - baseline) and not (axioms - ALLOWED_AXIOMS)
        kk, timed = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqchk.resources').resolve()),
            str(cdfg.ROOT / '_opam/bin/coqchk'), '-silent', *flags, '-norec', 'GeneratedFetchReference.FetchReference'],
            out / 'coqchk.log', max(.1, 1200 - (time.monotonic() - start)))
        ok = audit and kk.returncode == 0
        report.update(accepted=ok, coqchk_exit=kk.returncode, coqchk_timed_out=timed,
            assumptions_audit_passed=audit, local_assumptions_closed=closed,
            isa_assumptions=sorted(axioms), baseline_assumptions=sorted(baseline),
            actual_capture_to_original_fetch_proved=ok, new_run1_success_proved=ok)
        if ok:
            report['object_sha256'] = hashlib.sha256(file.with_suffix('.vo').read_bytes()).hexdigest()
    report['seconds'] = time.monotonic() - start
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ['inputs', 'pair-provider', 'output']: parser.add_argument('--' + key, required=True)
    args = parser.parse_args()
    try:
        report = check(json.loads(Path(args.inputs).read_text()), args.pair_provider, args.output)
    except Exception as exc:
        out = Path(args.output)
        if out.is_dir() and not (out / 'report.json').exists():
            (out / 'report.json').write_text(json.dumps(dict(accepted=False, stage='preflight', error=str(exc), cli_exit=1), indent=2) + '\n')
        raise
    print(json.dumps(report, indent=2)); raise SystemExit(0 if report['accepted'] else 1)
