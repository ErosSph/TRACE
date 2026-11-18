"""Bind raw-generated output requirements to original ISA source reads.

This reuses checked physical equations generated from the same AST, never a
CPU invariant. Prefix validity, port/token/address identity and actual source
selection remain explicit obligations, not automatically established facts.
"""
import argparse
import hashlib
import json
import re
import time
from pathlib import Path
import cpu_operand_route_proofs as routes
import cpu_instruction_scope as scopes
from cpu_certificate_acceptance import run_stage
origin = routes.origin


def history_source(program, outputs):
    lines=['''Context {registers_ok:map.ok Registers}.
Theorem source_from_original_history width root expression seed fixed
 initial pending index token reference i address physical:
 CombLFP '''+program+''' seed fixed ->
 (norm width(read_signal fixed root)=norm width(eval_expr fixed expression)) ->
 RegisterRelated physical initial ->
 BeforeToken(instruction_effect token_pc token_word)initial pending index token reference ->
 Forall(fun older=>exists j,requested_instruction j=true /\\
   Decode.decode Decode.RV32I(token_word older)=Decode.IInstruction j)(firstn index pending) ->
 requested_instruction i=true ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction i ->
 In address(requested_registers i) ->
 exists batches value,map fst batches=firstn index pending /\\
 CertifiedBatches token_pc token_word initial batches reference /\\
 Machine.getRegister address reference=(Some value,reference) /\\
 (source_requirements width expression fixed physical batches address <->
  norm width(read_signal fixed root)=word.unsigned value).
Proof.
 intros HL HE HR HT HP HI HD HA.
 destruct(requested_values_before_execution token_pc token_word initial pending index
   token reference i HT HP HI HD)as[batches [HM [HC HV]]].
 rewrite Forall_forall in HV;destruct(HV address HA)as[value [Hread Hvalue]].
 exists batches,value;split;[exact HM|];split;[exact HC|];split;[exact Hread|].
 exact(source_requirements_exact token_pc token_word width root expression fixed
   initial batches reference reference address value physical HC HR
   (CPUISAInstructionExecution.read_address_bounds reference reference address value Hread) Hread HE).
Qed.
Theorem source_from_indexed_address width root expression seed fixed
 address_width address_root observed operand_position
 initial pending index token reference i physical:
 CombLFP '''+program+''' seed fixed ->
 (norm width(read_signal fixed root)=norm width(eval_expr fixed expression)) ->
 RegisterRelated physical initial ->
 BeforeToken(instruction_effect token_pc token_word)initial pending index token reference ->
 Forall(fun older=>exists j,requested_instruction j=true /\\
   Decode.decode Decode.RV32I(token_word older)=Decode.IInstruction j)(firstn index pending) ->
 requested_instruction i=true ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction i ->
 nth_error (CV32E40PReq41Instruction.CV32E40PReq41Instruction.source_registers i) operand_position <> None ->
 IndexedSourceAddress address_width address_root observed i operand_position ->
 exists batches value,map fst batches=firstn index pending /\\
 CertifiedBatches token_pc token_word initial batches reference /\\
 Machine.getRegister (norm address_width(read_signal observed address_root)) reference=(Some value,reference) /\\
 (source_requirements width expression fixed physical batches
    (norm address_width(read_signal observed address_root)) <->
  norm width(read_signal fixed root)=word.unsigned value).
Proof.
 intros HL HE HR HT HP HI HD HN HA.
 apply(source_from_original_history width root expression seed fixed initial pending
   index token reference i (norm address_width(read_signal observed address_root))
   physical HL HE HR HT HP HI HD).
 rewrite requested_registers_agree.
 exact(indexed_source_address_member address_width address_root observed i operand_position HN HA).
Qed.''']
    for n,row in enumerate(outputs):
        width,root=row['width'],row['output_root']
        lines += [f'''Theorem port_{n}_source_R_from_history seed fixed
 initial pending index token reference i address physical:
 CombLFP {program} seed fixed ->RegisterRelated physical initial ->
 BeforeToken(instruction_effect token_pc token_word)initial pending index token reference ->
 Forall(fun older=>exists j,requested_instruction j=true /\\
   Decode.decode Decode.RV32I(token_word older)=Decode.IInstruction j)(firstn index pending) ->
 requested_instruction i=true ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction i ->
 In address(requested_registers i) ->
 exists batches value,map fst batches=firstn index pending /\\
 CertifiedBatches token_pc token_word initial batches reference /\\
 Machine.getRegister address reference=(Some value,reference) /\\
 (port_{n}_source_R fixed physical batches address <->
  norm {width}%nat(read_signal fixed {root}%nat)=word.unsigned value).
Proof.
 intro HL;exact(source_from_original_history {width}%nat {root}%nat port_{n}_rhs seed fixed
   initial pending index token reference i address physical HL (port_{n}_lfp seed fixed HL)).
Qed.''']
    return '\n'.join(lines)


def computed_history_source(program):
    return '''Theorem source_from_computed_prefix
 (same:forall x y:Token,{x=y}+{x<>y})
 width root expression seed fixed address_width address_root observed operand_position
 initial pending index token reference i physical:
 CombLFP '''+program+''' seed fixed ->
 (norm width(read_signal fixed root)=norm width(eval_expr fixed expression)) ->
 RegisterRelated physical initial ->
 CPUComputedReferenceCut.lookup_before (instruction_effect token_pc token_word)
   same token initial pending=Some(index,reference) ->
 Forall(fun older=>exists j,requested_instruction j=true /\\
   Decode.decode Decode.RV32I(token_word older)=Decode.IInstruction j)(firstn index pending) ->
 requested_instruction i=true ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction i ->
 nth_error (CV32E40PReq41Instruction.CV32E40PReq41Instruction.source_registers i) operand_position <> None ->
 IndexedSourceAddress address_width address_root observed i operand_position ->
 exists batches value,map fst batches=firstn index pending /\\
 CertifiedBatches token_pc token_word initial batches reference /\\
 Machine.getRegister (norm address_width(read_signal observed address_root)) reference=(Some value,reference) /\\
 (source_requirements width expression fixed physical batches
    (norm address_width(read_signal observed address_root)) <->
  norm width(read_signal fixed root)=word.unsigned value).
Proof.
 intros HL HE HR HC.
 exact(source_from_indexed_address width root expression seed fixed address_width
 address_root observed operand_position initial pending index token reference i physical
 HL HE HR (CPUComputedReferenceCut.lookup_before_sound
 (instruction_effect token_pc token_word) same token pending initial index reference HC)).
Qed.
'''


def computed_relation_source(program, outputs):
    lines=['''Definition computed_operand_R
 (same:forall x y:Token,{x=y}+{x<>y}) width root observed initial pending token position : Prop :=
 match CPUComputedReferenceCut.lookup_before (instruction_effect token_pc token_word)
   same token initial pending with
 | None=>False
 | Some(_,reference)=>
   match Decode.decode Decode.RV32I(token_word token) with
   | Decode.IInstruction i=>if requested_instruction i then
     match nth_error(requested_registers i)position with
     | None=>True
     | Some address=>match Machine.getRegister address reference with
       | (Some value,_)=>norm width(read_signal observed root)=word.unsigned value
       | _=>False end
     end else False
   | _=>False end
 end.

Theorem computed_operand_R_reduction same width root observed initial pending token position
 index reference i address value:
 CPUComputedReferenceCut.lookup_before (instruction_effect token_pc token_word)
   same token initial pending=Some(index,reference) ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction i ->
 requested_instruction i=true ->nth_error(requested_registers i)position=Some address ->
 Machine.getRegister address reference=(Some value,reference) ->
 (computed_operand_R same width root observed initial pending token position <->
  norm width(read_signal observed root)=word.unsigned value).
Proof. intros HC HD HI HN HR;unfold computed_operand_R;rewrite HC,HD,HI,HN,HR;reflexivity. Qed.

Theorem computed_operand_R_missing_token same width root observed initial pending token position:
 CPUComputedReferenceCut.lookup_before (instruction_effect token_pc token_word)
   same token initial pending=None ->
 ~computed_operand_R same width root observed initial pending token position.
Proof. intro H;unfold computed_operand_R;rewrite H;exact(fun H=>H). Qed.

Theorem computed_operand_R_matches_requirement
 (same:forall x y:Token,{x=y}+{x<>y})
 width root expression seed fixed address_width address_root observed position
 initial pending index token reference i physical:
 CombLFP '''+program+''' seed fixed ->
 (norm width(read_signal fixed root)=norm width(eval_expr fixed expression)) ->
 RegisterRelated physical initial ->
 CPUComputedReferenceCut.lookup_before (instruction_effect token_pc token_word)
   same token initial pending=Some(index,reference) ->
 Forall(fun older=>exists j,requested_instruction j=true /\\
   Decode.decode Decode.RV32I(token_word older)=Decode.IInstruction j)(firstn index pending) ->
 requested_instruction i=true ->Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction i ->
 nth_error (CV32E40PReq41Instruction.CV32E40PReq41Instruction.source_registers i) position <> None ->
 IndexedSourceAddress address_width address_root observed i position ->
 exists batches,map fst batches=firstn index pending /\\
 CertifiedBatches token_pc token_word initial batches reference /\\
 (computed_operand_R same width root fixed initial pending token position <->
  source_requirements width expression fixed physical batches
    (norm address_width(read_signal observed address_root))).
Proof.
 intros HL HE HR HC HP HI HD HN HA.
 destruct(source_from_computed_prefix same width root expression seed fixed address_width
 address_root observed position initial pending index token reference i physical
 HL HE HR HC HP HI HD HN HA)as[batches[value[HM[HB[HV HQ]]]]].
 assert(Haddr:nth_error(requested_registers i)position=
 Some(norm address_width(read_signal observed address_root))).
 { rewrite requested_registers_agree;unfold IndexedSourceAddress in HA.
   destruct(nth_error _ position)as[address|]eqn:HT;[rewrite HA;reflexivity|contradiction]. }
 exists batches;split;[exact HM|];split;[exact HB|].
 rewrite(computed_operand_R_reduction same width root fixed initial pending token position
 index reference i (norm address_width(read_signal observed address_root)) value HC HD HI Haddr HV).
 symmetry;exact HQ.
Qed.
''']
    for n,row in enumerate(outputs):
        lines += [f'''Definition port_{n}_computed_R same observed initial pending token position :=
 computed_operand_R same {row['width']}%nat {row['output_root']}%nat observed initial pending token position.''']
    return '\n'.join(lines)


def render(program, outputs, include_history=False):
    lines = ['''From Coq Require Import ZArith List.
Require Import Ex.External.CPUISAValueRequirements
 Ex.External.CPUISAReadyBatches Ex.External.CPUReadyOperand
 Ex.External.CPUISAOwnedEffects Ex.External.CPURegisterEffectRelation
 Ex.RvCore.FormalSpec Ex.RvCore.Machine
 Lang.ExtendedSV Lang.ExtendedSVValueRequirements
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte GeneratedOperandRoutes.OperandRoutes.
Import ExtendedSV CPUISAValueRequirements CPUISAOwnedEffects CPURegisterEffectRelation
 CPUISAReadyBatches CPUReadyOperand.
Local Open Scope Z_scope.
Section GeneratedReferenceRequirements.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}{word_ok:word.ok word}
 {Token:Type}.
Variable token_pc token_word:Token->Z.
''']
    for n, row in enumerate(outputs):
        width, root = row['width'], row['output_root']
        lines += [f'''Definition port_{n}_source_R fixed physical batches address :=
 @source_requirements Token {width}%nat port_{n}_rhs fixed physical batches address.
Theorem port_{n}_source_R_exact seed fixed initial batches before after address value physical:
 CombLFP {program} seed fixed ->
 CertifiedBatches token_pc token_word initial batches before ->
 RegisterRelated physical initial -> 0<=address<32 ->
 Machine.getRegister address before=(Some value,after) ->
 (port_{n}_source_R fixed physical batches address <->
 norm {width}%nat(read_signal fixed {root}%nat)=word.unsigned value).
Proof.
 intros HL HC HP HA HR;unfold port_{n}_source_R.
 exact(source_requirements_exact token_pc token_word {width}%nat {root}%nat
   port_{n}_rhs fixed initial batches before after address value physical
   HC HP HA HR (port_{n}_lfp seed fixed HL)).
Qed.
Theorem port_{n}_ready_source_matches_read seed fixed initial batches before after
 address value physical slots:
 CombLFP {program} seed fixed ->
 CertifiedBatches token_pc token_word initial batches before ->
 RegisterRelated physical initial ->0<=address<32 ->
 Machine.getRegister address before=(Some value,after) ->
 Forall2 SlotRelated slots(batch_writes 32 address batches) ->
 resolve 0 physical address slots=Some(norm {width}%nat(eval_expr fixed port_{n}_rhs)) ->
 norm {width}%nat(read_signal fixed {root}%nat)=word.unsigned value.
Proof.
 intros HL HC HP HA HR HS HE;rewrite(port_{n}_lfp seed fixed HL).
 exact(actual_ready_selector_matches_read token_pc token_word initial batches before
   after address value physical slots (norm {width}%nat(eval_expr fixed port_{n}_rhs))
   HC HP HA HR HS HE).
Qed.''']
    if include_history:
        lines.insert(0,'''Require Import GeneratedISAInputs.ISAInputs
 Ex.External.CPUReferenceCuts Ex.External.CPUOriginalISAReference Ex.External.CPUISAInstructionExecution
 Ex.External.CPUIndexedSource Ex.External.CPUComputedReferenceCut.
Import CPUReferenceCuts CPUOriginalISAReference.''')
        lines.append(history_source(program, outputs))
        lines.append(computed_history_source(program))
        lines.append(computed_relation_source(program,outputs))
    lines += ['End GeneratedReferenceRequirements.',
              'Goal True. idtac "SOURCE_REFERENCE_AUDIT". exact I. Qed.']
    lines += [f'Print Assumptions port_{n}_source_R_exact.' for n in range(len(outputs))]
    lines += [f'Print Assumptions port_{n}_ready_source_matches_read.' for n in range(len(outputs))]
    if include_history:
        lines += ['Print Assumptions source_from_original_history.',
                  'Print Assumptions source_from_indexed_address.',
                  'Print Assumptions source_from_computed_prefix.']
        lines += ['Print Assumptions computed_operand_R_reduction.',
                  'Print Assumptions computed_operand_R_missing_token.',
                  'Print Assumptions computed_operand_R_matches_requirement.']
        lines += [f'Print Assumptions port_{n}_source_R_from_history.' for n in range(len(outputs))]
    return '\n'.join(lines)+'\n'


def audit(log, count, closed=0):
    pieces = log.split('\nSOURCE_REFERENCE_AUDIT\n')
    if len(pieces) != 2:
        return False
    names = [name for name in re.findall(r'^([A-Za-z_][\w.]*)\s*:', pieces[1], re.M)
             if name != 'Axioms']
    return (pieces[1].count('Axioms:') == count and
            pieces[1].count('Closed under the global context') == closed and
            names == ['FunctionalExtensionality.functional_extensionality_dep'] * count)


def check(ast_path, ast_module, provider, output, isa_provider=None):
    provider, output = Path(provider), Path(output)
    ast, binding, paths = origin.raw_binding(ast_path, ast_module)
    analysis, _ = routes.analyze(ast)
    expected = routes.ports.render(binding['ast'], ast, analysis, opaque_single=True)
    expected += routes.requirement_source(binding['ast']['program'], analysis['ports'])
    previous = json.loads((provider/'report.json').read_text())
    if not (previous.get('coqc_exit') == 0 and previous.get('coqchk_exit') == 0
            and previous.get('source_sha256') == hashlib.sha256(expected.encode()).hexdigest()
            and (provider/'OperandRoutes.v').read_text() == expected
            and (provider/'OperandRoutes.vo').is_file()
            and routes.audit_requirements((provider/'coqc.log').read_text(), len(analysis['ports']))):
        raise ValueError('successful unchanged raw-AST output equations required')
    if not analysis['ports']:
        raise ValueError('no outputs: cannot accept an empty proof')
    output.mkdir(parents=True, exist_ok=False)
    import cpu_isa_input_certificate as isa_inputs
    scope=scopes.for_input(ast_path,ast_module)
    if isa_provider is None:
        isa_provider=output/'isa-inputs'
        isa_inputs.run(isa_provider,scope)
    isa_provider=Path(isa_provider)
    _,isa_source=isa_inputs.render((origin.ROOT/'dep/riscv-coq/src/riscv/Spec/ExecuteI.v').read_text(),scope)
    isa_report=json.loads((isa_provider/'report.json').read_text())
    if not(isa_report.get('accepted') and isa_report.get('coqc_exit')==0 and isa_report.get('coqchk_exit')==0
        and isa_report.get('source_sha256')==hashlib.sha256(isa_source.encode()).hexdigest()
        and (isa_provider/'ISAInputs.v').read_text()==isa_source
        and (isa_provider/'ISAInputs.vo').is_file()
        and isa_inputs.assumptions_expected((isa_provider/'coqc.log').read_text())):
        raise ValueError('checked original ISA input provider with matching scope required')
    source = f'Require Import {ast_module}.\n' + render(binding['ast']['program'], analysis['ports'],include_history=True)
    path = output/'SourceRequirements.v'
    path.write_text(source)
    report = dict(accepted=False, old_inv_read=False, complete_R_generated=False,
        hardware_token_binding_proved=False, operand_freshness_proved=False,
        source_role_selection_proved=False,
        reachable_source_requirements_proved=False,
        conditional_original_read_correspondence_generated=True,
        conditional_original_read_correspondence_proved=False,
        current_instruction_success_required_for_history_entry=False,
        decoded_register_bounds_proved=False,
        indexed_address_to_reference_read_proved=False,
        computed_reference_cut_connection_proved=False,
        executable_reference_R_generated=True,
        provider=str(provider.resolve()), ast_sha256=ast['source_sha256'],
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        generated_relations=len(analysis['ports']),
        history_connections_generated=len(analysis['ports']),instruction_scope=scope,
        ready_selector_connections_generated=len(analysis['ports']),
        ready_selector_connections_proved=False,
        isa_provider=str(isa_provider.resolve()),
        remaining_obligations=['current hardware token and source address identity',
            'output is used as this source under the actual instruction/control conditions',
            'original ISA history at the exact older prefix', 'physical RF related to committed state',
            'actual selected source satisfies generated condition',
            'hardware slots match original ISA operations in age order, including readiness',
            'actual selector expression equals ready-slot resolution',
            'initialization and cycle preservation'])
    flags = list(origin.pending.rtl.framework.FLAGS)
    for row in paths:
        flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(provider.resolve()), 'GeneratedOperandRoutes',
              '-R', str(output.resolve()), 'GeneratedSourceRequirements']
    flags += ['-R',str(isa_provider.resolve()),'GeneratedISAInputs']
    start = time.monotonic()
    deadline = start+1200
    c, timed = run_stage([str(origin.ROOT/'_opam/bin/coqc'), '-time', *flags, str(path.resolve())],
                        output/'coqc.log', deadline-time.monotonic())
    report.update(coqc_exit=c.returncode, coqc_timed_out=timed)
    if c.returncode == 0 and time.monotonic() < deadline:
        report['original_assumptions_only'] = audit(c.stdout, 3*len(analysis['ports'])+6)
        k, timed = run_stage([str(origin.ROOT/'_opam/bin/coqchk'), '-silent', *flags,
            '-norec', 'GeneratedSourceRequirements.SourceRequirements'],
            output/'coqchk.log', deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode, coqchk_timed_out=timed,
            accepted=k.returncode == 0 and report['original_assumptions_only'])
        report['conditional_original_read_correspondence_proved'] = report['accepted']
        report['ready_selector_connections_proved'] = report['accepted']
        report['decoded_register_bounds_proved'] = report['accepted']
        report['indexed_address_to_reference_read_proved'] = report['accepted']
        report['computed_reference_cut_connection_proved'] = report['accepted']
    report['seconds'] = time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    for name in ['ast', 'ast-module', 'provider', 'output']:
        p.add_argument('--'+name, required=True)
    p.add_argument('--isa-provider')
    a = p.parse_args()
    result = check(a.ast, a.ast_module, a.provider, a.output,a.isa_provider)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['accepted'] else 1)
