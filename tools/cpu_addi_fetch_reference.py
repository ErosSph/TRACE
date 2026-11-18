"""Actual recorded ADDI fetch to unchanged ISA run1, registers and frontier.

The existing checked physical ROM/fetch theorem is reused at its exact source,
object, AST and CDFG identities. No success or CPU invariant is assumed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_cdfg_fetch_reference as fetch
import cpu_add_admission_write as admission
from cpu_certificate_acceptance import run_stage, parse_assumptions, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports

NS = 'GeneratedAddiFetchReference'
RULE = 'CPUOriginalADDIFetchRules'
EXPORTS = ['recorded_addi_executes_original_isa', 'recorded_addi_frontier', 'recorded_addi_step']
SHARED = ['original_addi_run1_total', 'original_addi_execution_frame']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def render(plan):
    original = fetch.render(plan)
    header = original[:original.index('Module R:=')]
    header += '''Require Import GeneratedFetchReference.FetchReference
 Ex.External.CPUOriginalADDIFetchRules Ex.External.CPUISAExecutionEffects
 Ex.External.CPUISAInstructionExecution Ex.External.CPUISAAddiEffects
 Ex.External.CPUOriginalADDFrontier Ex.External.CPUISARegisterUpdate Ex.External.CPURegisterEffectRelation.
Import CPUISAExecutionEffects CPUISAInstructionExecution CPUOriginalADDFrontier
 CPUISARegisterUpdate CPURegisterEffectRelation.
Module F:=GeneratedFetchReference.FetchReference.
Import F.
Local Open Scope Z_scope.
'''
    context = original[original.index('Section OriginalISA.'):original.index('Theorem recorded_word_matches_original_memory')]
    theorem = original[original.index('Theorem recorded_add_executes_original_isa'):original.index('End OriginalISA.')]
    theorem = theorem.replace('recorded_add_executes_original_isa', 'recorded_addi_executes_original_isa')
    theorem = theorem.replace('Decode.Add ', 'Decode.Addi ').replace('rs2', 'imm')
    theorem = re.sub(r' pose proof\(CPUISADecodeInputs.second_register_field[\s\S]*?as Himm\.\n', '', theorem)
    theorem = re.sub(r' assert\(HimmBound:[\s\S]*? \}\n', '', theorem)
    theorem = theorem.replace('rs1[imm]HD', 'rs1[]HD')
    theorem = theorem.replace('CPUOriginalInstructionSuccess.original_add_run1_total', RULE+'.original_addi_run1_total')
    theorem = theorem.replace(' Hrs1Bound HimmBound)', ' Hrs1Bound)')
    post = '''Definition AddiPost(before after:FormalSpec.State)rd rs imm:=
 getPc after=getNextPc before /\\
 getNextPc after=word.add(getPc after)(word.of_Z 4) /\\
 getInstMem after=getInstMem before /\\getDataMem after=getDataMem before /\\
 exists x,Machine.getRegister rs before=(Some x,before) /\\
 ISAProjectedRegisterEffects before after(register_operations rd(Utility.add x(Utility.ZToReg imm))).

Theorem recorded_addi_frontier token(before after:FormalSpec.State)rd rs imm:
 CPUOriginalISAReference.instruction_effect recorded_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi rd rs imm) ->
 AddiPost before after rd rs imm.
Proof. intros HS HD.
 destruct(token_execute recorded_pc token_word token before after(Decode.Addi rd rs imm)HS HD)
 as[middle[HX HE]].
 destruct(CPUOriginalADDIFetchRules.original_addi_execution_frame before middle rd rs imm HX)
 as[HPC[HN[HI HM]]].
 destruct(original_end_cycle_frontier middle after HE)as[HP[HNext[HInst HData]]].
 destruct(CPUISAAddiEffects.original_addi_effect before middle rd rs imm HX)as[x[HRead HRegs]].
 unfold AddiPost;refine(conj(eq_trans HP HN)(conj
 (eq_trans HNext(f_equal(fun value=>word.add value(word.of_Z 4))(eq_sym HP)))
 (conj(eq_trans HInst HI)(conj(eq_trans HData HM)_)))).
 exists x;split;[exact HRead|].
 intros address HA;unfold ISAView;rewrite(end_cycle_register_frame middle after HE).
 exact(HRegs address HA).
Qed.
'''
    step = theorem[:theorem.index('Proof.')]
    step = step.replace('recorded_addi_executes_original_isa', 'recorded_addi_step')
    step = step.replace(' FormalSpec.run1 before=(Some tt,after).',
                        ' FormalSpec.run1 before=(Some tt,after) /\\ AddiPost before after rd rs1 imm.')
    step += '''Proof. intros HW HL HC HI HO HE HT HP HA HM HD.
 destruct(recorded_addi_executes_original_isa words events token before i rd rs1 imm
 HW HL HC HI HO HE HT HP HA HM HD)as[after[HS HR]].
 exists after;split;[exact HS|];split;[exact HR|exact(recorded_addi_frontier token before after rd rs1 imm HS HD)].
Qed.
'''
    source = header+context+theorem+post+step+'End OriginalISA.\n'
    source += 'Goal True. idtac "ADDI_FETCH_REFERENCE_AUDIT". exact I. Qed.\n'
    source += ''.join('Print Assumptions '+name+'.\n' for name in EXPORTS)
    return source, header, context


def declaration(source, name):
    m = re.search(r'(?m)^(?:Lemma|Theorem)\s+'+re.escape(name)+r'\s*([\s\S]*?)\.\s*Proof\.', source)
    if not m:
        raise ValueError('missing explicit declaration '+name)
    text = m.group(1)
    depth = 0
    for index, char in enumerate(text):
        if char in '({[': depth += 1
        if char in ')}]': depth -= 1
        if char == ':' and depth == 0:
            return 'forall '+text[:index].strip()+',\n'+text[index+1:]
    raise ValueError('unsupported declaration '+name)


def check(config, output, reuse_rules=None):
    out = Path(output);out.mkdir(parents=True, exist_ok=False)
    base = json.loads(Path('framework/bzeeno-cdfg-add-inputs.json').read_text())
    if any(config[k] != base[k] for k in ['ast', 'ast_module', 'graph', 'history']):
        raise ValueError('different original ADDI/source/ROM configuration')
    config = dict(base, **config)
    graph = fetch.cdfg.checked_graph(config['graph'], config['ast'], out/'replayed')
    raw, _, _ = fetch.cdfg.raw_binding(config['ast'], config['ast_module'])
    plan = fetch.discover(raw, graph)
    if (plan['capacity'], plan['offset_width']) != (101, 12):
        raise ValueError('original ROM101/offset12 configuration required')
    fp = Path(config['fetch_reference']);fr = json.loads((fp/'report.json').read_text())
    if not (fr['accepted'] and fr['coqc_exit'] == fr['coqchk_exit'] == 0
            and fr['assumptions_audit_passed'] and fr['ast_sha256'] == raw['source_sha256']
            and fr['graph_sha256'] == digest(config['graph'])
            and fr['source_sha256'] == digest(fp/'FetchReference.v')
            and fr['object_sha256'] == digest(fp/'FetchReference.vo')):
        raise ValueError('same-object physical recorded fetch certificate required')
    paths = json.loads((fp/'providers.json').read_text())
    paths.append(dict(namespace='GeneratedFetchReference', directory=str(fp.resolve())))
    paths = list({(p['namespace'], p['directory']):p for p in paths}.values())
    paths.sort(key=lambda p:len(Path(p['directory']).parts))
    environment = admission.verify_environment_paths(paths)
    flags = list(fetch.rom.rtl.framework.FLAGS)
    for p in paths: flags += ['-R', p['directory'], p['namespace']]
    flags += ['-R', str(out.resolve()), NS]
    (out/'providers.json').write_text(json.dumps(paths, indent=2)+'\n')
    (out/'plan.json').write_text(json.dumps(plan, indent=2)+'\n')
    baseline = out/'Baseline.v'
    baseline.write_text('Require Import Ex.External.CPUISAInstructionExecution.\n'
                       'Goal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\n'
                       'Print Assumptions CPUISAInstructionExecution.token_execute.\n')
    bc, bt = run_stage(['_opam/bin/coqc', *flags, str(baseline)], out/'baseline.log', 1200)
    allowed = parse_assumptions(bc.stdout) if bc.returncode == 0 else set()
    if bc.returncode != 0 or allowed != set(fr['baseline_assumptions']) or allowed-ALLOWED_AXIOMS:
        raise ValueError('original reference assumption baseline changed')
    report = dict(accepted=False, baseline_coqc_exit=bc.returncode, baseline_assumptions=sorted(allowed),
                  old_inv_read=False, complete_R_generated=False, infinite_itree_refinement_proved=False,
                  ast_sha256=raw['source_sha256'], graph_sha256=digest(config['graph']),
                  original_environment_input_hashes=environment, physical_fetch_provider=str(fp.resolve()), stages={})
    target = fetch.cdfg.ROOT/('src/Ex/External/'+RULE+'.v')
    source, header, context = render(plan)
    file = out/'AddiFetchReference.v';file.write_text(source)
    units = [('shared', target, 'Pfv.Ex.External.'+RULE, 2),
             ('fetch', file, NS+'.AddiFetchReference', 3)]
    if reuse_rules:
        old = json.loads((Path(reuse_rules)/'report.json').read_text())['stages']['shared']
        if not(old['accepted'] and old['coqc_exit'] == old['coqchk_exit'] == 0
               and old['source_sha256'] == digest(target) and old['object_sha256'] == digest(target.with_suffix('.vo'))
               and not(set(old['assumptions'])-allowed)):
            raise ValueError('unchanged accepted ADDI shared rules required')
        report['stages']['shared'] = dict(old, reused_from=str(Path(reuse_rules).resolve()))
        units = units[1:]
    start = time.monotonic()
    for stage, path, module, count in units:
        stage_start = time.monotonic()
        cc, ct = run_stage(['/usr/bin/time', '-v', '-o', str((out/(stage+'.coqc.resources')).resolve()),
                            '_opam/bin/coqc', '-time', *flags, str(path)], out/(stage+'.coqc.log'), 1200)
        row = dict(accepted=False, coqc_exit=cc.returncode, coqc_timed_out=ct, source_sha256=digest(path))
        report['stages'][stage] = row
        if cc.returncode: break
        ax = audit_all_exports(cc.stdout.split('ADDI_FETCH_REFERENCE_AUDIT')[-1] if stage == 'fetch' else cc.stdout, count)
        kk, kt = run_stage(['/usr/bin/time', '-v', '-o', str((out/(stage+'.coqchk.resources')).resolve()),
                            '_opam/bin/coqchk', '-silent', *flags, '-norec', module], out/(stage+'.coqchk.log'),
                            max(.1, 1200-(time.monotonic()-stage_start)))
        row.update(coqchk_exit=kk.returncode, coqchk_timed_out=kt, assumptions=sorted(ax),
                   assumptions_audit_passed=not(ax-allowed), accepted=kk.returncode == 0 and not(ax-allowed),
                   object_sha256=digest(path.with_suffix('.vo')))
        if not row['accepted']: break
    else:
        # Literal declared types are checked independently, not inferred Check.
        shared_source = target.read_text()
        shared_header = shared_source[:shared_source.index('Module '+RULE+'.')]
        shared_context = shared_source[shared_source.index('Section ISA.'):shared_source.index('Theorem original_addi_run1_total')]
        audit = shared_header+'Require Import Ex.External.'+RULE+'.\nImport '+RULE+'.\n'+shared_context
        for name in SHARED:
            audit += 'Definition exact_'+name+' : '+declaration(shared_source, name)+' := '+RULE+'.'+name+'.\n'
        audit += 'End ISA.\n'+header+'Require Import '+NS+'.AddiFetchReference.\nImport AddiFetchReference.\n'+context
        for name in EXPORTS:
            audit += 'Definition exact_'+name+' : '+declaration(source, name)+' := AddiFetchReference.'+name+'.\n'
        audit += 'End OriginalISA.\nGoal True. idtac "EXACT_ADDI_FETCH_TYPE_AUDIT". exact I. Qed.\n'
        audit += ''.join('Print Assumptions exact_'+name+'.\n' for name in SHARED+EXPORTS)
        af = out/'ExactTypeAudit.v';af.write_text(audit)
        ac, at = run_stage(['_opam/bin/coqc', '-time', *flags, str(af)], out/'exact-type-audit.coqc.log', 1200)
        report['exact_type_audit'] = dict(accepted=False, coqc_exit=ac.returncode, coqc_timed_out=at,
                                         expected_explicit_mappings=5, source_sha256=digest(af))
        if ac.returncode == 0:
            ax = audit_all_exports(ac.stdout.split('EXACT_ADDI_FETCH_TYPE_AUDIT')[-1], 5)
            ak, akt = run_stage(['_opam/bin/coqchk', '-silent', *flags, '-norec', NS+'.ExactTypeAudit'],
                                out/'exact-type-audit.coqchk.log', 1200)
            report['exact_type_audit'].update(coqchk_exit=ak.returncode, coqchk_timed_out=akt,
                assumptions=sorted(ax), accepted=ak.returncode == 0 and not(ax-allowed))
            report['accepted'] = report['exact_type_audit']['accepted']
    report.update(seconds=time.monotonic()-start, source_sha256=digest(file),
                  actual_recorded_ADDI_run1_success_proved=report['accepted'],
                  original_ADDI_PC_ROM_RAM_register_effects_proved=report['accepted'])
    if report['stages'].get('fetch', {}).get('accepted'):
        report.update(coqc_exit=0, coqchk_exit=0, assumptions_audit_passed=True,
                      object_sha256=digest(file.with_suffix('.vo')))
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--inputs', required=True);p.add_argument('--output', required=True);p.add_argument('--reuse-rules')
    a = p.parse_args()
    try:
        r = check(json.loads(Path(a.inputs).read_text()), a.output, a.reuse_rules)
    except Exception as error:
        out = Path(a.output)
        if out.is_dir() and not(out/'report.json').exists():
            (out/'report.json').write_text(json.dumps(dict(accepted=False, stage='preflight', error=str(error), cli_exit=1), indent=2)+'\n')
        raise
    print(json.dumps(r, indent=2));raise SystemExit(0 if r['accepted'] else 1)
