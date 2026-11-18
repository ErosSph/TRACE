"""Generate raw RTL read-port clauses for the ISA-driven R frontier.

The architectural cut is explicit. This proves actual sampled read values
from a bank relation at that cut; instruction age/forwarding remain obligations.
No old CPU invariant, selected port profile or source theorem is read.
"""
import argparse
import hashlib
import json
import re
import time
from pathlib import Path
import cpu_pending_origins as origin
import cpu_rf_read_ports as ports
import cpu_rf_view_expression as views
from cpu_certificate_acceptance import run_stage


def original_isa_source(plan):
    lines=['From Coq Require Import List ZArith.',
        f'Require Import {plan["ast_module"]}.',
        'Require Import GeneratedOperandClauses.OperandClauses Ex.External.CPUOriginalISAReference',
        ' Ex.External.CPUReferenceCuts Ex.External.CPUGeneratedJointTemplate Ex.External.CPURegisterEffectRelation',
        ' Lang.ExtendedSV Lang.ExtendedSVRegisterBank Ex.RvCore.FormalSpec coqutil.Map.Interface coqutil.Word.Interface',
        ' coqutil.Word.Bitwidth coqutil.Byte riscv.Utility.Utility.',
        'Import ExtendedSV ExtendedSVRegisterBank CPUReferenceCuts CPUGeneratedJointTemplate CPURegisterEffectRelation CPUOriginalISAReference.',
        'Section OriginalReference.',
        'Context {word:Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}.',
        'Context {Registers:map.map Z word}{Mem:map.map word byte}.']
    for n in range(len(plan['ports'])):
        lines += [f'Definition operand_{n}_isa_clause {{Token:Type}}(token_pc token_word:Token->Z)',
            ' initial pending index token fixed :=',
            f' operand_{n}_pending_clause(instruction_effect token_pc token_word)initial pending index token fixed.',
            f'Theorem operand_{n}_at_original_cut {{Token:Type}}(token_pc token_word:Token->Z)',
            ' initial pending frontier index token seed fixed:',
            ' EffectChain(instruction_effect token_pc token_word)initial pending frontier ->',
            ' nth_error pending index=Some token ->',
            f' CombLFP {plan["program"]} seed fixed ->',
            ' (forall before,BeforeInstruction token_pc token_word initial pending index token before ->',
            f' RegisterRelated(lane_read 32(read_signal fixed {plan["bank"]}))before) ->',
            f' operand_{n}_isa_clause token_pc token_word initial pending index token fixed.',
            f'Proof. exact(operand_{n}_at_pending_cut(instruction_effect token_pc token_word)',
            ' initial pending frontier index token seed fixed). Qed.']
    lines+=['End OriginalReference.']
    for n in range(len(plan['ports'])):
        lines += [f'Goal True. idtac "R_ORIGINAL_ISA_CUT_{n}". exact I. Qed.',
            f'Print Assumptions operand_{n}_at_original_cut.']
    return '\n'.join(lines)+'\n'


def audit_original_isa(log, count):
    markers=list(re.finditer(r'^R_ORIGINAL_ISA_CUT_(\d+)\s*$',log,re.M))
    if [int(m[1])for m in markers]!=list(range(count)) or not count:return False
    for n,m in enumerate(markers):
        segment=log[m.end():markers[n+1].start() if n+1<len(markers)else len(log)]
        names=[name for name in re.findall(r'^([A-Za-z_][\w.]*)\s*:',segment,re.M) if name!='Axioms']
        if names!=['FunctionalExtensionality.functional_extensionality_dep'] or segment.count('Axioms:')!=1:
            return False
    return True


def render(ast_path, ast_module):
    ast, profile, paths = origin.raw_binding(ast_path, ast_module)
    analysis = ports.analyze(ast)
    roots = {site['root']: site['total'] for site in views.reads.analyze(ast)['sites']}
    if analysis['residuals'] or len(roots) != 1 or not analysis['ports']:
        raise ValueError('complete single-bank read support required; no dropped ports')
    root, total = next(iter(roots.items()))
    program = profile['ast']['program']
    source = ports.render(profile['ast'], ast, analysis)
    lines = ['Require Import Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankReadExpression',
             ' Ex.External.CPURegisterEffectRelation Ex.External.CPURegisterReadExpression',
             ' Ex.RvCore.FormalSpec Ex.External.CPUReferenceCuts Ex.External.CPUGeneratedJointTemplate',
             ' coqutil.Map.Interface coqutil.Word.Interface coqutil.Byte.',
             'Import ExtendedSVRegisterBank ExtendedSVBankReadExpression CPURegisterEffectRelation CPURegisterReadExpression CPUReferenceCuts CPUGeneratedJointTemplate.']
    for n, port in enumerate(analysis['ports']):
        expr, proof = views.lower(port['rhs'], root, total)
        w, out = port['width'], port['output_root']
        lines += [f'Definition operand_{n}_view(s:State)(view:Z->Z):Expr:={expr}.',
            f'Lemma operand_{n}_expression s view(HR:BankRelated 32 32(read_signal s {root})view):',
            f' ValueEquivalent s port_{n}_rhs(operand_{n}_view s view).',
            f'Proof. exact {proof}. Qed.',
            f'Section Operand{n}.',
            'Context {word:Interface.word 32}{Registers:map.map Z word}{Mem:map.map word byte}.',
            f'Definition operand_{n}_clause(s:State)(before:FormalSpec.State):Prop:=',
            f' norm {w}(read_signal s {out})=norm {w}(eval_expr s(operand_{n}_view s',
            f' (PhysicalZeroISAView(read_signal s {root})before))).',
            f'Theorem operand_{n}_from_actual_read seed fixed(before:FormalSpec.State):',
            f' CombLFP {program} seed fixed ->',
            f' RegisterRelated(lane_read 32(read_signal fixed {root}))before ->',
            f' operand_{n}_clause fixed before.',
            f'Proof. intros HL HR;unfold operand_{n}_clause;rewrite(port_{n}_lfp seed fixed HL).',
            f' exact(f_equal(norm {w})(proj2(operand_{n}_expression fixed _',
            ' (register_related_physical_view _ before HR)))). Qed.',
            f'Definition operand_{n}_pending_clause {{Token:Type}}',
            ' (effect:Token->FormalSpec.State->option FormalSpec.State) initial pending index token fixed : Prop:=',
            f' exists before,BeforeToken effect initial pending index token before /\\operand_{n}_clause fixed before.',
            f'Theorem operand_{n}_at_pending_cut {{Token:Type}}',
            ' (effect:Token->FormalSpec.State->option FormalSpec.State) initial pending frontier index token seed fixed:',
            ' EffectChain effect initial pending frontier ->nth_error pending index=Some token ->',
            f' CombLFP {program} seed fixed ->',
            ' (forall before,BeforeToken effect initial pending index token before ->',
            f' RegisterRelated(lane_read 32(read_signal fixed {root}))before) ->',
            f' operand_{n}_pending_clause effect initial pending index token fixed.',
            'Proof. intros HC HT HL HR;',
            ' destruct(token_before_exists effect initial pending frontier index token HC HT)as[before HB];',
            f' exists before;split;[exact HB|exact(operand_{n}_from_actual_read seed fixed before HL(HR before HB))]. Qed.',
            f'End Operand{n}.', f'Print Assumptions operand_{n}_from_actual_read.',
            f'Print Assumptions operand_{n}_at_pending_cut.']
    return dict(ast_sha256=ast['source_sha256'], program=program, ast_module=ast_module, bank=root,
        ports=[dict(output=p['output_root'], process=p['process'], width=p['width'],
                    expression=origin.pending.rtl.render(p['rhs'])) for p in analysis['ports']],
        old_inv_read=False, architectural_cut='explicit caller-supplied ISA state; not inferred token age',
        physical_zero_lane_retained=True, operand_freshness_proved=False), source+'\n'+'\n'.join(lines)+'\n', paths


def check(ast_path, ast_module, output):
    output = Path(output); output.mkdir(parents=True, exist_ok=False)
    start = time.monotonic(); deadline = start+1200
    report = dict(accepted=False, goal_complete=False, old_inv_read=False,
        operand_freshness_proved=False, full_R_preservation_proved=False)
    try:
        plan, source, paths = render(ast_path, ast_module)
    except ValueError as exc:
        report['residual'] = str(exc)
        (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
        return report
    (output/'plan.json').write_text(json.dumps(plan, indent=2)+'\n')
    path = output/'OperandClauses.v'; path.write_text(source)
    flags = list(origin.pending.rtl.framework.FLAGS)
    for row in paths: flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(output.resolve()), 'GeneratedOperandClauses']
    c, timed = run_stage([str(origin.ROOT/'_opam/bin/coqc'), '-time', *flags, str(path.resolve())],
                        output/'coqc.log', max(0.1,deadline-time.monotonic()))
    report.update(coqc_exit=c.returncode, coqc_timed_out=timed,
                  source_sha256=hashlib.sha256(source.encode()).hexdigest(), ports=len(plan['ports']))
    if c.returncode == 0:
        # Physical read, ISA read, and the token-indexed reference cut.
        report['assumptions_closed'] = c.stdout.count('Closed under the global context') == 3*len(plan['ports']) and 'Axioms:' not in c.stdout
        if time.monotonic() < deadline:
            k, timed = run_stage([str(origin.ROOT/'_opam/bin/coqchk'), '-silent', *flags,
                '-norec', 'GeneratedOperandClauses.OperandClauses'], output/'coqchk.log', deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode, coqchk_timed_out=timed,
                          accepted=k.returncode == 0 and report['assumptions_closed'])
    if report['accepted'] and time.monotonic()<deadline:
        isa_path=output/'OperandISACuts.v';isa_source=original_isa_source(plan)
        isa_path.write_text(isa_source)
        c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(isa_path.resolve())],
            output/'isa-cuts.coqc.log',deadline-time.monotonic())
        item=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,
            source_sha256=hashlib.sha256(isa_source.encode()).hexdigest(),
            inherited_assumption='original run1 functional_extensionality_dep')
        if c.returncode==0 and time.monotonic()<deadline:
            item['assumptions_expected']=audit_original_isa(c.stdout,len(plan['ports']))
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedOperandClauses.OperandISACuts'],output/'isa-cuts.coqchk.log',deadline-time.monotonic())
            item.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                accepted=k.returncode==0 and item['assumptions_expected'])
        report['original_isa_reference']=item
        report['accepted']=item['accepted']
    elif report['accepted']:
        report['accepted']=False
        report['original_isa_reference']=dict(accepted=False,status='budget_exhausted_before_required_ISA_check')
    report['seconds'] = time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    for arg in ['ast', 'ast-module', 'output']: p.add_argument('--'+arg, required=True)
    a = p.parse_args(); result = check(a.ast, a.ast_module, a.output)
    print(json.dumps(result, indent=2)); raise SystemExit(0 if result['accepted'] else 1)
