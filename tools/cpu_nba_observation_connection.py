"""Checked whole-process NBA expressions at the original combinational LFP.

Retain case order, sampled RHS values and last-assignment wins. Do not turn
combinational NBAs into blocking assignments or execute a replacement CPU.
Both the original process compiler and LFP frame checker must accept in Coq.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_auto_adapter as rtl
import cpu_pending_origins as origin
import cpu_plan_slices as slices
import cpu_scalar_expressions as expressions
from cpu_certificate_acceptance import run_stage


def proposal(proc, root, width):
    if proc['kind'] != 'Combinational':
        raise ValueError('an actual combinational writer is required')
    assignments = [s for s in rtl.walk(proc['body']) if s.name == 'SAssign'
        and rtl.root_of(s.args[2]) == root]
    if not assignments or any(s.args[2].name != 'LVar'
            or int(s.args[2].args[0].name) != width for s in assignments):
        raise ValueError('NBA observation needs consistent whole-scalar writes')
    plan = rtl.plan_of(proc['body'])
    seed = rtl.Term('EVar', (rtl.Term(str(width)), rtl.Term(str(root))))
    expression = expressions.compile_expression(slices.slice_plan(plan, root),
        root, width, seed)
    if expression is None:
        raise ValueError('NBA scalar-expression compiler rejected this body')
    return plan, expression


def render(ast_path, module, process, root, width):
    raw, profile, paths = origin.raw_binding(ast_path, module)
    proc = next(p for p in raw['processes'] if p['name'] == process)
    plan, expression = proposal(proc, root, width)
    program = profile['ast']['program']
    pn = raw['module'] + '.' + process
    index = [p['name'] for p in raw['processes']
        if p['kind'] == 'Combinational'].index(process)
    source = f'''From Coq Require Import List ZArith Bool.
Require Import {module} Lang.ExtendedSV Lang.ExtendedSVAutoAdapterPlan
 Lang.ExtendedSVPlanRootSlice Lang.ExtendedSVScalarExpression Lang.ExtendedSVExpressionBinding.
Import ListNotations ExtendedSV ExtendedSVAutoAdapterPlan ExtendedSVPlanRootSlice
 ExtendedSVScalarExpression ExtendedSVExpressionBinding.
Definition original_plan : NbPlan := {rtl.render(plan)}.
Definition output_expression : Expr := {rtl.render(expression)}.
Lemma compiled : compile_nb (statement_fuel {program}) (process_body {pn})=Some original_plan.
Proof. vm_compute;reflexivity. Qed.
Lemma expression_checked : compile_scalar 512 {root}%nat {width}
 (slice_plan 512 {root}%nat original_plan)(EVar {width} {root})=Some output_expression.
Proof. vm_compute;reflexivity. Qed.
Theorem actual_process s : norm {width}(read_signal(run_process {program} s {pn}){root})=
 norm {width}(eval_expr s output_expression).
Proof. exact(checked_sliced_scalar_process {program} {pn} original_plan {root}%nat {width}
 512 512 output_expression compiled expression_checked s). Qed.
Definition original_combs := filter is_comb(processes {program}).
Lemma registered : nth_error original_combs {index}=Some {pn}.
Proof. vm_compute;reflexivity. Qed.
Lemma connected : expression_bindingb original_combs {index} {root} output_expression=true.
Proof. vm_compute;reflexivity. Qed.
Theorem actual_lfp seed fixed : CombLFP {program} seed fixed ->
 norm {width}(read_signal fixed {root})=norm {width}(eval_expr fixed output_expression).
Proof. exact(checked_expression_binding {program} original_combs {index} {pn} {width}
 {root} output_expression seed fixed eq_refl registered actual_process connected). Qed.
Goal True. idtac "NBA_OBSERVATION_AUDIT". exact I. Qed.
Print Assumptions actual_process.
Print Assumptions actual_lfp.
'''
    return source, paths, dict(ast_sha256=raw['source_sha256'], process=process,
        root=root, width=width, comb_index=index, expression=rtl.render(expression),
        dependencies=sorted({tuple(int(a.name) for a in n.args)
            for n in rtl.walk(expression) if n.name == 'EVar'}),
        old_inv_read=False, complete_R_generated=False, llm_calls=0)


def check(ast_path, module, process, root, width, output, timeout=1200):
    if not 0 < timeout <= 1200:
        raise ValueError('native budget must be <=1200s')
    source, paths, report = render(ast_path, module, process, root, width)
    out = Path(output)
    out.mkdir(parents=True, exist_ok=False)
    path = out / 'NBAObservation.v'
    path.write_text(source)
    flags = list(rtl.framework.FLAGS)
    for row in paths:
        flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(out.resolve()), 'GeneratedNBAObservation']
    start = time.monotonic()
    deadline = start + timeout
    cc, timed = run_stage([str(origin.ROOT/'_opam/bin/coqc'), '-time', *flags,
        str(path.resolve())], out/'coqc.log', timeout)
    report.update(accepted=False, source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        coqc_exit=cc.returncode, coqc_timed_out=timed)
    if cc.returncode == 0 and time.monotonic() < deadline:
        tail = cc.stdout.split('NBA_OBSERVATION_AUDIT')[-1]
        closed = tail.count('Closed under the global context') == 2 and 'Axioms:' not in tail
        kk, timed = run_stage([str(origin.ROOT/'_opam/bin/coqchk'), '-silent', *flags,
            '-norec', 'GeneratedNBAObservation.NBAObservation'], out/'coqchk.log',
            deadline-time.monotonic())
        report.update(coqchk_exit=kk.returncode, coqchk_timed_out=timed,
            assumptions_closed=closed, accepted=closed and kk.returncode == 0)
    report['seconds'] = time.monotonic()-start
    if report['accepted']:
        report['object_sha256'] = hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    for name in ['ast', 'ast-module', 'process', 'output']:
        p.add_argument('--'+name, required=True)
    p.add_argument('--root', required=True, type=int)
    p.add_argument('--width', required=True, type=int)
    a = p.parse_args()
    result = check(a.ast, a.ast_module, a.process, a.root, a.width, a.output)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['accepted'] else 1)
