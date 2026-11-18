"""Checked scalar selection from original multi-output blocking controllers.

No instruction roles or old CPU invariant are inputs. The output is a hardware
equation; correspondence to pending token age remains a separate obligation.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
import cpu_pending_origins as origin
import cpu_tagged_instruction_fields as tagged
import cpu_operand_branch_proofs as branches
from cpu_certificate_acceptance import run_stage
rtl = origin.pending.rtl


def discover(ast):
    """Follow original operand mux selector wires to their unique producers."""
    selected, residuals = {}, []
    processes = {p['name']: p for p in ast['processes']}
    branch_plan = branches.discover(ast)
    for mux in branch_plan['selected']:
        body = branches.cases.unwrap(processes[mux['process']]['body'])
        selector = body.args[0]
        if selector.name != 'EVar':
            residuals.append(dict(mux=mux['process'], reason='non-variable selector')); continue
        root = int(selector.args[1].name); seen = set(); path=[]
        while root not in seen:
            seen.add(root)
            writers=[p for p in ast['processes'] if root in p['writers']]
            if len(writers)!=1:
                residuals.append(dict(mux=mux['process'],root=root,reason='not one writer')); break
            proc=writers[0]; path.append(dict(root=root,process=proc['name']))
            simple=branches.cases.unwrap(proc['body'])
            if proc['kind']=='Combinational' and simple.name=='SAssign' and \
               simple.args[0].name=='false' and simple.args[1].name=='EVar' and \
               simple.args[2].name=='LVar':
                root=int(simple.args[1].args[1].name); continue
            try:
                _,_,width,inputs,expr=proposal(proc,root)
            except ValueError as exc:
                residuals.append(dict(mux=mux['process'],root=root,reason=str(exc))); break
            key=(proc['name'],root)
            selected.setdefault(key,dict(process=proc['name'],root=root,width=width,
                inputs=inputs,expression=rtl.render(expr),paths=[]))['paths'].append(path)
            break
        else:
            residuals.append(dict(mux=mux['process'],root=root,reason='selector alias cycle'))
    return dict(selected=list(selected.values()),residuals=residuals,
        upstream_route_residuals=branch_plan['residuals'],
        old_inv_read=False, token_freshness_proved=False)


def snapshot_plan(st):
    T = rtl.Term
    n, a = st.name, st.args
    if n == 'SSkip': return T('NEmpty')
    if n == 'SAssign':
        if a[0].name != 'false' or a[2].name != 'LVar':
            raise ValueError('requires whole-scalar blocking writes')
        return T('NAssign', a[1:])
    if n == 'SSeq':
        return T('NSeq', (T('list', tuple(snapshot_plan(x) for x in a[0].args)),))
    if n == 'SIf': return T('NIf', (a[0], snapshot_plan(a[1]), snapshot_plan(a[2])))
    if n == 'SCase':
        return T('NCase',(a[0],T('list',tuple(T('pair',(arm.args[0],snapshot_plan(arm.args[1])))
            for arm in a[1].args))))
    raise ValueError('unknown snapshot statement')


def proposal(proc, root):
    if proc['kind'] != 'Combinational': raise ValueError('not combinational')
    body = tagged.output_slice(proc['body'], root)
    plan = snapshot_plan(body)
    writes = [n for n in rtl.walk(body) if n.name == 'SAssign']
    if not writes: raise ValueError('output not written')
    widths = {int(n.args[2].args[0].name) for n in writes}
    if len(widths) != 1: raise ValueError('inconsistent output widths')
    width = next(iter(widths))
    inputs = sorted({int(n.args[1].name) for n in rtl.walk(body) if n.name == 'EVar'})
    if root in inputs: raise ValueError('blocking self-read requires sequential substitution')
    original_writes = {rtl.root_of(n.args[2]) for n in rtl.walk(proc['body']) if n.name=='SAssign'}
    if original_writes.intersection(inputs):
        raise ValueError('retained inputs are written by the original process')
    seed = rtl.Term('EVar', (rtl.Term(str(width)), rtl.Term(str(root))))
    expression = origin.expressions.compile_expression(plan, root, width, seed, 64)
    if expression is None: raise ValueError('scalar compilation unsupported')
    return body, plan, width, inputs, expression


def render(ast_path, ast_module, process, root):
    ast, profile, paths = origin.raw_binding(ast_path, ast_module)
    proc = next(p for p in ast['processes'] if p['name'] == process)
    body, plan, width, inputs, expression = proposal(proc, root)
    p = profile['ast']['program']; pn = ast['module'] + '.' + process
    index = [x for x in ast['processes'] if x['kind']=='Combinational'].index(proc)
    roots = '[' + ';'.join(str(x)+'%nat' for x in sorted(set(inputs+[root]))) + ']'
    reads = '[' + ';'.join(str(x)+'%nat' for x in inputs) + ']'
    source = f'''From Coq Require Import ZArith List.
Require Import Lang.ExtendedSV Lang.ExtendedSVOutputSlice Lang.ExtendedSVBlocking
 Lang.ExtendedSVBlockingScalarExpression Lang.ExtendedSVBlockingSnapshot
 Lang.ExtendedSVScalarExpression Lang.ExtendedSVAutoAdapterPlan
 Lang.ExtendedSVAutoAdapterEffects Lang.ExtendedSVExpressionBinding {ast_module}.
Import ListNotations ExtendedSV ExtendedSVOutputSlice ExtendedSVBlocking
 ExtendedSVBlockingScalarExpression ExtendedSVBlockingSnapshot
 ExtendedSVScalarExpression ExtendedSVAutoAdapterPlan ExtendedSVAutoAdapterEffects
 ExtendedSVExpressionBinding.
Definition selector_body : Stmt := {rtl.render(body)}.
Definition selector_plan : NbPlan := {rtl.render(plan)}.
Definition selector_expression : Expr := {rtl.render(expression)}.
Definition selector_proc := sliced_process {p} [{root}%nat] {pn}.
Lemma selector_slice : process_body selector_proc = selector_body.
Proof. vm_compute. reflexivity. Qed.
Lemma selector_safe : output_slice_safeb (statement_fuel {p})
 [{root}%nat] {roots} (process_body {pn}) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma original_blocking : blocking_onlyb (process_body {pn}) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma selector_blocking : blocking_onlyb (process_body selector_proc) = true.
Proof. rewrite selector_slice. vm_compute. reflexivity. Qed.
Lemma selector_compiled : compile_effect (statement_fuel {p})
 (process_body selector_proc) = Some (snapshot_effect 64 selector_plan).
Proof. rewrite selector_slice. vm_compute. reflexivity. Qed.
Lemma selector_snapshot : snapshot_safe 64 {reads} selector_plan = true.
Proof. vm_compute. reflexivity. Qed.
Lemma selector_expression_checked : compile_scalar 64 {root}%nat {width}
 selector_plan (EVar {width} {root}) = Some selector_expression.
Proof. vm_compute. reflexivity. Qed.
Lemma selector_local s : norm {width} (read_signal (run_process {p} s {pn}) {root}) =
 norm {width} (eval_expr s selector_expression).
Proof.
 pose proof (actual_output_slice_process {p} [{root}%nat] {roots} {pn} s
 selector_safe original_blocking selector_blocking {root}%nat) as H.
 assert (HI : In {root}%nat {roots}) by (simpl; tauto).
 rewrite (H HI).
 exact (checked_blocking_scalar_process {p} selector_proc selector_plan {reads}
 {root}%nat {width} 64 64 selector_expression selector_blocking selector_compiled
 selector_snapshot selector_expression_checked s).
Qed.
Definition selector_combs := filter is_comb (processes {p}).
Lemma selector_registered : nth_error selector_combs {index} = Some {pn}.
Proof. vm_compute. reflexivity. Qed.
Lemma selector_binding : expression_bindingb selector_combs {index} {root} selector_expression = true.
Proof. vm_compute. reflexivity. Qed.
Theorem selector_actual_lfp seed fixed : CombLFP {p} seed fixed ->
 norm {width} (read_signal fixed {root}) = norm {width} (eval_expr fixed selector_expression).
Proof. exact (checked_expression_binding {p} selector_combs {index} {pn} {width} {root}
 selector_expression seed fixed eq_refl selector_registered selector_local selector_binding). Qed.
Print Assumptions selector_actual_lfp.
'''
    if any(n.name=='NCase' for n in rtl.walk(plan)):
        source=source.replace('Import ListNotations ExtendedSV',
            'Require Import Lang.ExtendedSVBlockingSnapshotCase.\nImport ListNotations ExtendedSV',1)
        source=source.replace('snapshot_safe 64','ExtendedSVBlockingSnapshotCase.safe 64')
        source=source.replace('checked_blocking_scalar_process ',
            'ExtendedSVBlockingSnapshotCase.scalar_process ')
    return source, paths, dict(process=process, root=root, width=width,
        inputs=inputs, expression=rtl.render(expression), ast_sha256=ast['source_sha256'])


def check(ast_path, ast_module, process, root, output, timeout=1200):
    if not 0 < timeout <= 1200: raise ValueError('budget must be within 20 minutes')
    source, paths, report = render(ast_path, ast_module, process, root)
    output = Path(output); output.mkdir(parents=True, exist_ok=False)
    path = output/'BlockingSelector.v'; path.write_text(source)
    report.update(accepted=False, complete_R_generated=False, token_freshness_proved=False,
        old_inv_read=False, llm_calls=0, source_sha256=hashlib.sha256(source.encode()).hexdigest())
    flags = list(rtl.framework.FLAGS)
    for row in paths: flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(output.resolve()), 'GeneratedBlockingSelector']
    start=time.monotonic(); deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],
        output/'coqc.log',deadline-time.monotonic())
    report.update(coqc_exit=c.returncode,coqc_timed_out=t)
    if c.returncode==0 and time.monotonic()<deadline:
        report['assumptions_closed']=c.stdout.count('Closed under the global context')==1 and 'Axioms:' not in c.stdout
        k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedBlockingSelector.BlockingSelector'],output/'coqchk.log',deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
            accepted=k.returncode==0 and report['assumptions_closed'])
    report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def check_discovered(ast_path,ast_module,output,timeout=1200):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    ast,_,_=origin.raw_binding(ast_path,ast_module)
    plan=discover(ast)
    (output/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    results=[check(ast_path,ast_module,r['process'],r['root'],
        output/(r['process']+'_'+str(r['root'])),timeout) for r in plan['selected']]
    report=dict(accepted=bool(results) and all(r['accepted'] for r in results),
        status='checked' if results else 'no_supported_selector_not_a_completeness_claim',
        results=results,residuals=plan['residuals'],complete_R_generated=False,
        upstream_route_residuals=plan['upstream_route_residuals'],
        token_freshness_proved=False,old_inv_read=False,llm_calls=0)
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']: p.add_argument('--'+name,required=True)
    p.add_argument('--process'); p.add_argument('--root',type=int)
    p.add_argument('--timeout',type=float,default=1200)
    a=p.parse_args()
    if (a.process is None)!=(a.root is None): p.error('--process and --root must be provided together')
    report=(check_discovered(a.ast,a.ast_module,a.output,a.timeout) if a.process is None
        else check(a.ast,a.ast_module,a.process,a.root,a.output,a.timeout))
    print(json.dumps(report,indent=2));raise SystemExit(0 if report['accepted'] else 1)
