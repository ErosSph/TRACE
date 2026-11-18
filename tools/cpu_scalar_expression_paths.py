"""Generate checked guard-to-leaf phase equations, without guessing guards.

The inputs are actual AST bindings, not ISA role names. Each exported leaf
requires the real sampled PathHolds and actual writer selection evidence.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import time
import cpu_auto_adapter as adapter
import cpu_scalar_captures as scalar
import cpu_scalar_expressions as expressions
from cpu_certificate_acceptance import run_stage


def leaf_paths(expression, width, max_leaves=256, max_depth=64):
    result=[]
    def visit(e,path):
        if len(path)>max_depth:raise ValueError('expression path depth limit')
        if e.name=='ECond' and int(e.args[0].name)==width:
            visit(e.args[2],path+(True,));visit(e.args[3],path+(False,))
        else:
            result.append((path,e))
            if len(result)>max_leaves:raise ValueError('expression leaf limit')
    visit(expression,())
    return result


def proposal(profile,roots=None):
    ast,residuals,outputs,source,count=expressions.proposal(profile,roots)
    lines=['Require Import Lang.ExtendedSVExpressionPath.',
           'Import ExtendedSVExpressionPath.']
    exports=[]
    program=profile['ast']['program']
    for item in outputs:
        root,width,proc=item['root'],item['width'],item['process']
        for index,(path,leaf) in enumerate(leaf_paths(item['expression'],width)):
            name=f'root_{root}_path_{index}'
            bits='['+'; '.join('true' if b else 'false' for b in path)+']'
            lines += [f'Definition {name}_choices : list bool := {bits}.',
                f'Definition {name}_leaf : Expr := {adapter.render(leaf)}.',
                f'Lemma {name}_checked : expression_path {width} root_{root}_expression',
                f' {name}_choices = Some {name}_leaf.',
                'Proof. vm_compute. reflexivity. Qed.',
                f'Lemma {name}_phase ev pre : changed_signal ev <> {root}%nat ->',
                f' process_matches_states pre (phase_driven_state {program} ev pre)',
                f' {ast["module"]}.{proc} = true ->',
                f' PathHolds (phase_driven_state {program} ev pre)',
                f' root_{root}_expression {name}_choices ->',
                f' norm {width} (read_signal (PhaseSemantics {program} ev pre) {root}%nat) =',
                f' norm {width} (eval_expr (phase_driven_state {program} ev pre) {name}_leaf).',
                'Proof. intros HE HS HP.',
                f' rewrite (root_{root}_expression_phase ev pre HE), HS.',
                f' exact (selected_expression_sound {width} {name}_choices',
                f' root_{root}_expression {name}_leaf _ {name}_checked HP). Qed.',
                f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
                f'Print Assumptions {name}_phase.']
            exports.append(dict(root=root,width=width,path=list(path),
                leaf=adapter.render(leaf),theorem=name+'_phase'))
            count+=1
    return ast,residuals,exports,source+'\n'.join(lines)+'\n',count


def emit_library(profile,destination,roots=None,check=False):
    _,residuals,exports,source,count=proposal(profile,roots)
    if residuals or not exports:raise ValueError('unsupported expression path selection')
    path=Path(destination)
    if check:
        if not path.is_file() or path.read_text()!=source:
            raise ValueError('persistent expression path source differs from generation')
    elif path.exists():raise ValueError('destination exists; use --check-source')
    else:
        path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
    return dict(source=str(path),source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        leaf_equations=len(exports),audited_exports=count,source_matches_generator=True,
        coq_checked=False)


def check_profile(profile,output,roots=None,timeout=1200):
    output=Path(output)
    if output.exists():raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    ast,residuals,exports,source,count=proposal(profile,roots)
    path=output/'ScalarExpressionPaths.v';path.write_text(source)
    report=dict(accepted=False,ast_sha256=ast['source_sha256'],
        generated_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        actual_program=profile['ast']['program'],exports=exports,residuals=residuals,
        audited_exports=count,llm_calls=0,reachable_guards_proved=False,
        global_invariant_synthesized=False)
    if residuals or not exports:report['status']='unsupported_expression_selection'
    else:
        flags=list(adapter.framework.FLAGS)
        for extra in profile.get('coq_load_paths',[]):
            flags+=['-R',extra['directory'],extra['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedExpressionPaths']
        start=time.monotonic()
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(path.resolve())],
            output/'coqc.log',timeout)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
        if c.returncode==0:
            report['assumptions_closed']=scalar.audit_output(c.stdout,count)
            start=time.monotonic()
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedExpressionPaths.ScalarExpressionPaths'],output/'coqchk.log',timeout)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                coqchk_seconds=time.monotonic()-start)
            report['accepted']=report['assumptions_closed'] and k.returncode==0
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile',type=Path,required=True)
    target=p.add_mutually_exclusive_group(required=True)
    target.add_argument('--output',type=Path)
    target.add_argument('--emit-source',type=Path)
    p.add_argument('--check-source',action='store_true')
    p.add_argument('--roots',type=int,nargs='+')
    p.add_argument('--timeout',type=float,default=1200)
    a=p.parse_args()
    if not 0<a.timeout<=1200:p.error('timeout must be positive and at most1200 seconds')
    profile=json.loads(a.profile.read_text())
    if a.emit_source:result=emit_library(profile,a.emit_source,a.roots,a.check_source)
    else:
        if a.check_source:p.error('--check-source requires --emit-source')
        result=check_profile(profile,a.output,a.roots,a.timeout)
    print(json.dumps(result,indent=2))
    return 0 if a.emit_source or result['accepted'] else 1


if __name__=='__main__':raise SystemExit(main())
