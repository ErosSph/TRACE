"""Generate use-guarded source clauses from original output expressions.

This produces candidate R clauses and their exact physical meaning. It does
not invent a consumer guard or establish reachable-state preservation.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
import cpu_operand_route_proofs as routes
from cpu_certificate_acceptance import run_stage
origin = routes.origin


def render(program, outputs):
    lines=['''From Coq Require Import ZArith List.
Require Import Lang.ExtendedSV Ex.External.CPUReadyOperand
 Ex.External.CPUReadySelectionRequirements GeneratedOperandRoutes.OperandRoutes.
Import ExtendedSV CPUReadyOperand CPUReadySelectionRequirements.
Local Open Scope Z_scope.''']
    for n, row in enumerate(outputs):
        w, r = row['width'], row['output_root']
        lines += [f'''Definition port_{n}_guarded_R guard fixed physical address slots :=
 guarded_requirements guard {w}%nat port_{n}_rhs fixed physical address slots.
Theorem port_{n}_guarded_exact seed fixed guard physical address slots:
 CombLFP {program} seed fixed ->
 (port_{n}_guarded_R guard fixed physical address slots <->
  (eval_expr fixed guard<>0 ->
   resolve 0 physical address slots=Some(norm {w}%nat(read_signal fixed {r}%nat)))).
Proof.
 intro HL;unfold port_{n}_guarded_R,guarded_requirements.
 rewrite(port_{n}_lfp seed fixed HL).
 split;intros H HG;apply selection_exact;exact(H HG).
Qed.
Theorem port_{n}_unready_blocks guard fixed physical address slots:
 address<>0 ->lookup address slots=Some None ->
 port_{n}_guarded_R guard fixed physical address slots ->eval_expr fixed guard=0.
Proof. exact(unready_requires_inactive guard {w}%nat port_{n}_rhs fixed physical address slots). Qed.''']
    lines += ['Goal True. idtac "READY_SELECTION_AUDIT". exact I. Qed.']
    for n in range(len(outputs)):
        lines += [f'Print Assumptions port_{n}_guarded_exact.',f'Print Assumptions port_{n}_unready_blocks.']
    return '\n'.join(lines)+'\n'


def check(ast_path, ast_module, provider, output):
    provider, output = Path(provider), Path(output)
    ast, binding, paths = origin.raw_binding(ast_path, ast_module)
    analysis, _ = routes.analyze(ast)
    expected = routes.ports.render(binding['ast'], ast, analysis, opaque_single=True)
    expected += routes.requirement_source(binding['ast']['program'], analysis['ports'])
    prior = json.loads((provider/'report.json').read_text())
    if not (prior.get('coqc_exit') == 0 and prior.get('coqchk_exit') == 0
            and prior.get('source_sha256') == hashlib.sha256(expected.encode()).hexdigest()
            and (provider/'OperandRoutes.v').read_text() == expected
            and (provider/'OperandRoutes.vo').is_file()
            and routes.audit_requirements((provider/'coqc.log').read_text(),len(analysis['ports']))):
        raise ValueError('unchanged checked original output equations required')
    if not analysis['ports']:raise ValueError('empty selection proof forbidden')
    output.mkdir(parents=True,exist_ok=False)
    source=f'Require Import {ast_module}.\n'+render(binding['ast']['program'],analysis['ports'])
    path=output/'ReadySelection.v';path.write_text(source)
    flags=list(origin.pending.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(provider.resolve()),'GeneratedOperandRoutes',
            '-R',str(output.resolve()),'GeneratedReadySelection']
    report=dict(accepted=False,old_inv_read=False,complete_R_generated=False,
        actual_consumer_guard_identified=False,reachable_R_proved=False,
        count=len(analysis['ports']),source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        residuals=['bind guard to actual source consumption',
            'hardware slot age/readiness and ISA operation correspondence',
            'initialization and whole-cycle preservation'])
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',1200)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t)
    if c.returncode==0:
        audit=c.stdout.split('\nREADY_SELECTION_AUDIT\n')
        closed=len(audit)==2 and audit[1].count('Closed under the global context')==2*len(analysis['ports']) and 'Axioms:' not in audit[1]
        k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedReadySelection.ReadySelection'],output/'coqchk.log',max(.1,deadline-time.monotonic()))
        report.update(assumptions_closed=closed,coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=closed and k.returncode==0)
    report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['ast','ast-module','provider','output']:p.add_argument('--'+key,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.provider,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted'] else 1)
