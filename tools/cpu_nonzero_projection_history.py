"""Generate actual source-history to decoded-field connections from raw RTL.

No physical valid bit is invented. Known-tag values and recordedness are proved;
ISA admission, architectural coverage and complete R remain separate obligations.
"""
import argparse,json,time,hashlib
from pathlib import Path
import cpu_nonzero_capture as nonzero
import cpu_pending_connected_projections as connected
from cpu_certificate_acceptance import run_stage


def matching(projections,roots):
    return [(i,row)for i,row in enumerate(projections)if row['source']in roots]


def connection_flags(paths,output):
    flags=list(nonzero.rtl.framework.FLAGS)
    for b in paths:flags+=['-R',b['directory'],b['namespace']]
    # -R is recursive; specific children must override the parent's mapping.
    for folder,namespace in [('', 'GeneratedProjectionHistory'),('source','GeneratedNonzeroCapture'),('projection','GeneratedConnectedProjections')]:
        flags+=['-R',str((Path(output)/folder).resolve()),namespace]
    return flags


def check(ast_path,ast_module,output):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    report=dict(accepted=False,old_inv_read=False,complete_R_generated=False,
                isa_admission_proved=False,validity_coverage_proved=False,
                phase_conditions_discharged=False,
                conditions=['actual sampled state satisfies CombLFP',
                    'external event does not directly drive source or target',
                    'source history and known target labels satisfy the pre-relation'])
    def finish():
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    ast,profile,paths=nonzero.origin.raw_binding(ast_path,ast_module)
    try:nd,_=nonzero.render(ast_path,ast_module)
    except ValueError as exc:
        report.update(status='unsupported_source_history',residual=str(exc));return finish()
    vd=connected.discover(ast);pairs=matching(vd['projections'],nd['roots'])
    source_process={r['carrier']:r['capture']['process']for r in nonzero.origin.pending.analyze(ast)['slots']}
    report['connections']=[dict(source=r['source'],target=r['root'])for _,r in pairs]
    if not pairs:
        report['status']='no_source_history_projection_match';return finish()
    report['source_history']=nonzero.check(ast_path,ast_module,output/'source')
    if not report['source_history']['accepted']:return finish()
    report['projection']=connected.check(ast_path,ast_module,output/'projection')
    if not report['projection']['accepted']:return finish()
    p=profile['ast']['program']
    lines=['Require Import Lang.ExtendedSVNonzeroProjectionHistory Lang.ExtendedSVCaptureBirth.',
        f'Require Import GeneratedNonzeroCapture.NonzeroCapture GeneratedConnectedProjections.ConnectedProjections {ast_module}.',
        'Import ExtendedSVCaptureBirth.',
        'Module N:=GeneratedNonzeroCapture.NonzeroCapture.',
        'Module V:=GeneratedConnectedProjections.ConnectedProjections.']
    for i,row in pairs:
        src=row['source'];dst=row['root'];proc=ast['module']+'.'+source_process[src]
        target_proc=ast['module']+'.'+row['process']
        lines += [f'Definition history_connection_{dst}:=',
            f' @ExtendedSVNonzeroProjectionHistory.phase_preserves {p} {src} {dst} {row["width"]}',
            f' {proc} {target_proc} N.root_{src}_expression V.connected_{i}_recipe',
            f' V.connected_{i}_reference (fun _ _=>None)',
            f' N.nonzero_certificate_{src} N.nonzero_shape_{src}',
            f' (@V.connected_{i}_actual_phase Token token_word).',
            f'Print Assumptions history_connection_{dst}.']
    source='\n'.join(lines)+'\n';file=output/'ProjectionHistory.v';file.write_text(source)
    flags=connection_flags(paths,output)
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(nonzero.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],output/'coqc.log',1200)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest())
    if c.returncode==0 and time.monotonic()<deadline:
        closed=c.stdout.count('Closed under the global context')==len(pairs)and'Axioms:'not in c.stdout
        report['assumptions_closed']=closed
        k,t=run_stage([str(nonzero.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedProjectionHistory.ProjectionHistory'],output/'coqchk.log',deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0 and closed)
    report['connection_seconds']=time.monotonic()-start
    return finish()


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:p.add_argument('--'+name,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output);print(json.dumps(r,indent=2))
    raise SystemExit(0 if r['accepted']else 1)
