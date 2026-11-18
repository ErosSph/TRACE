"""Generate nonzero-word provenance, never assume zero means an ISA bubble."""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_origins as origin
from cpu_certificate_acceptance import run_stage
rtl=origin.pending.rtl


def shape(e):
    if e.name=='EVar' and e.args[0].name=='32':return 'apply CopyLeaf.'
    if e.name=='EConst' and [a.name for a in e.args]==['32','0']:return 'apply ZeroLeaf.'
    if e.name=='ECond' and e.args[0].name=='32':
        return 'apply CopyChoice.\n'+shape(e.args[2])+'\n'+shape(e.args[3])
    raise ValueError('not a 32-bit copy/hold/zero expression')


def render(ast_path,ast_module):
    ast,profile,paths=origin.raw_binding(ast_path,ast_module)
    selected=[];residuals=[]
    for row in origin.pending.analyze(ast)['slots']:
        try:
            proof=shape(rtl.Parser(row['capture']['next_expression']).complete())
            selected.append(dict(root=row['carrier'],proof=proof))
        except ValueError as exc:residuals.append(dict(root=row['carrier'],reason=str(exc)))
    if not selected:raise ValueError('no supported nonzero capture; no vacuous proof')
    _,remaining,outputs,source,count=origin.expressions.proposal(profile,[r['root'] for r in selected])
    if remaining:raise ValueError('scalar certificate not available')
    p=profile['ast']['program'];proofs={r['root']:r['proof'] for r in selected}
    lines=['Require Import Lang.ExtendedSVNonzeroCapture Lang.ExtendedSVScalarHistory',
        ' Lang.ExtendedSVNonzeroHistory Lang.ExtendedSVCaptureBirth Lang.ExtendedSVRootProjection Lang.ExtendedSVConstantRoot.',
        'Import ExtendedSVNonzeroCapture ExtendedSVScalarHistory ExtendedSVCaptureBirth ExtendedSVRootProjection ExtendedSVConstantRoot.',f'Local Opaque {p}.']
    initialized=[]
    for row in outputs:
        r=row['root'];proc=ast['module']+'.'+row['process']
        lines += [f'Lemma nonzero_shape_{r}:CopyOrZero root_{r}_expression.',
            f'Proof. unfold root_{r}_expression. {proofs[r]} Qed.',
            f'Lemma nonzero_width_{r}:self_widthb 32 {r} root_{r}_expression=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Definition nonzero_certificate_{r}:ScalarCertificate {p} {r} 32 {proc} root_{r}_expression:=',
            f' Build_ScalarCertificate _ _ _ _ _ root_{r}_comb_frame nonzero_width_{r} root_{r}_expression_phase.',
            f'Theorem nonzero_phase_{r} ev pre serial pc old:',
            f' changed_signal ev<>{r}%nat ->ExtendedSVNonzeroCapture.Related {r} old pre ->',
            f' ExtendedSVNonzeroCapture.Related {r}',
            f' (ExtendedSVNonzeroCapture.phase_tag {p} {proc} {r} root_{r}_expression ev pre serial pc old)',
            f' (PhaseSemantics {p} ev pre).',
            f'Proof. exact(actual_phase {p} {r} {proc} root_{r}_expression nonzero_certificate_{r} nonzero_shape_{r} ev pre serial pc old). Qed.',
            f'Print Assumptions nonzero_phase_{r}.']
        count+=1
        lines += [f'Definition nonzero_history_{r}:=',
            f' ExtendedSVNonzeroHistory.replay {p} {proc} {r} root_{r}_expression (fun _ _=>None).',
            f'Theorem nonzero_history_preserves_{r} events:',
            f' Forall(fun ev=>changed_signal ev<>{r}%nat)events ->forall pre g,',
            f' ExtendedSVNonzeroHistory.Invariant {r} pre g ->',
            f' ExtendedSVNonzeroHistory.Invariant {r}(fst(nonzero_history_{r} events pre g))(snd(nonzero_history_{r} events pre g)).',
            f'Proof. exact(ExtendedSVNonzeroHistory.replay_preserves {p} {r} {proc} root_{r}_expression',
            f' nonzero_certificate_{r} nonzero_shape_{r} (fun _ _=>None) events). Qed.',
            f'Theorem nonzero_history_erases_{r} events pre g:',
            f' fst(nonzero_history_{r} events pre g)=phase_run {p} events pre.',
            'Proof. apply ExtendedSVNonzeroHistory.replay_erases. Qed.',
            f'Print Assumptions nonzero_history_preserves_{r}.',
            f'Print Assumptions nonzero_history_erases_{r}.']
        count+=2
        if not any(x['kind']=='Initial' and r in x['writers'] for x in ast['processes']):
            lines += [f'Local Transparent {p}.',
                f'Lemma nonzero_initial_unwritten_{r}:roots_unwrittenb {r}(filter is_initial(processes {p}))=true.',
                'Proof. vm_compute. reflexivity. Qed.',f'Local Opaque {p}.',
                f'Theorem nonzero_history_initial_{r}:',
                f' ExtendedSVNonzeroHistory.Invariant {r}(initialize {p} [])(Build_Ghost 0 None []).',
                'Proof. apply ExtendedSVNonzeroHistory.empty_initial.',
                f' rewrite(initialize_unwritten_field {p} {r} nonzero_initial_unwritten_{r} []). reflexivity. Qed.',
                f'Print Assumptions nonzero_history_initial_{r}.']
            count+=1;initialized.append(r)
    return dict(roots=[r['root'] for r in selected],residuals=residuals,coq_load_paths=paths,
        initialized_roots=initialized,ast_sha256=ast['source_sha256'],audited_exports=count),source+'\n'+'\n'.join(lines)+'\n'


def check(ast_path,ast_module,output):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module)
    except ValueError as exc:
        report=dict(accepted=False,status='unsupported_nonzero_capture',residual=str(exc),
            old_inv_read=False,complete_R_generated=False,zero_encoding_inactive_proved=False,isa_admission_proved=False)
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        return report
    path=output/'NonzeroCapture.v';path.write_text(source)
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for row in data['coq_load_paths']:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedNonzeroCapture']
    report=dict(accepted=False,roots=data['roots'],old_inv_read=False,complete_R_generated=False,
        zero_encoding_inactive_proved=False,isa_admission_proved=False,
        generated_history=True,initialized_roots=data['initialized_roots'],
        initialization_scope='original initialize with empty seed, not arbitrary hardware power-up values',
        source_sha256=hashlib.sha256(source.encode()).hexdigest())
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',deadline-time.monotonic())
    report.update(coqc_exit=c.returncode,coqc_timed_out=t)
    if c.returncode==0 and time.monotonic()<deadline:
        report['assumptions_closed']=c.stdout.count('Closed under the global context')==data['audited_exports'] and 'Axioms:' not in c.stdout
        k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedNonzeroCapture.NonzeroCapture'],output/'coqchk.log',deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0 and report['assumptions_closed'])
    report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for n in ['ast','ast-module','output']:p.add_argument('--'+n,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted'] else 1)
