"""Connect regenerated provenance relations to actual selector input fields.

Providers must regenerate exactly from raw RTL. This consumes no old CPU INV.
The conclusion is token-associated metadata, not latest-operand correctness.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_joint_history as history
import cpu_selector_sources as sources
from cpu_certificate_acceptance import run_stage


def connections(plan,slots):
    unique={(r['width'],r['input']):r for r in plan['sources'] if r['edges']}
    result=[];residuals=[]
    for i,row in enumerate(unique.values()):
        matches=[s for s in slots if (s['width'],s['root'])==(row['width'],row['terminal'])]
        if len(matches)==1:result.append(dict(wire_index=i,wire=row,slot=matches[0]))
        else:residuals.append(dict(input=row['input'],terminal=row['terminal'],reason='no unique generated history slot'))
    return result,residuals


def render(ast_path,ast_module,provider):
    provider=Path(provider)
    names=['capture-birth','coverage','value','copies','joint']
    data,proof=history.render(ast_path,ast_module,*[provider/n for n in names])
    verified=history.fields.verify(provider/'joint-history','JointHistory.v',data,proof)
    plan,source,paths,count=sources.render(ast_path,ast_module)
    ast,profile,_=history.origin.raw_binding(ast_path,ast_module);p=profile['ast']['program']
    rows,residuals=connections(plan,data['slots'])
    if not rows:raise ValueError('no history-to-selector connection; not an empty R')
    lines=['Require Import Lang.ExtendedSVCoveredField Lang.ExtendedSVCaptureBirth Lang.ExtendedSVOriginLedger.',
        'Require GeneratedJointHistory.JointHistory.',
        'Import ExtendedSVCoveredField ExtendedSVCaptureBirth ExtendedSVOriginLedger.',
        'Module J:=GeneratedJointHistory.JointHistory.',f'Local Opaque {p}.']
    pattern=history.nested(['H'+str(s['index']) for s in data['slots']])
    recorded=history.nested(['R'+str(s['index']) for s in data['slots']])
    for n,c in enumerate(rows):
        s=c['slot'];w=c['wire'];i=s['index'];ref=s['ref'].replace('V.','J.V.')
        lines += [f'Theorem selector_from_history_{n} seed state g:',
            f' CombLFP {p} seed state ->J.JointInv state g ->',
            f' norm 1(read_signal state {s["valid"]})<>0%Z ->',
            f' exists l,J.joint_tag_{i} g=Some l /\\',
            f' norm {s["width"]}(read_signal state {w["input"]})={ref}.',
            f'Proof. intros HL H HV;unfold J.JointInv in H;destruct H as[_ {pattern}].',
            f' destruct H{i} as[HC HX]. destruct(HC HV)as[l HT]. exists l;split;[exact HT|].',
            f' exact(eq_trans(selector_source_{c["wire_index"]} seed state HL)(HX l HT)). Qed.',
            f'Print Assumptions selector_from_history_{n}.',
            f'Theorem selector_recorded_{n} seed state g:',
            f' CombLFP {p} seed state ->J.AuthenticInv state g ->',
            f' norm 1(read_signal state {s["valid"]})<>0%Z ->',
            f' exists l,J.joint_tag_{i} g=Some l /\\ In l(history(J.joint_birth g)) /\\',
            f' norm {s["width"]}(read_signal state {w["input"]})={ref}.',
            'Proof. intros HL[HJ HR]HV.',
            f' destruct(selector_from_history_{n} seed state g HL HJ HV)as[l[HT HX]].',
            f' unfold J.JointRecorded in HR;destruct HR as[_ {recorded}].',
            f' exists l;split;[exact HT|];split;[exact(R{i} l HT)|exact HX]. Qed.',
            f'Print Assumptions selector_recorded_{n}.']
        count+=2
    return dict(connections=rows,residuals=residuals,coq_load_paths=paths,audited_exports=count,
        joint_object_sha256=verified['object_sha256'],old_inv_read=False,
        operand_freshness_proved=False,complete_R_generated=False),source+'\n'+'\n'.join(lines)+'\n'


def check(ast_path,ast_module,provider,output):
    data,source=render(ast_path,ast_module,provider)
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    path=output/'SelectorJoint.v';path.write_text(source)
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(sources.rtl.framework.FLAGS)
    for row in data['coq_load_paths']:flags+=['-R',row['directory'],row['namespace']]
    for folder,ns in [('capture-birth','GeneratedCaptureBirth'),('coverage','GeneratedRecipeCoverage'),
        ('value','GeneratedConnectedProjections'),('copies','GeneratedMetadataCopies'),
        ('joint','GeneratedCoveredFields'),('joint-history','GeneratedJointHistory')]:
        flags+=['-R',str((Path(provider)/folder).resolve()),ns]
    flags+=['-R',str(output.resolve()),'GeneratedSelectorJoint']
    report=dict(accepted=False,old_inv_read=False,complete_R_generated=False,
        operand_freshness_proved=False,connection_count=len(data['connections']),
        source_sha256=hashlib.sha256(source.encode()).hexdigest())
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(history.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',deadline-time.monotonic())
    report.update(coqc_exit=c.returncode,coqc_timed_out=t)
    if c.returncode==0 and time.monotonic()<deadline:
        report['assumptions_closed']=c.stdout.count('Closed under the global context')==data['audited_exports'] and 'Axioms:' not in c.stdout
        k,t=run_stage([str(history.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedSelectorJoint.SelectorJoint'],output/'coqchk.log',deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0 and report['assumptions_closed'])
    report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


def check_auto(ast_path,ast_module,output):
    """Generate the entire provider chain from the two raw AST arguments."""
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    fields=history.fields
    ast,_,_=history.origin.raw_binding(ast_path,ast_module)
    births=history.birth.discover(ast)
    coverage=fields.coverage.discover(ast)
    report=dict(accepted=False,old_inv_read=False,external_provider_required=False,
        complete_R_generated=False,operand_freshness_proved=False,stages={})
    def save():
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        return report
    (output/'discovery.json').write_text(json.dumps(dict(birth=births,coverage=coverage),indent=2)+'\n')
    if len(births['captures'])!=1 or not coverage['covered_fields']:
        report.update(status='unsupported_history_schema',
            residual='requires one generated capture carrier and a covered metadata network',
            capture_count=len(births['captures']),covered_field_count=len(coverage['covered_fields']),
            capture_residuals=births.get('residuals',[]),coverage_residuals=coverage.get('residuals',[]))
        return save()
    provider=output/'providers';provider.mkdir()
    tasks=[('capture-birth',lambda:history.birth.check(ast_path,ast_module,provider/'capture-birth')),
        ('coverage',lambda:fields.coverage.check(ast_path,ast_module,provider/'coverage')),
        ('value',lambda:fields.connected.check(ast_path,ast_module,provider/'value')),
        ('copies',lambda:fields.copies.check(ast_path,ast_module,provider/'copies')),
        ('joint',lambda:fields.check(ast_path,ast_module,provider/'coverage',provider/'value',provider/'copies',provider/'joint')),
        ('joint-history',lambda:history.check(ast_path,ast_module,provider/'capture-birth',provider/'coverage',
            provider/'value',provider/'copies',provider/'joint',provider/'joint-history'))]
    for name,action in tasks:
        result=action();report['stages'][name]=result;save()
        if not result.get('accepted'):
            report.update(status='dependency_failed',failed_stage=name)
            return save()
    try:report['connection']=check(ast_path,ast_module,provider,output/'connection')
    except ValueError as exc:
        report.update(status='connection_residual',residual=str(exc))
        return save()
    report['accepted']=report['connection']['accepted']
    report['status']='checked_metadata_connection' if report['accepted'] else 'connection_failed'
    return save()


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for n in ['ast','ast-module','output']:p.add_argument('--'+n,required=True)
    p.add_argument('--provider',help='Optional exact-regenerated provider; omitted generates all dependencies')
    a=p.parse_args();r=check(a.ast,a.ast_module,a.provider,a.output) if a.provider else check_auto(a.ast,a.ast_module,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted'] else 1)
