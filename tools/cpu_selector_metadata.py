"""Join freshly reconstructable metadata transport to actual selector wiring.
No old INV lookup. This transfers an existing instruction-label relation; it
does not invent initial labels, token age, or an ISA result relation.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_selector_sources as sources
import cpu_pending_metadata_copies as metadata
import cpu_pending_covered_fields as providers
from cpu_certificate_acceptance import run_stage
origin=sources.selectors.origin


def connect(sd,md,vd=None):
    unique={(r['width'],r['input']):r for r in sd['sources'] if r['edges']}
    connections=[];residuals=[]
    for i,row in enumerate(unique.values()):
        candidates=[(kind,j,r) for kind,rows in [('copy',md['copy_edges']),('connected',(vd or {}).get('projections',[]))]
            for j,r in enumerate(rows) if r['root']==row['terminal'] and r['width']==row['width']]
        if len(candidates)!=1:
            residuals.append(dict(input=row['input'],terminal=row['terminal'],
                reason='no unique generated metadata-copy relation'));continue
        kind,j,m=candidates[0];connections.append(dict(source_index=i,copy_index=j,kind=kind,wire=row,copy=m))
    return connections,residuals


def render(ast_path,ast_module,source_provider,copy_provider,connected_provider=None):
    sd,ss,paths,count=sources.render(ast_path,ast_module)
    folder=Path(source_provider);sr=json.loads((folder/'report.json').read_text())
    if not(sr.get('accepted') is True and sr.get('coqc_exit')==sr.get('coqchk_exit')==0
        and sr.get('assumptions_closed') is True and sr.get('old_inv_read') is False
        and sr.get('source_sha256')==hashlib.sha256(ss.encode()).hexdigest()
        and (folder/'SelectorSources.v').read_text()==ss
        and json.loads((folder/'plan.json').read_text())==sd
        and (folder/'SelectorSources.vo').is_file()):
        raise ValueError('current raw-generated selector source certificate required')
    md=dict(copy_edges=[])
    if copy_provider:
        md,ms=metadata.render(ast_path,ast_module)
        providers.verify(copy_provider,'MetadataCopies.v',md,ms)
    vd=None
    if connected_provider:
        vd,vs=metadata.connected.render(ast_path,ast_module)
        providers.verify(connected_provider,'ConnectedProjections.v',vd,vs)
    ast,profile,_=origin.raw_binding(ast_path,ast_module);p=profile['ast']['program']
    connections,residuals=connect(sd,md,vd)
    if not connections:raise ValueError('no checked metadata-to-selector connection')
    lines=['From Coq Require Import ZArith.',f'Require Import {ast_module}.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVProjectionOrigin',
        ' GeneratedSelectorSources.SelectorSources.',
        'Import ExtendedSV ExtendedSVProjectionOrigin.',
        'Module W:=GeneratedSelectorSources.SelectorSources.',
        f'Local Opaque {p}.']
    if copy_provider:
        lines+=['Require Import GeneratedMetadataCopies.MetadataCopies.',
            'Module M:=GeneratedMetadataCopies.MetadataCopies.']
    if connected_provider:
        lines+=['Require Import GeneratedConnectedProjections.ConnectedProjections.',
            'Module C:=GeneratedConnectedProjections.ConnectedProjections.']
    for n,c in enumerate(connections):
        row=c['wire'];m=c['copy'];i=c['source_index'];j=c['copy_index'];w=row['width']
        r=m['root'];src=m['source'];proc=ast['module']+'.'+m['process']
        post=f'(PhaseSemantics {p} ev pre)'
        if c['kind']=='connected':
            ref=f'C.connected_{j}_reference'
            lines += [f'Theorem selector_metadata_{n}(Label:Type)(word:Label->Z)',
                ' seed post_seed ev pre old incoming label:',
                f' changed_signal ev<>{r}%nat ->',
                f' CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
                f' (forall l,old=Some l ->norm {w}(read_signal pre {r})={ref}(word l)) ->',
                f' (forall l,incoming=Some l ->norm 32(read_signal(phase_driven_state {p} ev pre){src})=norm 32(word l)) ->',
                f' @projection_phase_origin Label {p} {proc} C.connected_{j}_recipe ev pre old incoming=Some label ->',
                f' CombLFP {p} post_seed {post} ->',
                f' norm {w}(read_signal {post} {row["input"]})={ref}(word label).',
                'Proof. intros HE HL HO HI HT HP.',
                f' exact(eq_trans(W.selector_source_{i} post_seed {post} HP)',
                f' (C.connected_{j}_actual_phase Label word seed ev pre old incoming label HE HL HO HI HT)). Qed.',
                f'Print Assumptions selector_metadata_{n}.']
            continue
        lines += [f'Theorem selector_metadata_{n}(Label:Type)(reference:Label->Z)',
            ' seed post_seed ev pre old incoming label:',
            f' changed_signal ev<>{r}%nat ->changed_signal ev<>{src}%nat ->',
            f' CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
            f' (forall l,old=Some l ->norm {w}(read_signal pre {r})=reference l) ->',
            f' (forall l,incoming=Some l ->norm {w}(read_signal pre {src})=reference l) ->',
            f' @projection_phase_origin Label {p} {proc} M.copy_{j}_recipe ev pre old incoming=Some label ->',
            f' CombLFP {p} post_seed {post} ->',
            f' norm {w}(read_signal {post} {row["input"]})=reference label.',
            'Proof. intros HE HS HL HO HI HT HP.',
            f' exact(eq_trans(W.selector_source_{i} post_seed {post} HP)',
            f' (M.copy_{j}_actual_phase Label reference seed ev pre old incoming label HE HS HL HO HI HT)). Qed.',
            f'Print Assumptions selector_metadata_{n}.']
    plan=dict(connections=connections,residuals=residuals,old_inv_read=False,
        token_initialization_proved=False,token_age_proved=False,complete_R_generated=False)
    return plan,'\n'.join(lines)+'\n',paths


def check(ast_path,ast_module,source_provider,copy_provider,output,connected_provider=None):
    plan,source,paths=render(ast_path,ast_module,source_provider,copy_provider,connected_provider)
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    path=output/'SelectorMetadata.v';path.write_text(source)
    (output/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    flags=list(sources.rtl.framework.FLAGS)
    for r in paths:flags+=['-R',r['directory'],r['namespace']]
    for directory,namespace in [(source_provider,'GeneratedSelectorSources'),(copy_provider,'GeneratedMetadataCopies'),
        (output,'GeneratedSelectorMetadata')]:
        if directory: flags+=['-R',str(Path(directory).resolve()),namespace]
    if connected_provider:flags+=['-R',str(Path(connected_provider).resolve()),'GeneratedConnectedProjections']
    report=dict(accepted=False,connection_count=len(plan['connections']),old_inv_read=False,
        token_initialization_proved=False,token_age_proved=False,complete_R_generated=False,
        source_sha256=hashlib.sha256(source.encode()).hexdigest())
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',deadline-time.monotonic())
    report.update(coqc_exit=c.returncode,coqc_timed_out=t)
    if c.returncode==0 and time.monotonic()<deadline:
        report['assumptions_closed']=c.stdout.count('Closed under the global context')==len(plan['connections']) and 'Axioms:' not in c.stdout
        k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedSelectorMetadata.SelectorMetadata'],output/'coqchk.log',deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
            accepted=k.returncode==0 and report['assumptions_closed'])
    report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


def check_auto(ast_path,ast_module,source_provider,output):
    """Generate all needed providers from raw AST, never search old proofs."""
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    ast,_,_=origin.raw_binding(ast_path,ast_module)
    sd=sources.discover(ast);md=metadata.discover(ast);vd=metadata.connected.discover(ast)
    connections,residuals=connect(sd,md,vd)
    report=dict(accepted=False,complete_R_generated=False,old_inv_read=False,
        residuals=residuals,connection_count=len(connections),llm_calls=0)
    kinds={r['kind'] for r in connections};cp=None;vp=None
    if not connections:report['status']='no_supported_metadata_connection_not_a_completeness_claim'
    else:
        ok=True
        if 'copy' in kinds:
            cp=output/'copies';r=metadata.check(ast_path,ast_module,cp)
            report['copies']=r;ok=ok and r['accepted']
        if 'connected' in kinds:
            vp=output/'capture';r=metadata.connected.check(ast_path,ast_module,vp)
            report['capture']=r;ok=ok and r['accepted']
        if ok:
            r=check(ast_path,ast_module,source_provider,cp,output/'connection',vp)
            report['connection']=r;report['accepted']=r['accepted']
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for n in ['ast','ast-module','source-provider','output']:p.add_argument('--'+n,required=True)
    p.add_argument('--copy-provider')
    p.add_argument('--connected-provider')
    p.add_argument('--auto',action='store_true')
    a=p.parse_args()
    if a.auto and (a.copy_provider or a.connected_provider):p.error('automatic mode forbids supplied metadata providers')
    r=(check_auto(a.ast,a.ast_module,a.source_provider,a.output) if a.auto
        else check(a.ast,a.ast_module,a.source_provider,a.copy_provider,a.output,a.connected_provider))
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted'] else 1)
