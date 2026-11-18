"""Connect actual RF address aliases to checked full-width instruction fields.
The high bank bit is proved zero by the existing raw-RTL generator, not erased.
"""
import argparse
import hashlib
import json
import re
import time
from pathlib import Path
import cpu_pending_origins as origin
import cpu_tagged_instruction_fields as tagged
import cpu_rf_read_ports as readers
import cpu_comb_scalar_bindings as comb
from cpu_certificate_acceptance import run_stage
rtl=origin.pending.rtl


def render(ast_path,ast_module):
    ast,profile,paths=origin.raw_binding(ast_path,ast_module)
    _,residuals,fields,source,count,_=tagged.proposal(profile, opaque_program_connection=True)
    byroot={row['root']:row for row in fields}
    requested=sorted({int(n.args[1].name)for port in readers.analyze(ast)['ports']
        for n in rtl.walk(port['rhs'])if n.name=='EVar' and n.args[0].name=='6'})
    rows=[];missing=[]
    for root in requested:
        current=root;edges=[];seen=set()
        while current not in byroot:
            if current in seen:break
            seen.add(current)
            writers=[p for p in ast['processes']if p['kind']!='Initial' and current in p['writers']]
            if len(writers)!=1 or writers[0]['kind']!='Combinational':break
            st=writers[0]['body']
            if st.name!='SAssign' or st.args[0].name!='false' or st.args[2].name!='LVar':break
            rhs=st.args[1]
            if st.args[2].args[0].name!='6' or rhs.name!='EVar' or rhs.args[0].name!='6':break
            parent=int(rhs.args[1].name);edges.append(dict(root=current,parent=parent));current=parent
        if current not in byroot:missing.append(root);continue
        field=byroot[current]
        rows.append(dict(root=root,field_root=current,field=field['field'],
            word_root=field['origin']['terminal'],edges=edges))
    report=dict(accepted=False,old_inv_read=False,complete_R_generated=False,
        token_identity_proved=False,tag_truncated=False,origins=rows,unresolved_roots=missing,
        generator_residuals=residuals,ast_sha256=ast['source_sha256'])
    if residuals or not rows:return report,None,paths,0
    roots=sorted({e['root']for row in rows for e in row['edges']})
    aliases={}
    if roots:
        _,analysis,alias_source=comb.proposal(profile,roots)
        if analysis['residuals']:
            report['alias_residuals']=analysis['residuals'];return report,None,paths,0
        aliases={p['output_root']:i for i,p in enumerate(analysis['ports'])}
        alias_source=re.sub(r'\b(port_\d+|block_\d+|actual_combs)',r'address_alias_\1',alias_source)
        source+='\n'+alias_source;count+=len(analysis['ports'])
    program=profile['ast']['program'];lines=[]
    for row in rows:
        root=row['root'];word=row['word_root'];field=row['field']
        term=f'(root_{row["field_root"]}_actual_carrier seed fixed HL)'
        for edge in reversed(row['edges']):
            term=f'(eq_trans(address_alias_port_{aliases[edge["root"]]}_lfp seed fixed HL)(eq_trans(norm_idempotent 6(read_signal fixed {edge["parent"]})){term}))'
        lines += [f'Theorem address_{root}_tagged_origin seed fixed instruction:CombLFP {program} seed fixed ->',
            f' norm 32(read_signal fixed {word})=norm 32 instruction ->',
            f' norm 6(read_signal fixed {root})=field_reference instruction {field}.',
            f'Proof. intros HL HW. exact(eq_trans {term} (field_reference_alias _ _ {field} HW)). Qed.',
            f'Print Assumptions address_{root}_tagged_origin.']
        count+=1
    return report,source+'\n'+'\n'.join(lines)+'\n',paths,count


def check(ast_path,ast_module,output,timeout=1200):
    if not 0 < timeout <= 1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    report,source,paths,count=render(ast_path,ast_module)
    if source is not None:
        path=output/'TaggedAddresses.v';path.write_text(source)
        flags=list(rtl.framework.FLAGS)
        for row in paths:flags+=['-R',row['directory'],row['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedTaggedAddresses']
        start=time.monotonic();deadline=start+timeout
        c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',deadline-time.monotonic())
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest())
        if c.returncode==0 and time.monotonic()<deadline:
            report['assumptions_closed']=c.stdout.count('Closed under the global context')==count and 'Axioms:' not in c.stdout
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedTaggedAddresses.TaggedAddresses'],output/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0 and report['assumptions_closed'])
        report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:p.add_argument('--'+name,required=True)
    p.add_argument('--timeout',type=float,default=1200)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output,a.timeout)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
