"""Untrusted LLM rule choice -> checked complete RF address case connection.
All branch arms, tags and the original default are retained; no ISA role guessed.
"""
import argparse,json,time
from pathlib import Path
import cpu_operand_address_origins as a
import cpu_pending_llm as llm
from cpu_certificate_acceptance import run_stage
o=a.origin


def collect(designs):
    slots={};facts={};jobs={}
    for d in designs:
        ast,_,_=o.raw_binding(d['ast'],d['ast_module'])
        plan=a.support_frontier(ast)
        facts[d['name']]=dict(ast_sha256=ast['source_sha256'],frontier=plan,
            processes=[dict(name=p['name'],body=a.rtl.render(p['body']))for p in ast['processes']
                if p['name']in{r['process']for r in plan['cases']}])
        for row in plan['cases']:
            key=d['name']+'_'+row['process'];jobs[key]=(d,row)
            slots[key]=[dict(id='complete_case_and_alias',description='Prove all scalar case arms plus original default, then connect actual RF aliases through original CombLFP; no branch inactivity or ISA identity is assumed.'),
                        dict(id='defer_unsupported',description='Keep the residual; do not generate a proof from incomplete structure.')]
    return slots,facts,jobs


def render(d,row):
    ast,profile,paths=o.raw_binding(d['ast'],d['ast_module'])
    base,_=a.case_binding.render(d['ast'],d['ast_module'],row['process'],structural=True)
    requested=sorted({int(n.args[1].name)for port in a.readers.analyze(ast)['ports']
        for n in a.rtl.walk(port['rhs'])if n.name=='EVar'and n.args[0].name==str(row['width'])})
    chains={};roots=set()
    for root in requested:
        current=root;edges=[];seen=set()
        while current!=row['root']and current not in seen:
            seen.add(current)
            writers=[p for p in ast['processes']if p['kind']!='Initial'and current in p['writers']]
            if len(writers)!=1 or writers[0]['kind']!='Combinational':break
            st=writers[0]['body'];w=str(row['width'])
            if not(st.name=='SAssign'and st.args[0].name=='false'and st.args[2].name=='LVar'
                and st.args[2].args[0].name==w and st.args[1].name=='EVar'and st.args[1].args[0].name==w):break
            parent=int(st.args[1].args[1].name);edges.append((current,parent));current=parent
        if current==row['root']:chains[root]=edges;roots.update(x for x,_ in edges)
    if not chains:raise ValueError('no actual RF address reaches the case output')
    _,analysis,alias=a.connected.comb.proposal(profile,sorted(roots))
    if analysis['residuals']:raise ValueError('unproved alias structure')
    indices={p['output_root']:i for i,p in enumerate(analysis['ports'])}
    program=profile['ast']['program'];lines=[]
    for root,edges in chains.items():
        term='(case_actual_lfp seed fixed HL)'
        for child,parent in reversed(edges):
            term=f'(eq_trans(port_{indices[child]}_lfp seed fixed HL)(eq_trans(norm_idempotent {row["width"]}(read_signal fixed {parent})){term}))'
        lines += [f'Theorem address_{root}_complete_case seed fixed:CombLFP {program} seed fixed ->',
            f'norm {row["width"]}(read_signal fixed {root})=norm {row["width"]}(eval_expr fixed case_expression).',
            f'Proof. intro HL;exact {term}. Qed.',f'Print Assumptions address_{root}_complete_case.']
    source=base+'\n'+alias+'\n'+'\n'.join(lines)+'\n'
    return source,paths,source.count('Print Assumptions '),sorted(chains)


def check(d,row,output):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    source,paths,count,roots=render(d,row);file=output/'CaseAddresses.v';file.write_text(source)
    flags=list(a.rtl.framework.FLAGS)
    for p in paths:flags+=['-R',p['directory'],p['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedCaseAddresses']
    start=time.monotonic();deadline=start+1200
    result,t=run_stage([str(o.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],output/'coqc.log',1200)
    r=dict(accepted=False,roots=roots,coqc_exit=result.returncode,coqc_timed_out=t,
        old_inv_read=False,isa_field_identity_proved=False,complete_R_generated=False)
    if result.returncode==0:
        closed=result.stdout.count('Closed under the global context')==count and'Axioms:'not in result.stdout
        k,t=run_stage([str(o.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedCaseAddresses.CaseAddresses'],output/'coqchk.log',max(.1,deadline-time.monotonic()))
        r.update(assumptions_closed=closed,coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=closed and k.returncode==0)
    r['seconds']=time.monotonic()-start;(output/'report.json').write_text(json.dumps(r,indent=2)+'\n');return r


def run(designs,output,key=None):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    slots,facts,jobs=collect(designs);request=llm.prompt(slots,facts,'field_selector_gap')
    (output/'request.json').write_text(json.dumps(request,indent=2)+'\n')
    audit,answer=llm.query(slots,facts,key if key is not None else llm.transport.key_from_note(),'field_selector_gap')if slots else({'attempts':0},None)
    r=dict(llm=audit,proposals=answer,checks={},complete_R_generated=False,old_inv_read=False,
           scope='LLM-selected full hardware address equations, not architectural R')
    (output/'report.json').write_text(json.dumps(r,indent=2)+'\n')
    for key,choice in(answer or {}).items():
        if choice=='complete_case_and_alias':r['checks'][key]=check(*jobs[key],output/key)
    (output/'report.json').write_text(json.dumps(r,indent=2)+'\n');return r


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',required=True)
    p.add_argument('--manifest',default=str(o.ROOT/'framework/pending-rtl-inputs.json'))
    args=p.parse_args();print(json.dumps(run(json.loads(Path(args.manifest).read_text())['designs'],args.output),indent=2))
