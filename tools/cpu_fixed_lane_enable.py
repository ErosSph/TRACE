"""Discover fixed-lane guard decoders and prove actual local-process address selection.
No assertion is made that local output equals the full CPU LFP packed bit.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_write_ownership_frontier as ownership
from cpu_certificate_acceptance import run_stage
rtl=ownership.rtl

def discover(ast):
    front=ownership.analyze(ast);rows={};residuals=[]
    for site in front['writes']:
        if site['destination']['kind']!='fixed_lane':continue
        lane=site['destination']['lane'];matched=False
        for guard in site['guards']:
            if not guard['taken']:continue
            g=rtl.Parser(guard['expression']).complete()
            if g.name!='ESel'or g.args[0].name!='1':continue
            base,offset=g.args[1:]
            if base.name!='EVar'or ownership.bank.literal(offset)!=lane:continue
            root=int(base.args[1].name);writers=[]
            for p in ast['processes']:
                st=p['body']
                if p['kind']!='Combinational'or st.name!='SAssign'or st.args[0].name!='false':continue
                rhs,lhs=st.args[1:]
                if lhs.name!='LSel'or lhs.args[0].name!='1'or lhs.args[1].name!='LVar':continue
                if int(lhs.args[1].args[1].name)!=root or ownership.bank.literal(lhs.args[2])!=lane:continue
                writers.append((p,rhs,lhs))
            if len(writers)!=1:continue
            p,rhs,lhs=writers[0]
            if rhs.name!='EBinary'or rhs.args[0].name!='1'or rhs.args[1].name!='BAnd':continue
            eq,enable=rhs.args[2:]
            if eq.name!='EBinary'or eq.args[0].name!='1'or eq.args[1].name!='BEq':continue
            literal,address=eq.args[2:]
            if ownership.bank.literal(literal)!=lane:continue
            key=(root,lane)
            row=rows.setdefault(key,dict(root=root,lane=lane,process=p['name'],
                total=int(lhs.args[1].args[0].name),offset=rtl.render(lhs.args[2]),
                literal=rtl.render(literal),address=rtl.render(address),enable=rtl.render(enable),consumers=[]))
            row['consumers'].append(dict(process=site['process'],path=site['path']))
            matched=True
        if not matched:residuals.append(dict(process=site['process'],path=site['path'],lane=lane,
            reason='no positive same-lane equality decoder; initialization/other path remains explicit'))
    return dict(rows=list(rows.values()),residuals=residuals,write_sites=len(front['writes']),
                full_lfp_bit_connection_proved=False,isa_destination_proved=False)

def render(ast_module,program,mod,rows):
    lines=[f'Require Import {ast_module}.',
        'From Coq Require Import ZArith Lia.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice Lang.ExtendedSVDecodedEnable.',
        'Import ExtendedSV ExtendedSVBitSlice ExtendedSVDecodedEnable.',
        f'Lemma fuel_positive : (0<statement_fuel {program})%nat.',
        'Proof. vm_compute. lia. Qed.']
    for n,r in enumerate(rows):
        offset,literal,address,enable=[r[k]for k in ['offset','literal','address','enable']]
        proc=mod+'.'+r['process'];root=r['root'];total=r['total']
        lines += [f'Theorem lane_{n}_local_selection s:',
          f' read_slice(read_signal(run_process {program} s {proc}){root})(eval_expr s {offset})1<>0%Z ->',
          f' eval_expr s {address}=eval_expr s {literal}.',
          'Proof. intro H;symmetry.',
          f' apply(decoded_bit_implies_address {program} {proc} s {total}%nat {root}%nat',
          f' {offset} {literal} {address} {enable});',
          f' [reflexivity|exact fuel_positive|change (0<={r["lane"]})%Z;lia|exact H]. Qed.',
          f'Print Assumptions lane_{n}_local_selection.']
    return '\n'.join(lines)+'\n'

def check(ast_path,ast_module,output):
    ast,profile,paths=ownership.origin.raw_binding(ast_path,ast_module)
    plan=discover(ast);out=Path(output);out.mkdir(parents=True,exist_ok=False)
    (out/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    report=dict(accepted=False,rows=len(plan['rows']),residuals=plan['residuals'],old_inv_read=False,
        full_lfp_bit_connection_proved=False,isa_destination_proved=False,complete_R_generated=False)
    if plan['rows']:
        source=render(ast_module,profile['ast']['program'],ast['module'],plan['rows'])
        path=out/'FixedLaneEnable.v';path.write_text(source)
        flags=list(rtl.framework.FLAGS)
        for row in paths:flags+=['-R',row['directory'],row['namespace']]
        flags+=['-R',str(out.resolve()),'GeneratedFixedLaneEnable']
        start=time.monotonic();deadline=start+1200
        c,t=run_stage([str(rtl.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],out/'coqc.log',1200)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest())
        if c.returncode==0:
            closed=c.stdout.count('Closed under the global context')==len(plan['rows'])and'Axioms:'not in c.stdout
            k,t=run_stage([str(rtl.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedFixedLaneEnable.FixedLaneEnable'],out/'coqchk.log',max(.1,deadline-time.monotonic()))
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,accepted=k.returncode==0 and closed)
        report['seconds']=time.monotonic()-start
    else:report['status']='no_applicable_fixed_lane_decoder'
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for arg in ['ast','ast-module','output']:p.add_argument('--'+arg,required=True)
    a=p.parse_args();result=check(a.ast,a.ast_module,a.output)
    print(json.dumps({k:v for k,v in result.items()if k!='residuals'},indent=2))
    raise SystemExit(0 if result['accepted']else 1)
