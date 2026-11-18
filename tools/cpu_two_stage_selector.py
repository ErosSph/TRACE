"""Match and prove an actual two-producer ready selector normal form.

First/second priority is structural. Program-age and value correspondence
remain separate obligations and are not inferred from branch position.
"""
import argparse,json,hashlib,time
from pathlib import Path
import cpu_blocking_selector as selectors
from cpu_certificate_acceptance import run_stage
rtl=selectors.rtl


def conjuncts(e):
    if e.name=='EBinary' and e.args[:2]==(rtl.Term('1'),rtl.Term('BAnd')):
        return conjuncts(e.args[2])+conjuncts(e.args[3])
    return [e]


def var(e,width):
    if e.name!='EVar' or e.args[0].name!=str(width):raise ValueError('unexpected scalar variable')
    return int(e.args[1].name)


def branch(guard,negative):
    atoms=conjuncts(guard);neq=[e for e in atoms if e.name=='EBinary' and e.args[1].name=='BNeq']
    eq=[e for e in atoms if e.name=='EBinary' and e.args[1].name=='BEq']
    if len(neq)!=1 or len(eq)!=1:raise ValueError('unique destination/nonzero/source tests required')
    n=neq[0];a,b=n.args[2:]
    if a.name!='EConst' or int(a.args[1].name)%(1<<int(a.args[0].name))!=0:raise ValueError('normalized zero destination guard required')
    rd=var(b,5);x,y=eq[0].args[2:]
    rs=var(y,5)if var(x,5)==rd else var(x,5)if var(y,5)==rd else None
    if rs is None:raise ValueError('source comparison does not use destination')
    rest=[e for e in atoms if e not in neq+eq]
    if negative:
        neg=[e for e in rest if e.name=='EUnary' and e.args[:2]==(rtl.Term('1'),rtl.Term('UNot'))]
        if len(neg)!=1:raise ValueError('one negated readiness flag required')
        load=var(neg[0].args[2],1);rest.remove(neg[0])
        if len(rest)!=1:raise ValueError('one write enable required')
        write=var(rest[0],1)
        return dict(write=write,rd=rd,rs=rs,load=load)
    if len(rest)!=2:raise ValueError('positive load/write pair required')
    return dict(rd=rd,rs=rs,flags=sorted(var(e,1)for e in rest))


def match(expression):
    e=expression;guards=[]
    for code in [1,2,3]:
        if e.name!='ECond' or e.args[0].name!='2':raise ValueError('three two-bit priority branches required')
        _,g,yes,e=e.args
        if yes.name!='EConst' or yes.args[0].name!='2' or int(yes.args[1].name)%4!=code:
            raise ValueError('unexpected normalized selector code')
        guards.append(g)
    if e.name!='EConst' or e.args[0].name!='2' or int(e.args[1].name)%4!=0:raise ValueError('zero fallback required')
    first,second,last=branch(guards[0],True),branch(guards[1],True),branch(guards[2],False)
    if first['rs']!=second['rs'] or last!={k:second[k]for k in ['rd','rs']}|{'flags':sorted([second['write'],second['load']])}:
        raise ValueError('split readiness branches refer to different producers')
    return dict(first=first,second=second)


def check(ast,module,output):
    raw,profile,paths=selectors.origin.raw_binding(ast,module)
    rows=[];residuals=[];source=''
    for s in selectors.discover(raw)['selected']:
        try:binding=match(rtl.Parser(s['expression']).complete())
        except ValueError as error:residuals.append(dict(root=s['root'],reason=str(error)));continue
        rows.append(dict(selector=s,binding=binding))
        text,_,_=selectors.render(ast,module,s['process'],s['root']);source+=f'Module S{s["root"]}.\n'+text+f'\nEnd S{s["root"]}.\n'
    if not rows:raise ValueError('no supported ready selector')
    p=profile['ast']['program']
    source+=f'''From Coq Require Import ZArith.
Require Import {module} Lang.ExtendedSV Lang.ExtendedSVStallFlush Ex.External.CPUTwoStageReadySelection.
Import ExtendedSV ExtendedSVStallFlush CPUTwoStageReadySelection.
Definition bit s root:=(norm 1(read_signal s root)=?1)%Z.
Local Opaque {p}.
Local Transparent norm mask eval_expr.
Local Opaque Z.eqb.
'''
    for row in rows:
        s=row['selector'];first,second=row['binding']['first'],row['binding']['second'];root=s['root']
        def args():
            return f"(bit fixed {second['write']})(norm 5(read_signal fixed {second['rd']}))(bit fixed {second['load']})(bit fixed {first['write']})(norm 5(read_signal fixed {first['rd']}))(bit fixed {first['load']})(norm 5(read_signal fixed {first['rs']}))"
        source+=f'''Theorem selector_{root}_normal_form seed fixed:CombLFP {p} seed fixed ->
 norm 2(read_signal fixed {root})=selected_code {args()}.
Proof. intro HL;rewrite(S{root}.selector_actual_lfp seed fixed HL).
 unfold S{root}.selector_expression,selected_code,eligible,bit;cbn[eval_expr].
 replace(norm 5 0%Z)with 0%Z by(vm_compute;reflexivity).
'''
        # Canonicalize the actual destination/source comparisons before splitting.
        for producer in [first,second]:
            rd,rs=producer['rd'],producer['rs']
            source+=f'rewrite ?(Z.eqb_sym 0(norm 5(read_signal fixed {rd}))),?(Z.eqb_sym(norm 5(read_signal fixed {rd}))(norm 5(read_signal fixed {rs}))).\n'
        flags=sorted({r[k]for r in [first,second]for k in ['write','load']})
        for flag in flags:source+=f'destruct(one_bit_cases fixed {flag})as[H{flag}|H{flag}];rewrite H{flag}.\nall: '
        comparisons=[f'(norm 5(read_signal fixed {r["rd"]}%nat)=?0)%Z'for r in [first,second]]+[f'(norm 5(read_signal fixed {first["rs"]}%nat)=?norm 5(read_signal fixed {r["rd"]}%nat))%Z'for r in [first,second]]
        source+=';'.join('destruct '+e for e in comparisons)+';cbn[Z.eqb];reflexivity. Qed.\n'
    source+='Goal True. idtac "READY_SELECTOR_AUDIT". exact I. Qed.\n'
    source+=''.join(f'Print Assumptions selector_{r["selector"]["root"]}_normal_form.\n'for r in rows)
    out=Path(output);out.mkdir(parents=True,exist_ok=False);file=out/'ReadySelector.v';file.write_text(source)
    (out/'plan.json').write_text(json.dumps(dict(rows=rows,residuals=residuals,ast_sha256=raw['source_sha256']),indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for path in paths:flags+=['-R',path['directory'],path['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedReadySelector'];start=time.monotonic()
    cc,t=run_stage([str(selectors.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),complete_R_generated=False,program_age_proved=False)
    if cc.returncode==0 and time.monotonic()-start<1200:
        kk,t=run_stage([str(selectors.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedReadySelector.ReadySelector'],out/'coqchk.log',1200-(time.monotonic()-start))
        tail=cc.stdout.split('READY_SELECTOR_AUDIT')[-1];closed=tail.count('Closed under the global context')==len(rows)and'Axioms:'not in tail
        report.update(coqchk_exit=kk.returncode,assumptions_closed=closed,accepted=kk.returncode==0 and closed)
    report['seconds']=time.monotonic()-start;(out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['ast','ast-module','output']:p.add_argument('--'+key,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
