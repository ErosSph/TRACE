"""Connect actual selector codes to boot-derived candidate token ownership."""
import argparse,json,time,hashlib
from pathlib import Path
import cpu_boot_selector_tokens as boot
from cpu_certificate_acceptance import run_stage
rtl=boot.reads.rtl

def requirement(needed,guard):
    if needed==guard:return 'apply requires_self.'
    if guard.name=='EBinary'and guard.args[1].name=='BAnd':
        w,_,a,b=guard.args
        for child,side in [(a,'left'),(b,'right')]:
            proof=requirement(needed,child)
            if proof:return f'eapply requires_trans;[|apply and_{side}]. {{ {proof} }}'
    if guard.name=='EBinary'and guard.args[0].name=='1'and guard.args[1].name=='BNeq':
        left,right=guard.args[2:]
        if left.name=='EConst'and left.args[1].name=='0'and right==needed:return 'apply neq_zero.'
    return None

def certificate(expr,width,code,needed):
    if expr.name=='EConst'and expr.args[0].name==str(width):
        value=int(expr.args[1].name)%(1<<width)
        return 'apply Impossible;vm_compute;discriminate.'if value!=code else None
    if expr.name!='ECond'or expr.args[0].name!=str(width):return None
    _,guard,yes,no=expr.args
    n=certificate(no,width,code,needed)
    if n is None:return None
    g=requirement(needed,guard)
    if g:return f'apply Guarded. {{ {g} }} {{ {n} }}'
    y=certificate(yes,width,code,needed)
    return f'apply Both. {{ {y} }} {{ {n} }}'if y else None

def output_codes(expr,width):
    if expr.name=='EConst'and expr.args[0].name==str(width):
        return {int(expr.args[1].name)%(1<<width)}
    if expr.name=='ECond'and expr.args[0].name==str(width):
        return output_codes(expr.args[2],width)|output_codes(expr.args[3],width)
    return set()

def register_matches(ast,rows):
    """Match actual compared source IDs to existing RF-address alias cones."""
    origins=boot.reads.origins
    addresses,residuals,cones,order=origins.discover(ast)
    if residuals:raise ValueError('unresolved source address cones')
    source_plan=boot.sources.discover(ast)
    unique={(r['width'],r['input']):r for r in source_plan['sources']if r['edges']}
    source_indices={key:i for i,key in enumerate(unique)}
    result=[]
    for row in rows:
        expr=rtl.Parser(row['selector']['expression']).complete();matches=[]
        rd=rtl.Parser(f'(EVar 5 {row["pair"]["rd"]})').complete()
        for eq in {n for n in rtl.walk(expr)if n.name=='EBinary'and n.args[0].name=='1'and n.args[1].name=='BEq'}:
            a,b=eq.args[2:]
            other=b if a==rd else a if b==rd else None
            if other is None or other.name!='EVar'or other.args[0].name!='5':continue
            root=int(other.args[1].name);wire=unique.get((5,root))
            proof=certificate(expr,row['selector']['width'],row['code'],eq)
            if not wire or not proof:continue
            for address in addresses:
                route=boot.sources.trace(ast,5,address['root'])
                if route['terminal']!=wire['terminal']:continue
                matches.append(dict(source=root,wire=source_indices[(5,root)],address=address['root'],
                    route=route,proof=proof,equality=rtl.render(eq),reversed=a!=rd))
        if len(matches)!=1:raise ValueError('selected code lacks unique current-source match')
        result.append(matches[0])
    return result,order

def discover(ast,stages):
    source_plan=boot.sources.discover(ast);pairs=boot.discover(source_plan,stages)
    selectors=boot.sources.selectors.discover(ast)['selected'];rows=[]
    for selector in selectors:
        expr=rtl.Parser(selector['expression']).complete();width=selector['width']
        codes=sorted(output_codes(expr,width))
        for i,pair in enumerate(pairs):
            # Only pair inputs used by this same controller output.
            inputs={r['input']for r in source_plan['sources']if r['selector']==selector['root']}
            if pair['rd']not in inputs or pair['write']not in inputs:continue
            for code in codes:
                needed=[rtl.Parser(f'(EVar {w} {pair[k]})').complete()for w,k in [(1,'write'),(5,'rd')]]
                proofs=[certificate(expr,width,code,e)for e in needed]
                if all(proofs):rows.append(dict(selector=selector,pair=pair,pair_index=i,code=code,proofs=proofs))
    return rows

def check(ast,module,history,out,with_matches=False,with_data=False):
    with_matches=with_matches or with_data
    overall_start=time.monotonic()
    out=Path(out);out.mkdir(parents=True,exist_ok=False);provider=out/'ownership'
    pr=boot.check(ast,module,history,provider)
    report=dict(accepted=False,ownership=pr,complete_R_generated=False,operand_freshness_proved=False,old_inv_read=False)
    def save():
        report['overall_seconds']=time.monotonic()-overall_start
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    if not pr['accepted']:return save()
    raw,profile,_=boot.reads.origins.origin.raw_binding(ast,module)
    _,v=boot.reads.provenance.hb.boot.chain.render(ast,module);rows=discover(raw,v['rows'])
    if not rows:report['residual']='no structurally certified selected candidate';return save()
    matches=[];address_ports={}
    if with_matches:
        matches,order=register_matches(raw,rows)
        _,analysis,_=boot.reads.origins.connected.comb.proposal(profile,order)
        if analysis['residuals']:raise ValueError('address aliases unresolved')
        address_ports={p['output_root']:i for i,p in enumerate(analysis['ports'])}
        (out/'matches.json').write_text(json.dumps(matches,indent=2)+'\n')
    (out/'plan.json').write_text(json.dumps(rows,indent=2)+'\n')
    selectors={r['selector']['root']:r['selector']for r in rows};source='';data_paths=[]
    if with_data:
        import cpu_selected_data_paths as data
        text,data_paths=data.render(ast,module,rows)
        source+='Module D.\n'+text+'\nEnd D.\n'
        (out/'data-paths.json').write_text(json.dumps(data_paths,indent=2)+'\n')
    for root,s in selectors.items():
        text,_,_=boot.sources.selectors.render(ast,module,s['process'],root)
        source+=f'Module S{root}.\n{text}\nEnd S{root}.\n'
    p=profile['ast']['program'];sample=f'(phase_driven_state {p} ev pre)'
    source+=f'''From Coq Require Import List ZArith.
Require Import {module} Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVCaptureBirth
 Lang.ExtendedSVSelectedGuard Lang.ExtendedSVWordInvariant Ex.External.CPUInstructionFields.
Require GeneratedSelectorBoot.SelectorBootTokens.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVCaptureBirth ExtendedSVSelectedGuard ExtendedSVWordInvariant CPUInstructionFields.
Module O:=GeneratedSelectorBoot.SelectorBootTokens.
Module H:=O.H.
Local Opaque {p} PhaseSemantics.
'''
    for i,r in enumerate(rows):
        s=r['selector'];pair=r['pair'];root=s['root'];width=s['width'];code=r['code'];stage=pair['stage']
        for j,(w,k)in enumerate([(1,'write'),(5,'rd')]):
            source+=f'''Lemma certificate_{i}_{j}:Certificate {width} {code}(EVar {w} {pair[k]})S{root}.selector_expression.
Proof. unfold S{root}.selector_expression. {r['proofs'][j]} Qed.
'''
        source+=f'''Theorem selected_{i}_has_token image events ev:
 let pre:=phase_run {p} events(H.F.boot image)in
 Forall H.W.Environment events ->H.W.Environment ev ->
 norm {width}(read_signal {sample} {root})={code}%Z ->
 exists token,H.C.C.chain_tag{stage}(snd(H.boot_history image events))=Some token /\\
 norm 5(read_signal {sample} {pair['rd']})=norm 5(H.C.C.chain_head_value(token_word token)).
Proof. intros pre HE HEv HS.
destruct(O.R.sample_evidence image events ev HE HEv)as[seed HL].
pose proof(S{root}.selector_actual_lfp seed _ HL)as HX;fold pre in HX;rewrite HX in HS.
exact(O.selector_{r['pair_index']}_enabled_token image events ev HE HEv
 (selected_requires _ _ _ _ certificate_{i}_0 _ HS)
 (selected_requires _ _ _ _ certificate_{i}_1 _ HS)). Qed.
'''
        if with_matches:
            m=matches[i];root=s['root'];a=m['address']
            # The field role comes from the checked RF address classifier.
            addresses,_,_,_=boot.reads.origins.discover(raw)
            classified=boot.reads.classify(addresses,v['entry']['capture']['carrier'])
            field=next(x['field']for x in classified if x['root']==a)
            term='eq_refl'
            for e in reversed(m['route']['edges']):
                step=f'(eq_trans(O.R.A.port_{address_ports[e["root"]]}_lfp seed _ HL)(norm_idempotent 5(read_signal {sample} {e["parent"]})))'
                term=f'(eq_trans {step} {term})'
            source+=f'''Lemma match_certificate_{i}:Certificate {width} {code} {m['equality']} S{root}.selector_expression.
Proof. unfold S{root}.selector_expression. {m['proof']} Qed.
Theorem selected_{i}_register_match image events ev consumer:
 let pre:=phase_run {p} events(H.F.boot image)in
 Forall H.W.Environment events ->H.W.Environment ev ->
 current(fst(H.boot_history image events))=Some consumer ->
 norm {width}(read_signal {sample} {root})={code}%Z ->
 exists producer,H.C.C.chain_tag{stage}(snd(H.boot_history image events))=Some producer /\\
 norm 5(H.C.C.chain_head_value(token_word producer))=field_reference(token_word consumer){field}.
Proof. intros pre HE HEv HC HS.
destruct(selected_{i}_has_token image events ev HE HEv HS)as[producer[HT HD]].
destruct(O.R.sample_evidence image events ev HE HEv)as[seed HL].
pose proof(S{root}.selector_actual_lfp seed _ HL)as HX;fold pre in HX;rewrite HX in HS.
pose proof(equality_nonzero _ _ _ (selected_requires _ _ _ _ match_certificate_{i} _ HS))as HM.
cbn[eval_expr]in HM.
pose proof(O.W.selector_source_{m['wire']} seed _ HL)as HW;fold pre in HW.
pose proof {term} as HA;fold pre in HA.
pose proof(O.R.address_{a}_current_token image events ev consumer HE HEv HC)as HR;fold pre in HR.
exists producer;split;[exact HT|].
exact(eq_trans(eq_sym HD)(eq_trans {'(eq_sym HM)'if m['reversed']else'HM'}(eq_trans HW(eq_trans(eq_sym HA)HR)))). Qed.
'''
            if with_data:
                d=data_paths[i]
                source+=f'''Theorem selected_{i}_physical_operand image events ev consumer:
 let pre:=phase_run {p} events(H.F.boot image)in
 Forall H.W.Environment events ->H.W.Environment ev ->
 current(fst(H.boot_history image events))=Some consumer ->
 norm {width}(read_signal {sample} {root})={code}%Z ->
 exists producer,H.C.C.chain_tag{stage}(snd(H.boot_history image events))=Some producer /\\
 norm 5(H.C.C.chain_head_value(token_word producer))=field_reference(token_word consumer){field} /\\
 norm 32(read_signal {sample} {d['output']})=norm 32(read_signal {sample} {d['data']['terminal']}).
Proof. intros pre HE HEv HC HS.
destruct(selected_{i}_register_match image events ev consumer HE HEv HC HS)as[producer[HT HR]].
destruct(O.R.sample_evidence image events ev HE HEv)as[seed HL].
exists producer;split;[exact HT|];split;[exact HR|exact(D.data_{i}_lfp seed _ HL HS)]. Qed.
'''
    source+='Goal True. idtac "SELECTED_TOKEN_AUDIT". exact I. Qed.\n'
    source+=''.join(f'Print Assumptions selected_{i}_has_token.\n'for i in range(len(rows)))
    if with_matches:source+=''.join(f'Print Assumptions selected_{i}_register_match.\n'for i in range(len(rows)))
    if with_data:source+=''.join(f'Print Assumptions selected_{i}_physical_operand.\n'for i in range(len(rows)))
    path=out/'SelectedTokens.v';path.write_text(source)
    flags=list(rtl.framework.FLAGS)
    for r in json.loads((Path(history)/'plan.json').read_text())['paths']:flags+=['-R',r['directory'],r['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedSelectedTokens','-R',str(provider.resolve()),'GeneratedSelectorBoot','-R',str((provider/'reads').resolve()),'GeneratedCapturedReads']
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(boot.reads.origins.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],out/'coqc.log',1200)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),selected_cases=len(rows))
    if c.returncode==0:
        tail=c.stdout.split('SELECTED_TOKEN_AUDIT\n')[-1]
        report['assumptions_closed']=tail.count('Closed under the global context')==len(rows)*(1+int(with_matches)+int(with_data))and 'Axioms:'not in tail
        k,t=run_stage([str(boot.reads.origins.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedSelectedTokens.SelectedTokens'],out/'coqchk.log',max(.1,deadline-time.monotonic()))
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0 and report['assumptions_closed'])
    report['register_matches_proved']=len(matches)if report['accepted']else 0
    report['physical_operand_paths_proved']=len(data_paths)if report['accepted']else 0
    report['seconds']=time.monotonic()-start;return save()

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for k in ['ast','ast-module','history-provider','output']:p.add_argument('--'+k,required=True)
    p.add_argument('--with-matches',action='store_true')
    p.add_argument('--with-data',action='store_true')
    a=p.parse_args();r=check(a.ast,a.ast_module,a.history_provider,a.output,a.with_matches,a.with_data);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
