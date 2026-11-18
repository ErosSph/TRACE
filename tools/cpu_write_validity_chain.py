"""Infer aligned Rd/write/valid pipeline triples and prove real phase transport.

Where the capture/Rd/AND-gate pattern matches, discharge the entry relation
using the whole-controller certificate; otherwise retain it explicitly.
The RF branch, all scalar writers and every alias are found in the raw AST.
"""
import argparse, hashlib, json, time
from pathlib import Path
import cpu_write_destination_history as history
import cpu_capture_chain_coverage as coverage
import cpu_single_bank_branch as bank
import cpu_guarded_write as guarded
import cpu_invalid_capture_projection as invalid
from cpu_pending_retirement import alias_route
from cpu_certificate_acceptance import run_stage
origin=coverage.capture.birth.origin
rtl=coverage.capture.birth.rtl


def shape(e, width):
    if (e.name=='ECond' and e.args[0].name==str(width) and
        e.args[2].name=='EVar' and e.args[2].args[0].name==str(width) and
        e.args[3]==rtl.Term('EConst',(rtl.Term(str(width)),rtl.Term('0')))):
        return e.args[1],int(e.args[2].args[1].name)
    return None


def discover(ast):
    targets,_=history.discover(ast)
    if len(targets)!=1:raise ValueError('unique registered destination chain required')
    target=targets[0];data=coverage.capture.discover(ast,set(target['roots']))
    cov=coverage.coverage.discover(ast,relations=coverage.relations(data))
    byrd={r['root']:r for r in cov['covered_fields']}
    scalars={r['root']:r for r in coverage.coverage.connected.scalar_candidates(ast)}
    bits={r for r,x in scalars.items() if x['width']==1}
    sink=target['aliases'][0] if target['aliases'] else target['endpoint']
    branches=bank.discover(ast,sink)
    candidates=[]
    for branch in branches:
        for guard,taken in branch['guards']:
            if not taken:continue
            for term in rtl.walk(rtl.Parser(guard).complete()):
                if term.name!='EVar' or term.args[0].name!='1':continue
                route=alias_route(ast,int(term.args[1].name),1,bits)
                if route and scalars[route['terminal']]['process']==scalars[target['endpoint']]['process']:
                    candidates.append(route)
    unique={r['terminal']:r for r in candidates}
    if len(unique)!=1:raise ValueError('RF enable-to-final-stage route is ambiguous or absent')
    sink_route=next(iter(unique.values()));write=sink_route['terminal'];rows=[]
    original=data['chain']['rows']
    for pos in reversed(range(len(original))):
        rd=original[pos]['root'];valid=byrd[rd]['valid_root']
        xs=[scalars[r] for r in (rd,write,valid)]
        ss=[shape(x['expression'],x['width']) for x in xs]
        if any(s is None for s in ss) or len({x['process'] for x in xs})!=1 or len({rtl.render(s[0]) for s in ss})!=1:
            raise ValueError('triple does not share one reset/capture process')
        row=dict(rd=rd,write=write,valid=valid,process=xs[0]['process'],
                 guard=rtl.render(ss[0][0]),inputs=[s[1] for s in ss],routes=[])
        if pos:
            previous=original[pos-1]['root'];previous_valid=byrd[previous]['valid_root']
            routes=[alias_route(ast,ss[0][1],5,{previous}),
                    alias_route(ast,ss[1][1],1,bits),
                    alias_route(ast,ss[2][1],1,{previous_valid})]
            if any(r is None for r in routes):raise ValueError('incomplete triple alias connection')
            previous_write=routes[1]['terminal']
            if scalars[previous_write]['process']!=original[pos-1]['process']:
                raise ValueError('write-enable and Rd belong to different stages')
            row['routes']=routes;write=previous_write
        rows.append(row)
    rows=list(reversed(rows))
    cones=coverage.coverage.BitCones(ast)
    expressions=[rtl.Term('EVar',(rtl.Term(str(w)),rtl.Term(str(r))))for w,r in zip([5,1,1],rows[0]['inputs'])]
    expanded=[cones.expand(e)for e in expressions]
    def strip(e):
        if e.name=='EExtend' and e.args[1].name=='false':return strip(e.args[2])
        return rtl.Term(e.name,tuple(strip(x)if x.name.startswith('E')else x for x in e.args))
    rdexp,weexp,vexp=map(strip,expanded)
    capture=data['connection']['capture'] if data['connection'] else None
    control=guarded.discover(ast);entry=None
    if capture:
        carrier,valid=capture['carrier'],capture['valid_root']
        expected=rtl.Parser(f'(ESel 5 (EVar 32 {carrier}) (EConst 5 7))').complete()
        for index,pair in enumerate(control):
            bit=lambda r:rtl.Parser(f'(EVar 1 {r})').complete()
            if (rdexp==expected and weexp==bit(pair['write']) and
                vexp.name=='EBinary' and vexp.args[:2]==(rtl.Term('1'),rtl.Term('BAnd')) and
                set(vexp.args[2:])=={bit(valid),bit(pair['gate'])}):
                order=cones.closure(expressions)
                entry=dict(capture=capture,control_index=index,gate=pair['gate'],write=pair['write'],
                    cone_order=order,expanded=[rtl.render(e)for e in expanded])
    sink_enable=sink_route['edges'][0]['root'] if sink_route['edges'] else sink_route['terminal']
    guard=f'(EBinary 1 BAnd (EVar 1 {sink_enable}) (EBinary 1 BNeq (EConst 5 0) (EVar 5 {sink})))'
    if not any((guard,True) in [(g,bool(t))for g,t in b['guards']]for b in branches):
        raise ValueError('unsupported actual write branch shape')
    address_route=alias_route(ast,sink,5,{target['endpoint']})
    if address_route is None:raise ValueError('write address route missing')
    return dict(rows=rows,sink_route=sink_route,entry=entry,sink_enable=sink_enable,
                sink_index=sink,address_route=address_route,write_guard=guard,
                entry_relation_proved=False,complete_R_generated=False,old_inv_read=False)


def render(ast_path,module):
    ast,profile,paths=origin.raw_binding(ast_path,module);data=discover(ast)
    rows=data['rows'];roots=sorted({r[k] for r in rows for k in ('rd','write','valid')})
    entry=data['entry']
    if entry:roots=sorted(set(roots)|{entry['capture']['carrier'],entry['capture']['valid_root']})
    _,residuals,outputs,scalar_source,_=origin.expressions.proposal(profile,roots)
    if residuals:raise ValueError('scalar certificate gap')
    aliasroots=sorted({e['root'] for r in rows for route in r['routes'] for e in route['edges']})
    aliasroots=sorted(set(aliasroots)|{e['root']for route in[data['sink_route'],data['address_route']]for e in route['edges']})
    if entry:aliasroots=sorted(set(aliasroots)|set(entry['cone_order']))
    _,ports,comb_source=coverage.coverage.connected.comb.proposal(profile,aliasroots)
    if ports['residuals']:raise ValueError('alias certificate gap')
    indices={x['output_root']:i for i,x in enumerate(ports['ports'])}
    p=profile['ast']['program']
    lines=['From Coq Require Import List ZArith.',f'Require Import Lang.ExtendedSV {module}.',
        'Module P.',scalar_source,'End P.','Module W.',comb_source,'End W.',
        'Require Import Lang.ExtendedSVWriteValidity Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression Lang.ExtendedSVWordInvariant.',
        'Import ExtendedSV ExtendedSVWriteValidity ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVWordInvariant.',
        f'Local Opaque {p}.']
    if entry:
        gs,_=guarded.render(ast_path,module)
        lines += [f'Local Transparent {p}.','Module G.',gs,'End G.',
            'Require Import Ex.External.CPUInstructionFields Ex.External.CPUInstructionFieldAlias Lang.ExtendedSVInvalidProjection Lang.ExtendedSVStallFlush.',
            'Import CPUInstructionFields CPUInstructionFieldAlias ExtendedSVStallFlush.',f'Local Opaque {p}.']
    for x in outputs:
        r=x['root'];w=x['width'];proc=ast['module']+'.'+x['process']
        lines += [f'Lemma self_{r}:self_widthb {w} {r} P.root_{r}_expression=true. Proof. vm_compute;reflexivity. Qed.',
                  f'Definition cert_{r}:ScalarCertificate {p} {r} {w} {proc} P.root_{r}_expression:=Build_ScalarCertificate _ _ _ _ _ P.root_{r}_comb_frame self_{r} P.root_{r}_expression_phase.']
    n=len(rows)
    lines += ['Definition PipelineEligible s:Prop:='+ ' /\\ '.join(f'Eligible 5 {r["rd"]} {r["write"]} {r["valid"]} s' for r in rows)+'.',
        'Definition EntryEligible s:Prop:=InputsEligible 5 '+ ' '.join(f'(EVar {w} {root})' for w,root in zip([5,1,1],rows[0]['inputs']))+' s.',
        'Definition Boundary ev:Prop:='+ ' /\\ '.join(f'changed_signal ev<>{r}%nat' for r in roots)+'.']
    for i,row in enumerate(rows):
        rd,we,va=row['rd'],row['write'],row['valid'];proc=ast['module']+'.'+row['process']
        localpred='EntryEligible pre' if i==0 else f'Eligible 5 {rows[i-1]["rd"]} {rows[i-1]["write"]} {rows[i-1]["valid"]} pre'
        lines += [f'Lemma stage_{i}_inputs seed pre:CombLFP {p} seed pre ->{localpred} ->',
            f'InputsEligible 5 P.root_{rd}_expression P.root_{we}_expression P.root_{va}_expression pre.',
            f'Proof. intros HL HI;unfold P.root_{rd}_expression,P.root_{we}_expression,P.root_{va}_expression;apply reset_choices.']
        if i==0:lines+=['exact HI. Qed.']
        else:
            lines+=['unfold InputsEligible;cbn[eval_expr];rewrite !norm_idempotent.']
            for route in row['routes']:
                for edge in route['edges']:
                    j=indices[edge['root']]
                    lines += [f'rewrite(W.port_{j}_lfp seed pre HL);unfold W.port_{j}_rhs;cbn[eval_expr];rewrite norm_idempotent.']
            lines+=['exact HI. Qed.']
    lines += [f'Theorem actual_pipeline_phase seed ev pre:Boundary ev ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
        f'EntryEligible(phase_driven_state {p} ev pre) ->PipelineEligible pre ->PipelineEligible(PhaseSemantics {p} ev pre).',
        'Proof. intros HB HL HE HP;unfold Boundary in HB;unfold PipelineEligible in HP|-*.',
        'destruct HB as['+''.join(f'E{r} [' for r in roots[:-2])+f'E{roots[-2]} E{roots[-1]}'+']'*(len(roots)-1)+'.',
        ('rename HP into H0.' if n==1 else 'destruct HP as['+''.join(f'H{i} ['for i in range(n-2))+f'H{n-2} H{n-1}'+']'*(n-1)+'.')]
    for i,row in enumerate(rows):
        rd,we,va=row['rd'],row['write'],row['valid'];proc=ast['module']+'.'+row['process']
        lines += [f'assert(O{i}:Eligible 5 {rd} {we} {va}(PhaseSemantics {p} ev pre)).',
            f'{{ apply(actual_stage {p} 5 {rd} {we} {va} {proc} _ _ _ cert_{rd} cert_{we} cert_{va} ev pre E{rd} E{we} E{va} H{i}).',
            f' apply(stage_{i}_inputs seed _ HL).']
        if i==0:lines+=['exact HE. }']
        else:
            u=rows[i-1];a,b,c=u['rd'],u['write'],u['valid']
            lines += [f'exact(sampled_eligible {p} 5 {a} {b} {c} ev pre P.root_{a}_comb_frame P.root_{b}_comb_frame P.root_{c}_comb_frame E{a} E{b} E{c} H{i-1}). }}']
    for i in range(n-1):lines += [f'split;[exact O{i}|].']
    lines += [f'exact O{n-1}. Qed.']
    exports=1
    if entry:
        cap=entry['capture'];word,valid=cap['carrier'],cap['valid_root'];gate,write=entry['gate'],entry['write']
        ri,wi,vi=rows[0]['inputs']
        lines += [f'Definition CaptureSafe s:=ExtendedSVInvalidProjection.Related 32 {word} {valid}(fun code=>field_reference code Rd)s.']
        for label,root,width,rhs in [
            ('rd',ri,5,f'field_reference(norm 32(read_signal pre {word}))Rd'),
            ('write',wi,1,f'norm 1(read_signal pre {write})'),
            ('valid',vi,1,f'norm 1(Z.land(norm 1(read_signal pre {valid}))(norm 1(read_signal pre {gate})))')]:
            lines += [f'Lemma entry_{label} seed pre:CombLFP {p} seed pre ->norm {width}(read_signal pre {root})={rhs}.',
                      'Proof. intro HL.']
            for r in reversed(entry['cone_order']):
                j=indices[r]
                lines += [f'try rewrite(W.port_{j}_lfp seed pre HL);try unfold W.port_{j}_rhs;cbn[eval_expr];repeat rewrite norm_idempotent.']
            if label=='rd':
                lines += [f'change(eval_expr pre(field_expr {word} Rd)=field_reference(norm 32(read_signal pre {word}))Rd).',
                    'rewrite field_value,field_reference_normalized;reflexivity. Qed.']
            elif label=='valid':lines += ['try rewrite Z.land_comm;reflexivity. Qed.']
            else:lines += ['reflexivity. Qed.']
        ci=entry['control_index']
        lines += [f'Theorem entry_from_capture seed pre:CombLFP {p} seed pre ->CaptureSafe pre ->EntryEligible pre.',
            'Proof. intros HL HC;unfold EntryEligible,InputsEligible;cbn[eval_expr];rewrite !norm_idempotent.',
            'rewrite(entry_rd seed pre HL),(entry_write seed pre HL),(entry_valid seed pre HL).',
            f'intros HW HD;pose proof(G.pair_{ci}_actual_lfp seed pre HL HW)as HG.',
            f'assert(HV:norm 1(read_signal pre {valid})<>0%Z)by(intro H;apply HD;exact(HC H)).',
            f'destruct(one_bit_cases pre {valid})as[HZ|HO];[contradiction|].',
            f'destruct(one_bit_cases pre {gate})as[GZ|GO];[contradiction|].',
            'rewrite HO,GO;discriminate. Qed.']
        wordexpr=rtl.Parser(cap['word_expression']).complete();validexpr=rtl.Parser(cap['valid_expression']).complete()
        script=invalid.proof(wordexpr,validexpr,word,valid)
        if script is None:raise ValueError('capture invalid-Rd preservation unsupported')
        lines += ['Import ExtendedSVInvalidProjection.',
            f'Lemma capture_rule s:CaptureSafe s ->norm 1(eval_expr s P.root_{valid}_expression)=0%Z ->field_reference(norm 32(eval_expr s P.root_{word}_expression))Rd=0%Z.',
            f'Proof. intro HI;unfold P.root_{word}_expression,P.root_{valid}_expression. {script} Qed.',
            'Definition WriteValidityInvariant s:=CaptureSafe s /\\ PipelineEligible s.',
            f'Theorem actual_write_validity_phase seed ev pre:Boundary ev ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
            f'WriteValidityInvariant pre ->WriteValidityInvariant(PhaseSemantics {p} ev pre).',
            'Proof. intros HB HL [HC HP].',
            'assert(HBcopy:=HB);unfold Boundary in HBcopy.',
            'destruct HBcopy as['+''.join(f'E{r} ['for r in roots[:-2])+f'E{roots[-2]} E{roots[-1]}'+']'*(len(roots)-1)+'.',
            f'assert(HS:CaptureSafe(phase_driven_state {p} ev pre)).',
            f'{{ unfold CaptureSafe,ExtendedSVInvalidProjection.Related in *;rewrite(sampled_root_preserved {p} ev pre {word} P.root_{word}_comb_frame E{word}),',
            f'(sampled_root_preserved {p} ev pre {valid} P.root_{valid}_comb_frame E{valid});exact HC. }}',
            'split.',
            f'- exact(ExtendedSVInvalidProjection.phase_preserves {p} 32 {word} {valid} {ast["module"]+"."+cap["process"]} _ _ (fun code=>field_reference code Rd) cert_{word} cert_{valid} capture_rule ev pre E{word} E{valid} HC).',
            '- exact(actual_pipeline_phase seed ev pre HB HL(entry_from_capture seed _ HL HS)HP). Qed.']
        exports+=2
        end=rows[-1];rd,we,va=end['rd'],end['write'],end['valid'];sample=f'(phase_driven_state {p} ev pre)'
        lines += [f'Theorem actual_write_branch_valid seed ev pre:Boundary ev ->CombLFP {p} seed {sample} ->',
            f'WriteValidityInvariant pre ->Z.eqb(eval_expr {sample} {data["write_guard"]})0=false ->norm 1(read_signal pre {va})<>0%Z.',
            'Proof. intros HB HL [HC HP] HG;unfold Boundary in HB.',
            'destruct HB as['+''.join(f'E{r} ['for r in roots[:-2])+f'E{roots[-2]} E{roots[-1]}'+']'*(len(roots)-1)+'.',
            f'destruct(enabled_nonzero_guard 5 {data["sink_enable"]} {data["sink_index"]} {sample} HG)as[HW HD].']
        for name,route,width,root in [('HW',data['sink_route'],1,we),('HD',data['address_route'],5,rd)]:
            for edge in route['edges']:
                j=indices[edge['root']]
                lines += [f'rewrite(W.port_{j}_lfp seed _ HL)in {name};unfold W.port_{j}_rhs in {name};cbn[eval_expr]in {name};rewrite norm_idempotent in {name}.']
            lines += [f'rewrite(sampled_root_preserved {p} ev pre {root} P.root_{root}_comb_frame E{root})in {name}.']
        component='HP'
        for _ in range(n-1):component=f'(proj2 {component})'
        lines += [f'exact({component} HW HD). Qed.'];exports+=1
    lines += [
        'Goal True. idtac "WRITE_VALIDITY_AUDIT". exact I. Qed.',
        'Print Assumptions actual_pipeline_phase.']
    if entry:lines+=['Print Assumptions entry_from_capture. Print Assumptions actual_write_validity_phase. Print Assumptions actual_write_branch_valid.']
    return '\n'.join(lines)+'\n',dict(**data,paths=paths,ast_sha256=ast['source_sha256'],exports=exports)


def check(ast_path,module,output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    try:source,data=render(ast_path,module)
    except ValueError as error:
        result=dict(accepted=False,native_started=False,residual=str(error),complete_R_generated=False,entry_relation_proved=False,old_inv_read=False)
        (out/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result
    path=out/'WriteValidity.v';path.write_text(source)
    (out/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for x in data['paths']:flags+=['-R',x['directory'],x['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedWriteValidity'];start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],out/'coqc.log',1200)
    result=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,complete_R_generated=False,entry_relation_proved=False,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),ast_sha256=data['ast_sha256'],old_inv_read=False,
        initialization_proved=False,isa_result_value_proved=False)
    if c.returncode==0 and time.monotonic()<deadline:
        audit=c.stdout.split('WRITE_VALIDITY_AUDIT')[-1]
        closed=audit.count('Closed under the global context')==data['exports'] and 'Axioms:'not in audit
        k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedWriteValidity.WriteValidity'],out/'coqchk.log',deadline-time.monotonic())
        result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,accepted=closed and k.returncode==0)
        result['entry_relation_proved']=bool(data['entry']) and result['accepted']
        result['write_validity_preservation_proved']=result['entry_relation_proved']
        result['actual_write_branch_validity_proved']=result['entry_relation_proved']
    result['seconds']=time.monotonic()-start
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ['ast','ast-module','output']:parser.add_argument('--'+key,required=True)
    args=parser.parse_args();result=check(args.ast,args.ast_module,args.output)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
