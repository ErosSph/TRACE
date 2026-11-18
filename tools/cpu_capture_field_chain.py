"""Connect raw-AST capture identities to generated field chains.

Capture identity is NOT ISA admission. No existing CPU invariant is read.
"""
import argparse, hashlib, json, re, time
from pathlib import Path
import cpu_field_chain_history as chain
import cpu_pending_capture_birth as birth
from cpu_pending_retirement import alias_route
from cpu_certificate_acceptance import run_stage

def discover(ast,selected_roots=None):
    fields=chain.discover(ast,selected_roots) if selected_roots is not None else chain.discover(ast)
    captures=birth.discover(ast)['captures']
    result=dict(chain=fields,captures=captures,connection=None)
    if fields['head'] is None:return result
    terminals={r['carrier']:r for r in captures
               if sum(x['carrier']==r['carrier']for x in captures)==1}
    route=alias_route(ast,fields['head']['source'],32,terminals)
    if route is not None:
        result['connection']=dict(route=route,capture=terminals[route['terminal']])
    return result

def render(ast_path,ast_module,selected_roots=None):
    ast,profile,paths=birth.origin.raw_binding(ast_path,ast_module)
    data=discover(ast,selected_roots)
    if data['connection'] is None:return None,dict(**data,paths=paths)
    cs,_=chain.render(ast_path,ast_module,selected_roots)
    _,bs=birth.render(ast_path,ast_module)
    link=data['connection'];row=link['capture'];root=row['carrier'];valid=row['valid_root']
    roots=[e['root']for e in link['route']['edges']]
    _,ports,ws=chain.rf.comb.proposal(profile,roots)
    if ports['residuals']:raise ValueError('capture alias certificate residual')
    indices={r['output_root']:i for i,r in enumerate(ports['ports'])}
    program=profile['ast']['program'];source=data['chain']['head']['source']
    lines=['From Coq Require Import List ZArith.',f'Require Import {ast_module}.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory Lang.ExtendedSVHistoryChain Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCoveredField Lang.ExtendedSVScalarExpression.',
        'Import ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory ExtendedSVCaptureBirth ExtendedSVCoveredField ExtendedSVScalarExpression.',
        f'Local Opaque {program}.',
        'Theorem captured_chain_input seed ev pre g:',
        f'CombLFP {program} seed(phase_driven_state {program} ev pre) ->',
        f'changed_signal ev<>{root}%nat ->Invariant {root} {valid} pre g ->',
        f'forall token,current g=Some token ->norm 32(read_signal(phase_driven_state {program} ev pre){source})=norm 32(token_word token).',
        'Proof. intros HL HE HI token HT.']
    for edge in link['route']['edges']:
        i=indices[edge['root']]
        lines += [f'rewrite(W.port_{i}_lfp seed _ HL);unfold W.port_{i}_rhs;cbn[eval_expr];rewrite norm_idempotent.']
    lines += [f'rewrite(sampled_root_preserved {program} ev pre {root}(history_comb_frame _ _ _ _ _ B.root_{root}_birth_certificate)HE).',
        'destruct HI as[[HC HV]Hrest]. exact(HV token HT). Qed.',
        'Theorem captured_chain_boundary seed ev pre g:',
        f'CombLFP {program} seed(phase_driven_state {program} ev pre) ->',
        f'changed_signal ev<>{root}%nat ->Invariant {root} {valid} pre g ->']
    n=len(data['chain']['rows'])
    for r in data['chain']['rows']:lines += [f'changed_signal ev<>{r["root"]}%nat ->']
    lines += ['C.ChainBoundary token_word ev pre(current g).',
        'Proof. intros HL HE HI '+' '.join(f'HE{i}'for i in range(n))+'.',
        'exists seed;split;[exact HL|].']
    for i in range(n):lines += [f'split;[exact HE{i}|].']
    lines += ['exact(captured_chain_input seed ev pre g HL HE HI). Qed.',
        'Theorem captured_chain_phase seed ev pre g tags:',
        f'CombLFP {program} seed(phase_driven_state {program} ev pre) ->',
        f'changed_signal ev<>{root}%nat ->Invariant {root} {valid} pre g ->']
    for r in data['chain']['rows']:lines += [f'changed_signal ev<>{r["root"]}%nat ->']
    lines += ['C.ChainRelated token_word pre tags ->',
        f'C.ChainRelated token_word(PhaseSemantics {program} ev pre)(C.advance_tags ev pre tags(current g)).',
        'Proof. intros HL HE HI '+' '.join(f'HE{i}'for i in range(n))+' HR.',
        'exact(C.chain_history_step token_word ev pre tags(current g) HR',
        '(captured_chain_boundary seed ev pre g HL HE HI '+' '.join(f'HE{i}'for i in range(n))+')). Qed.']
    bi=data['captures'].index(row)
    lines += ['Definition Packed:Type:=(Ghost * @C.ChainTags Token)%type.',
        f'Definition CapturedFields pre(packed:Packed):=Invariant {root} {valid} pre(fst packed) /\\ C.ChainRelated token_word pre(snd packed).',
        f'Definition advance_capture_fields ev pre(packed:Packed)(unused:unit):Packed:=(B.capture_{bi}_step ev pre(fst packed),C.advance_tags ev pre(snd packed)(current(fst packed))).',
        'Definition CaptureFieldBoundary ev pre(unused:unit):Prop:=exists seed,',
        f'CombLFP {program} seed(phase_driven_state {program} ev pre) /\\ changed_signal ev<>{root}%nat /\\ changed_signal ev<>{valid}%nat /\\ '+
        ' /\\ '.join(f'changed_signal ev<>{r["root"]}%nat'for r in data['chain']['rows'])+'.',
        'Lemma capture_fields_step ev pre packed unused:CapturedFields pre packed ->CaptureFieldBoundary ev pre unused ->',
        f'CapturedFields(PhaseSemantics {program} ev pre)(advance_capture_fields ev pre packed unused).',
        'Proof. destruct packed as[g tags];intros[HI HR].',
        'intros[seed [HL [HE [HV '+''.join(f'[HE{i} 'for i in range(n-1))+f'HE{n-1}'+']'*(n+3)+'.',
        'split.',
        f'- exact(B.capture_{bi}_phase ev pre g HE HV HI).',
        '- exact(captured_chain_phase seed ev pre g tags HL HE HI '+' '.join(f'HE{i}'for i in range(n))+' HR). Qed.',
        f'Definition CapturedExecution:=ExtendedSVHistoryChain.Execution {program} Packed unit advance_capture_fields CaptureFieldBoundary.',
        'Theorem capture_fields_history pre packed events post final:CapturedExecution pre packed events post final ->CapturedFields pre packed ->CapturedFields post final.',
        f'Proof. exact(ExtendedSVHistoryChain.preserves {program} Packed unit advance_capture_fields CaptureFieldBoundary CapturedFields capture_fields_step pre packed events post final). Qed.',
        'Theorem capture_fields_erases pre packed events post final:CapturedExecution pre packed events post final ->',
        f'post=phase_run {program} events pre.',
        f'Proof. exact(ExtendedSVHistoryChain.erases {program} Packed unit advance_capture_fields CaptureFieldBoundary pre packed events post final). Qed.',
        'Goal True. idtac "CAPTURE_CHAIN_AUDIT". exact I. Qed.',
        'Print Assumptions captured_chain_input.',
        'Print Assumptions captured_chain_boundary.',
        'Print Assumptions captured_chain_phase.',
        'Print Assumptions capture_fields_history.',
        'Print Assumptions capture_fields_erases.']
    text='Module C.\n'+cs+'\nEnd C.\nModule B.\n'+bs+'\nEnd B.\nModule W.\n'+ws+'\nEnd W.\n'
    return text+'\n'.join(lines)+'\n',dict(**data,paths=paths)

def check(ast_path,ast_module,output,selected_roots=None):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    source,data=render(ast_path,ast_module,selected_roots)
    report=dict(accepted=False,old_inv_read=False,complete_R_generated=False,
        selected_roots=None if selected_roots is None else sorted(selected_roots),
        isa_admission_proved=False,validity_coverage_proved=False,
        connection=data['connection'])
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    if source is None:report['status']='no_capture_field_chain_connection'
    else:
        file=output/'CaptureChain.v';file.write_text(source)
        flags=list(chain.p.rtl.framework.FLAGS)
        for row in data['paths']:flags+=['-R',row['directory'],row['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedCaptureChain']
        start=time.monotonic();deadline=start+1200
        c,t=run_stage([str(birth.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],output/'coqc.log',1200)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest())
        if c.returncode==0 and time.monotonic()<deadline:
            marks=list(re.finditer(r'^CAPTURE_CHAIN_AUDIT\s*$',c.stdout,re.M))
            tail=c.stdout[marks[-1].end():]if marks else ''
            closed=len(marks)==1 and tail.count('Closed under the global context')==5 and 'Axioms:'not in tail
            k,t=run_stage([str(birth.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedCaptureChain.CaptureChain'],output/'coqchk.log',deadline-time.monotonic())
            report.update(export_assumptions_closed=closed,coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=closed and k.returncode==0)
        report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:parser.add_argument('--'+name,required=True)
    parser.add_argument('--roots',type=int,nargs='+')
    a=parser.parse_args();print(json.dumps(check(a.ast,a.ast_module,a.output,None if a.roots is None else set(a.roots)),indent=2))
