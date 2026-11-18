"""Derive selector destination ownership from actual boot history.
Effective write guards imply a valid stage; no caller-supplied CPU INV.
This does not establish newest-writer priority or result correctness.
"""
import argparse,json,hashlib,time
from pathlib import Path
import cpu_captured_read_addresses as reads
import cpu_selector_sources as sources
from cpu_certificate_acceptance import run_stage

def discover(plan,stages):
    unique={(r['width'],r['input']):r for r in plan['sources']if r['edges']}
    indices={key:i for i,key in enumerate(unique)}
    found={}
    for row in plan['sources']:
        matches=[(i,s)for i,s in enumerate(stages)if row['width']==5 and row['terminal']==s['rd']]
        if len(matches)!=1 or (5,row['input'])not in indices:continue
        i,s=matches[0]
        enables={r['input']:r for r in plan['sources']if r['selector']==row['selector']and r['width']==1 and r['terminal']==s['write']and r['edges']}
        if len(enables)!=1:continue
        e=next(iter(enables.values()))
        key=(row['input'],e['input'])
        found[key]=dict(stage=i,rd=row['input'],write=e['input'],rd_proof=indices[(5,row['input'])],
            write_proof=indices[(1,e['input'])],physical=s)
    return list(found.values())

def render(ast,module,stages):
    plan,source,_,_=sources.render(ast,module)
    rows=discover(plan,stages)
    if not rows:raise ValueError('no selector destination/enable pair matches a generated stage')
    _,profile,_=reads.origins.origin.raw_binding(ast,module);p=profile['ast']['program']
    text='Module W.\n'+source+'\nEnd W.\n'+f'''From Coq Require Import List ZArith Bool.
Require Import {module} Lang.ExtendedSV Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVWordInvariant Lang.ExtendedSVRootProjection Lang.ExtendedSVCaptureBirth
 Lang.ExtendedSVWriteValidity Lang.ExtendedSVScalarExpression.
Require GeneratedCapturedReads.CapturedReadAddresses.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVWordInvariant
 ExtendedSVRootProjection ExtendedSVCaptureBirth ExtendedSVWriteValidity ExtendedSVScalarExpression.
Module R:=GeneratedCapturedReads.CapturedReadAddresses.
Module H:=R.H.
Local Opaque {p} PhaseSemantics.
'''
    sample=f'(phase_driven_state {p} ev pre)'
    for root in sorted({s[k]for r in rows for s in [r['physical']]for k in ['rd','write']}):
        text+=f'''Lemma frame_{root}:comb_root_unwrittenb {p} {root}=true.
Proof. vm_compute;reflexivity. Qed.
Lemma protect_{root} ev:H.W.Environment ev ->changed_signal ev<>{root}%nat.
Proof. intros[_ HE];unfold H.W.ExternalEvent in HE;apply existsb_exists in HE;
destruct HE as[x[HX HE]];apply Nat.eqb_eq in HE;rewrite HE;unfold H.W.external_roots in HX;
cbn in HX;repeat destruct HX as[<-|HX];try contradiction;discriminate. Qed.
'''
    for n,r in enumerate(rows):
        i=r['stage'];s=r['physical'];eligible='(proj2 HW)'
        for _ in range(i):eligible=f'(proj2 {eligible})'
        if i<len(stages)-1:eligible=f'(proj1 {eligible})'
        text+=f'''Theorem selector_{n}_enabled_token image events ev:
 let pre:=phase_run {p} events(H.F.boot image)in
 Forall H.W.Environment events ->H.W.Environment ev ->
 norm 1(read_signal {sample} {r['write']})<>0%Z ->
 norm 5(read_signal {sample} {r['rd']})<>0%Z ->
 exists token,H.C.C.chain_tag{i}(snd(H.boot_history image events))=Some token /\\
 norm 5(read_signal {sample} {r['rd']})=norm 5(H.C.C.chain_head_value(token_word token)).
Proof. intros pre HE HEv HWinput HDinput.
destruct(R.sample_evidence image events ev HE HEv)as[seed HL].
pose proof(W.selector_source_{r['rd_proof']} seed _ HL)as HD;fold pre in HD.
pose proof(W.selector_source_{r['write_proof']} seed _ HL)as HEwrite;fold pre in HEwrite.
rewrite(sampled_root_preserved {p} ev pre {s['rd']} frame_{s['rd']}(protect_{s['rd']} ev HEv))in HD.
rewrite(sampled_root_preserved {p} ev pre {s['write']} frame_{s['write']}(protect_{s['write']} ev HEv))in HEwrite.
rewrite HD in HDinput;rewrite HEwrite in HWinput.
destruct(H.boot_and_runtime_related image events HE)as[HC HW].
assert(HV:norm 1(read_signal pre {s['valid']})<>0%Z).
{{ exact({eligible} HWinput HDinput). }}
destruct(H.C.valid_field_{i}_has_value pre _ HC HV)as[token[HT HX]].
exists token;split;[exact HT|exact(eq_trans HD HX)]. Qed.
'''
    text+='Goal True. idtac "SELECTOR_BOOT_AUDIT". exact I. Qed.\n'
    text+=''.join(f'Print Assumptions selector_{i}_enabled_token.\n'for i in range(len(rows)))
    return text,rows

def check(ast,module,history,out):
    out=Path(out);out.mkdir(parents=True,exist_ok=False);provider=out/'reads'
    rr=reads.check(ast,module,history,provider)
    report=dict(accepted=False,reads=rr,old_inv_read=False,complete_R_generated=False,operand_freshness_proved=False)
    def save():
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    if not rr['accepted']:return save()
    _,validity=reads.provenance.hb.boot.chain.render(ast,module)
    source,rows=render(ast,module,validity['rows'])
    (out/'plan.json').write_text(json.dumps(rows,indent=2)+'\n')
    path=out/'SelectorBootTokens.v';path.write_text(source)
    flags=list(reads.rtl.framework.FLAGS)
    for r in json.loads((Path(history)/'plan.json').read_text())['paths']:flags+=['-R',r['directory'],r['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedSelectorBoot','-R',str(provider.resolve()),'GeneratedCapturedReads']
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(reads.origins.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],out/'coqc.log',1200)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),connections=len(rows))
    if c.returncode==0:
        tail=c.stdout.split('SELECTOR_BOOT_AUDIT\n')[-1]
        report['assumptions_closed']=tail.count('Closed under the global context')==len(rows)and 'Axioms:'not in tail
        k,t=run_stage([str(reads.origins.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedSelectorBoot.SelectorBootTokens'],out/'coqchk.log',max(.1,deadline-time.monotonic()))
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0 and report['assumptions_closed'])
    report['seconds']=time.monotonic()-start
    return save()

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for k in ['ast','ast-module','history-provider','output']:p.add_argument('--'+k,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.history_provider,a.output);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
