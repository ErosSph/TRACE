"""Generate PC/word companion rules from complete raw capture branches."""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_fetch_pairs as fetch
import cpu_capture_provenance as provenance
from cpu_certificate_acceptance import run_stage
rtl=fetch.rtl

def match(word,valid,pc,root,pcroot,pair):
    v=provenance.hb.coverage.capture.birth.validity
    if v.is_const(valid,1,0):return 'apply Invalid.'
    if v.is_var(word,32,root) and v.is_var(pc,32,pcroot):return 'apply Hold.'
    if v.is_var(word,32,pair['word_input']) and v.is_var(pc,32,pair['pc_input']):
        return ('apply Fresh;[intro H;discriminate|]. intros s [seed HL].\n'
                f'change(Some(norm 32(read_signal s {pair["address_root"]}))=Some(norm 32(norm 32(read_signal s {pair["pc_input"]})))).\nrewrite ExtendedSVWordInvariant.norm_idempotent.\n'
                'exact(f_equal (@Some Z)(eq_sym(F.fetch_pair_0_sampled_pc seed s HL))).')
    if (word.name==valid.name==pc.name=='ECond' and word.args[1]==valid.args[1]==pc.args[1]
        and word.args[0].name==pc.args[0].name=='32' and valid.args[0].name=='1'):
        yes=match(word.args[2],valid.args[2],pc.args[2],root,pcroot,pair)
        no=match(word.args[3],valid.args[3],pc.args[3],root,pcroot,pair)
        if yes and no:return 'apply Select.\n{ '+yes+' }\n{ '+no+' }'
    return None

def render(program,module,pair,proof):
    r=pair['carrier'];pc=pair['pc_root'];proc=pair['process'];ast=program.rsplit('.',1)[0]
    return f'''From Coq Require Import List ZArith Bool.
Require Import {module}.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVCaptureBirth
 Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVCapturedPC Lang.ExtendedSVRuntimeHistory Lang.ExtendedSVBoundedCatalogPhase
 Lang.ExtendedSVBootstrap GeneratedCapturedHistoryBoot.CapturedHistoryBoot GeneratedFetchPairs.FetchPairs.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVCaptureBirth ExtendedSVCapturedPC ExtendedSVBoundedCatalogPhase.
Module H:=GeneratedCapturedHistoryBoot.CapturedHistoryBoot. Module C:=H.C.
Module F:=GeneratedFetchPairs.FetchPairs.
Local Opaque {program} PhaseSemantics.
Definition Good s:=exists seed,CombLFP {program} seed s.
Lemma pc_self:self_widthb 32 {pc} F.root_{pc}_expression=true.
Proof. vm_compute;reflexivity. Qed.
Definition pc_scalar:ScalarCertificate {program} {pc} 32 {ast}.{proc} F.root_{pc}_expression:=
 Build_ScalarCertificate _ _ _ _ _ F.root_{pc}_comb_frame pc_self F.root_{pc}_expression_phase.
Lemma pc_matches:Matches {r} {pc} C.B.capture_0_pc Good C.B.root_{r}_expression C.B.root_{pair['valid_root']}_expression F.root_{pc}_expression.
Proof. unfold C.B.root_{r}_expression,C.B.root_{pair['valid_root']}_expression,F.root_{pc}_expression.
{proof}
Qed.
Lemma protect_pc ev:H.W.Environment ev ->changed_signal ev<>{pc}%nat.
Proof. intros [_ HE];unfold H.W.ExternalEvent in HE;apply existsb_exists in HE.
destruct HE as[root[HI HR]];apply Nat.eqb_eq in HR;rewrite HR.
unfold H.W.external_roots in HI;cbn in HI;repeat destruct HI as[<-|HI];try contradiction;discriminate. Qed.
Lemma phase_pc seed ev pre packed:H.W.Environment ev ->CombLFP {program} seed(phase_driven_state {program} ev pre) ->
 Related {pc} pre(fst packed) ->Related {pc}(PhaseSemantics {program} ev pre)(fst(C.advance_capture_fields ev pre packed tt)).
Proof. intros HE HL HR;cbn[C.advance_capture_fields fst];unfold C.B.capture_0_step.
exact(actual_phase {program} {r} {pc} {ast}.{proc} C.B.root_{r}_expression C.B.root_{pair['valid_root']}_expression
 F.root_{pc}_expression C.B.capture_0_pc Good pc_scalar pc_matches ev pre(fst packed)(protect_pc ev HE)(ex_intro _ seed HL)HR). Qed.
Theorem runtime_pc events:Forall H.W.Environment events ->forall pre packed,
 CatalogShape {program} Catalog.actual_catalog pre ->Related {pc} pre(fst packed) ->
 Related {pc}(phase_run {program} events pre)(fst(H.history events pre packed)).
Proof. exact(checked_history {program} Catalog.actual_catalog Phase.actual_certificate C.Packed C.advance_capture_fields
 (fun pre packed=>Related {pc} pre(fst packed))H.W.Environment(fun ev HE=>proj1 HE)phase_pc events). Qed.
Theorem boot_pc image events:Forall H.W.Environment events ->
 Related {pc}(phase_run {program} events(H.F.boot image))(fst(H.boot_history image events)).
Proof. intro HE.
assert(HA:Forall H.W.Environment(H.F.boot_events++events))by(apply Forall_app;split;[exact H.W.boot_environment|exact HE]).
pose proof(runtime_pc (H.F.boot_events++events)HA(H.F.seed image)H.empty(H.B.seed_shape image))as HR.
assert(HI:Related {pc}(H.F.seed image)(fst H.empty))by(intros token HT;discriminate).
specialize(HR HI);rewrite ExtendedSVRuntimeHistory.phase_run_append in HR;exact HR. Qed.
Print Assumptions pc_matches. Print Assumptions runtime_pc. Print Assumptions boot_pc.
'''

def check(ast,module,history_provider,pair_provider,output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False);hp=Path(history_provider);fp=Path(pair_provider)
    raw,profile,_=fetch.origin.raw_binding(ast,module);p=profile['ast']['program']
    pd,ps=fetch.render(ast,module);pr=json.loads((fp/'report.json').read_text())
    if not(pr.get('accepted')is True and pr.get('coqc_exit')==pr.get('coqchk_exit')==0 and pr.get('assumptions_closed')is True
           and (fp/'FetchPairs.v').read_text()==ps and pr['source_sha256']==hashlib.sha256(ps.encode()).hexdigest()):raise ValueError('fetch proof mismatch')
    plan=json.loads((hp/'plan.json').read_text());hr=json.loads((hp/'report.json').read_text())
    ns={b['namespace']:Path(b['directory'])for b in plan['paths']}
    env=json.loads((ns['GeneratedSeedBoot']/'plan.json').read_text())['environment']
    _,data=provenance.hb.boot.chain.render(ast,module)
    expected=provenance.hb.render(p,module,data,env)
    if not(hr.get('accepted')is True and hr.get('coqc_exit')==hr.get('coqchk_exit')==0 and hr.get('assumptions_closed')is True
           and plan['ast_sha256']==raw['source_sha256'] and (hp/'CapturedHistoryBoot.v').read_text()==expected):raise ValueError('history proof mismatch')
    birth=data['entry']['capture']
    captures=provenance.hb.coverage.capture.birth.discover(raw)['captures']
    if len(captures)!=1 or captures[0]['carrier']!=birth['carrier']:
        raise ValueError('single capture-provider instance required; do not guess capture index')
    if len(pd['pairs'])!=1 or pd['pairs'][0]['carrier']!=birth['carrier']:raise ValueError('unique matching PC companion required')
    pair=dict(pd['pairs'][0],valid_root=birth['valid_root'])
    if any(e['changed_signal']==pair['pc_root']for e in env['events'].values()):raise ValueError('external driver on captured PC')
    scalars={r['root']:r for r in fetch.origin.pending.analyze(raw)['scalar_transitions']}
    parse=lambda root:rtl.Parser(scalars[root]['next_expression']).complete()
    proof=match(parse(pair['carrier']),parse(pair['valid_root']),parse(pair['pc_root']),pair['carrier'],pair['pc_root'],pair)
    if proof is None:raise ValueError('PC and word branch updates do not match')
    source=render(p,module,pair,proof);file=out/'CapturedPC.v';file.write_text(source)
    flags=list(rtl.framework.FLAGS)
    for b in plan['paths']:flags+=['-R',b['directory'],b['namespace']]
    flags+=['-R',str(fp.resolve()),'GeneratedFetchPairs','-R',str(out.resolve()),'GeneratedCapturedPC']
    start=time.monotonic();c,t=run_stage([str(fetch.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    result=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,complete_R_generated=False,isa_pc_order_proved=False,old_inv_read=False,
                source_sha256=hashlib.sha256(source.encode()).hexdigest(),pair=pair)
    if c.returncode==0 and time.monotonic()-start<1200:
        closed=c.stdout.count('Closed under the global context')==3 and 'Axioms:'not in c.stdout
        k,t=run_stage([str(fetch.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedCapturedPC.CapturedPC'],out/'coqchk.log',1200-(time.monotonic()-start))
        result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,accepted=closed and k.returncode==0)
    result['seconds']=time.monotonic()-start;(out/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ['ast','ast-module','history-provider','pair-provider','output']:parser.add_argument('--'+key,required=True)
    a=parser.parse_args();r=check(a.ast,a.ast_module,a.history_provider,a.pair_provider,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
