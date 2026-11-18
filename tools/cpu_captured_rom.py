"""Prove captured records read the original packed RTL ROM at their recorded PC.

This is not byte-memory ISA correspondence or program/retirement order.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_captured_pc as pc
from cpu_certificate_acceptance import run_stage
rtl=pc.rtl

def abstract_read(expr,bank,address):
    if expr.name=='EVar':
        width,root=expr.args
        if int(root.name)==bank:return f'(EConst {width.name} image)'
        if int(root.name)==address and width.name=='32':return '(EConst 32 address)'
        raise ValueError('ROM expression has an unsupported external dependency')
    if not expr.args:return expr.name
    return '('+expr.name+' '+' '.join(abstract_read(a,bank,address)for a in expr.args)+')'

def content_proof(word,valid,root,source,depth=0):
    if valid.name=='EConst'and [x.name for x in valid.args]==['1','0']:return 'apply Invalid.'
    if word.name=='EVar'and word.args[0].name=='32':
        if int(word.args[1].name)==root:return 'apply Hold.'
        if int(word.args[1].name)!=source:raise ValueError('unmatched capture source')
        unpack=''.join('destruct HG as[HG HB'+str(i)+']. 'for i in range(depth))
        return ('apply Fresh;[discriminate|]. intros s serial HG HV. '+unpack+
          'destruct HG as[[seed HL] HR]. unfold Content,fresh;cbn[token_pc token_word].\n'
          'eexists;split;[reflexivity|]. exact(eq_trans(F.fetch_pair_0_sampled_word seed s HL)(sampled_lookup s image HR)).')
    if word.name==valid.name=='ECond'and word.args[0].name=='32'and valid.args[0].name=='1'and word.args[1]==valid.args[1]:
        return 'apply Select.\n{ '+content_proof(word.args[2],valid.args[2],root,source,depth+1)+' }\n{ '+content_proof(word.args[3],valid.args[3],root,source,depth+1)+' }'
    raise ValueError('unsupported capture expression')

def render(program,module,pair,port,lookup,proof):
    bank=pair['reader']['bank_root'];root=pair['carrier'];v=pair['valid_root'];proc=program.rsplit('.',1)[0]+'.'+pair['process']
    return f'''From Coq Require Import List ZArith Bool.
Require Import {module} Lang.ExtendedSV Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCaptureContent Lang.ExtendedSVCapturedPC
 Lang.ExtendedSVRuntimeHistory Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVScalarExpression Lang.ExtendedSVScalarHistory
 GeneratedCapturedHistoryBoot.CapturedHistoryBoot GeneratedFetchPairs.FetchPairs.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVCaptureBirth
 ExtendedSVBoundedCatalogPhase ExtendedSVScalarExpression ExtendedSVScalarHistory ExtendedSVCaptureContent.
Module H:=GeneratedCapturedHistoryBoot.CapturedHistoryBoot. Module C:=H.C.
Module F:=GeneratedFetchPairs.FetchPairs.
Local Opaque {program} PhaseSemantics.
Definition lookup(image address:Z):Z:=norm 32(eval_expr [] {lookup}).
Definition Content image token:=exists address,token_pc token=Some address /\\token_word token=lookup image address.
Lemma sampled_lookup s image:read_signal s {bank}=image ->
 norm 32(eval_expr s F.port_{port}_rhs)=lookup image(norm 32(read_signal s {pair['address_root']})).
Proof. intro HR;unfold lookup,F.port_{port}_rhs;cbn[eval_expr];rewrite HR;repeat rewrite norm_idempotent;reflexivity. Qed.
Definition Good image s:=(exists seed,CombLFP {program} seed s)/\\read_signal s {bank}=image.
Lemma matches image:Matches {root} C.B.capture_0_pc(Good image)(Content image)C.B.root_{root}_expression C.B.root_{v}_expression.
Proof. unfold C.B.root_{root}_expression,C.B.root_{v}_expression.
{proof}
Qed.
Lemma protect ev:H.W.Environment ev ->changed_signal ev<>{bank}%nat.
Proof. intros[_ HE];unfold H.W.ExternalEvent in HE;apply existsb_exists in HE.
destruct HE as[x[HX HE]];apply Nat.eqb_eq in HE;rewrite HE;unfold H.W.external_roots in HX;
cbn in HX;repeat destruct HX as[<-|HX];try contradiction;discriminate. Qed.
Definition Joint image pre(packed:C.Packed):=read_signal pre {bank}=image /\\Related(Content image)(fst packed).
Theorem phase_content image seed ev pre packed:H.W.Environment ev ->
 CombLFP {program} seed(phase_driven_state {program} ev pre) ->Joint image pre packed ->
 Joint image(PhaseSemantics {program} ev pre)(C.advance_capture_fields ev pre packed tt).
Proof. intros HE HL[HR HC];split.
 - rewrite(R.rom_0_actual_phase ev pre(protect ev HE));exact HR.
 - cbn[C.advance_capture_fields fst];unfold C.B.capture_0_step.
   apply(actual_phase {program} {proc} {root} C.B.root_{root}_expression C.B.root_{v}_expression C.B.capture_0_pc(Good image)(Content image)(matches image));[|exact HC].
   split;[exists seed;exact HL|].
   rewrite(sampled_root_preserved {program} ev pre {bank} R.rom_0_comb_frame(protect ev HE));exact HR. Qed.
Theorem runtime_content image events:Forall H.W.Environment events ->forall pre packed,
 CatalogShape {program} Catalog.actual_catalog pre ->Joint image pre packed ->
 Joint image(phase_run {program} events pre)(H.history events pre packed).
Proof. exact(ExtendedSVCapturedPC.checked_history {program} Catalog.actual_catalog Phase.actual_certificate C.Packed C.advance_capture_fields
 (Joint image)H.W.Environment(fun ev HE=>proj1 HE)(phase_content image)events). Qed.
Theorem boot_content image events:Forall H.W.Environment events ->
 Joint image(phase_run {program} events(H.F.boot image))(H.boot_history image events).
Proof. intro HE.
assert(HA:Forall H.W.Environment(H.F.boot_events++events))by(apply Forall_app;split;[exact H.W.boot_environment|exact HE]).
assert(HI:Joint image(H.F.seed image)H.empty).
{{ split;[unfold H.F.seed,H.F.writes,H.F.seed_count;vm_compute;reflexivity|apply empty_related]. }}
pose proof(runtime_content image _ HA(H.F.seed image)H.empty(H.B.seed_shape image)HI)as HR.
rewrite ExtendedSVRuntimeHistory.phase_run_append in HR;exact HR. Qed.
Theorem boot_recorded_content image events token:Forall H.W.Environment events ->
 In token(history(fst(H.boot_history image events))) ->Content image token.
Proof. intro HE;exact(recorded_content(Content image)(fst(H.boot_history image events))token(proj2(boot_content image events HE))). Qed.
Goal True. idtac "CAPTURE_ROM_AUDIT". exact I. Qed.
Print Assumptions matches. Print Assumptions phase_content. Print Assumptions runtime_content. Print Assumptions boot_content. Print Assumptions boot_recorded_content.
'''

def render_pipeline(chain):
    n=len(chain['rows'])
    if n==0:raise ValueError('empty captured pipeline')
    lines=['Lemma content_at_pc image token address:Content image token ->token_pc token=Some address ->',
           'token_word token=lookup image address.',
           'Proof. intros[a[HP HW]] HE;rewrite HP in HE;inversion HE;subst a;exact HW. Qed.']
    for i,row in enumerate(chain['rows']):
        # RecordedFields is current-tag /\ stage0 /\ ... /\ stageN.
        term='HR'
        for _ in range(i+1):term=f'(proj2 {term})'
        if i<n-1:term=f'(proj1 {term})'
        lines += [f'Theorem pipeline_field_{i}_content image events token:',
            'Forall H.W.Environment events ->',
            f'C.C.chain_tag{i}(snd(H.boot_history image events))=Some token ->Content image token.',
            f'Proof. intros HE HT;pose proof(G.boot_recorded image events)as HR;unfold G.RecordedFields in HR.',
            f'exact(boot_recorded_content image events token HE({term} token HT)). Qed.']
    lines += ['Goal True. idtac "PIPELINE_CONTENT_AUDIT". exact I. Qed.',
              'Print Assumptions content_at_pc.']
    lines += [f'Print Assumptions pipeline_field_{i}_content.'for i in range(n)]
    return '\n'.join(lines)+'\n'

def check(ast,module,history_provider,pair_provider,output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    raw,profile,_=pc.fetch.origin.raw_binding(ast,module);p=profile['ast']['program']
    hp=Path(history_provider);fp=Path(pair_provider)
    plan=json.loads((hp/'plan.json').read_text());hr=json.loads((hp/'report.json').read_text())
    ns={r['namespace']:Path(r['directory'])for r in plan['paths']}
    env=json.loads((ns['GeneratedSeedBoot']/'plan.json').read_text())['environment']
    _,validity=pc.provenance.hb.boot.chain.render(ast,module)
    expected=pc.provenance.hb.render(p,module,validity,env)
    if not(hr.get('accepted')is True and hr.get('assumptions_closed')is True and hr.get('coqc_exit')==hr.get('coqchk_exit')==0 and plan['ast_sha256']==raw['source_sha256'] and(hp/'CapturedHistoryBoot.v').read_text()==expected):raise ValueError('history provider mismatch')
    for file,sha in env['input_hashes'].items():
        if pc.provenance.hb.boot.digest(file)!=sha:raise ValueError('environment data changed')
    pd,ps=pc.fetch.render(ast,module);pr=json.loads((fp/'report.json').read_text())
    if not(pr.get('accepted')is True and pr.get('assumptions_closed')is True and pr.get('coqc_exit')==pr.get('coqchk_exit')==0 and(fp/'FetchPairs.v').read_text()==ps):raise ValueError('fetch provider mismatch')
    if len(pd['pairs'])!=1:raise ValueError('unique capture pair required')
    pair=dict(pd['pairs'][0],valid_root=validity['entry']['capture']['valid_root'])
    if pair['carrier']!=validity['entry']['capture']['carrier']:raise ValueError('capture mismatch')
    rd,rs=pc.fetch.rom.render(ast,module)
    if len(rd['candidates'])!=1 or rd['candidates'][0]!=pair['reader']:raise ValueError('unique readonly source required')
    # Identify the port by its original expression, not by a generated index.
    import re
    expr=f'(ESel 32 (EVar {pair["reader"]["bank_width"]} {pair["reader"]["bank_root"]}) {pair["reader"]["offset"]})'
    ports=[int(i)for i,e in re.findall(r'Definition port_(\d+)_rhs : Expr := (.*)\.',ps)if e==expr]
    if len(ports)!=1:raise ValueError('unique actual ROM expression required')
    lookup=abstract_read(rtl.Parser(expr).complete(),pair['reader']['bank_root'],pair['address_root'])
    scalars={r['root']:r for r in pc.fetch.origin.pending.analyze(raw)['scalar_transitions']}
    parse=lambda r:rtl.Parser(scalars[r]['next_expression']).complete()
    proof=content_proof(parse(pair['carrier']),parse(pair['valid_root']),pair['carrier'],pair['word_input'])
    chain=pc.provenance.hb.coverage.capture.discover(raw,{r['rd']for r in validity['rows']})['chain']
    provenance=pc.provenance.render(p,chain,module)
    source='Module R.\n'+rs+'\nEnd R.\nModule G.\n'+provenance+'\nEnd G.\n'+render(p,module,pair,ports[0],lookup,proof)+render_pipeline(chain)
    file=out/'CapturedROM.v';file.write_text(source)
    (out/'plan.json').write_text(json.dumps(dict(ast_sha256=raw['source_sha256'],program=p,
        paths=plan['paths'],pair_provider=str(fp.resolve()),pair=pair,lookup_expression=lookup,chain=chain),indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for r in plan['paths']:flags+=['-R',r['directory'],r['namespace']]
    flags+=['-R',str(fp.resolve()),'GeneratedFetchPairs','-R',str(out.resolve()),'GeneratedCapturedROM']
    start=time.monotonic();c,t=run_stage([str(pc.fetch.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    result=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,complete_R_generated=False,isa_rom_correspondence_proved=False,old_inv_read=False,source_sha256=hashlib.sha256(source.encode()).hexdigest(),pair=pair)
    if c.returncode==0 and time.monotonic()-start<1200:
        tail=c.stdout.split('CAPTURE_ROM_AUDIT\n')[-1]
        closed=tail.count('Closed under the global context')==6+len(chain['rows']) and 'Axioms:'not in tail
        k,t=run_stage([str(pc.fetch.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedCapturedROM.CapturedROM'],out/'coqchk.log',1200-(time.monotonic()-start))
        result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,accepted=closed and k.returncode==0)
    result['pipeline_fields_connected']=len(chain['rows'])if result['accepted']else 0
    result['seconds']=time.monotonic()-start;(out/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ['ast','ast-module','history-provider','pair-provider','output']:parser.add_argument('--'+key,required=True)
    a=parser.parse_args();r=check(a.ast,a.ast_module,a.history_provider,a.pair_provider,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
