"""Bind actual sampled RF addresses to the current endogenous instruction token.
No register value freshness or ISA retirement order is asserted.
"""
import argparse,json,hashlib,time
from pathlib import Path
import cpu_operand_address_origins as origins
import cpu_capture_provenance as provenance
import cpu_instruction_fields as fields
from cpu_certificate_acceptance import run_stage
rtl=origins.rtl

def strip_identity_extensions(e):
    if not e.args:return e
    args=tuple(strip_identity_extensions(a)for a in e.args)
    e=rtl.Term(e.name,args)
    if e.name=='EExtend'and args[1].name=='false'and args[2].name in ['EVar','ESel','EExtend']and args[0].name==args[2].args[0].name:
        return args[2]
    return e

def classify(rows,carrier):
    selected=[]
    for row in rows:
        layout=fields.match_field(strip_identity_extensions(rtl.Parser(row['expanded']).complete()),row['width'])
        if row['source']!=carrier or not layout or layout['source']!=carrier or layout['field']not in ['Rs1','Rs2']:
            raise ValueError('read address does not match captured source field')
        selected.append(dict(row,field=layout['field']))
    if not selected:raise ValueError('no matched read addresses')
    return selected

def match_read_ports(analysis,rows):
    if analysis['residuals']:raise ValueError('read ports have unresolved semantics')
    result=[]
    for index,port in enumerate(analysis['ports']):
        e=port['rhs'];candidates=[]
        banks={(int(n.args[0].name),int(n.args[1].name))for n in rtl.walk(e)if n.name=='EVar'and int(n.args[0].name)>=1024}
        for total,bank in banks:
            for row in rows:
                a=row['root']
                expected=rtl.Parser(f'(ECond 32 (EBinary 1 BEq (EConst 5 0) (EVar 5 {a})) (EConst 32 0) (ESel 32 (EVar {total} {bank}) (ESel 10 (EBinary 32 BShiftL (EExtend 32 false (EVar 5 {a})) (EConst 32 5)) (EConst 32 0))))').complete()
                if e==expected and port['width']==32:candidates.append(dict(port=index,output=port['output_root'],address=a,bank=bank,total=total,field=row['field']))
        if len(candidates)!=1:raise ValueError('read port lacks unique checked zero-guarded pattern')
        result+=candidates
    if not result:raise ValueError('no physical read ports')
    return result

def render_values(program,ports,valid):
    sample=f'(phase_driven_state {program} ev pre)'
    lines=['From Coq Require Import Lia.',
           'Require Import Lang.ExtendedSVZeroGuardedRead Lang.ExtendedSVRootProjection.',
           'Import ExtendedSVRootProjection.']
    for bank in sorted({r['bank']for r in ports}):
        lines += [f'Lemma bank_{bank}_frame:comb_root_unwrittenb {program} {bank}=true.',
          'Proof. vm_compute;reflexivity. Qed.',
          f'Lemma protect_bank_{bank} ev:H.W.Environment ev ->changed_signal ev<>{bank}%nat.',
          'Proof. intros[_ HE];unfold H.W.ExternalEvent in HE;apply existsb_exists in HE;',
          'destruct HE as[x[HX HE]];apply Nat.eqb_eq in HE;rewrite HE;unfold H.W.external_roots in HX;',
          'cbn in HX;repeat destruct HX as[<-|HX];try contradiction;discriminate. Qed.']
    for r in ports:
        p=r['port'];bank=r['bank'];a=r['address']
        lines += [f'Theorem read_port_{p}_current_token image events ev token:',
          f'let pre:=phase_run {program} events(H.F.boot image) in',
          'Forall H.W.Environment events ->H.W.Environment ev ->',
          'current(fst(H.boot_history image events))=Some token ->',
          f'norm 32(read_signal {sample} {r["output"]})=ExtendedSVZeroGuardedRead.value(read_signal pre {bank})(field_reference(token_word token){r["field"]}).',
          'Proof. intros pre HE HEv HT;destruct(sample_evidence image events ev HE HEv)as[seed HL].',
          f'pose proof(B.port_{p}_lfp seed _ HL)as HR; fold pre in HR; rewrite HR.',
          f'change(norm 32(eval_expr {sample}(ExtendedSVZeroGuardedRead.expression {r["total"]} {bank} {a}))=ExtendedSVZeroGuardedRead.value(read_signal pre {bank})(field_reference(token_word token){r["field"]})).',
          f'rewrite(ExtendedSVZeroGuardedRead.read_value {r["total"]} {bank} {a} _ ltac:(lia)).',
          f'rewrite(sampled_root_preserved {program} ev pre {bank} bank_{bank}_frame(protect_bank_{bank} ev HEv)).',
          f'pose proof(address_{a}_current_token image events ev token HE HEv HT)as HA;fold pre in HA;rewrite HA;reflexivity. Qed.']
    lines += ['Theorem valid_sampled_read_values image events ev:',
      f'let pre:=phase_run {program} events(H.F.boot image) in',
      'Forall H.W.Environment events ->H.W.Environment ev ->',
      f'norm 1(read_signal pre {valid})<>0%Z ->exists token,',
      'current(fst(H.boot_history image events))=Some token /\\',
      ' /\\ '.join(f'norm 32(read_signal {sample} {r["output"]})=ExtendedSVZeroGuardedRead.value(read_signal pre {r["bank"]})(field_reference(token_word token){r["field"]})'for r in ports)+'.',
      'Proof. intros pre HE HEv HV;',
      'destruct(valid_sampled_read_addresses image events ev HE HEv HV)as[token[HT HA]].',
      'exists token;split;[exact HT|].']
    for i,r in enumerate(ports):
        proof=f'exact(read_port_{r["port"]}_current_token image events ev token HE HEv HT)'
        lines += [f'split;[{proof}|].'if i<len(ports)-1 else proof+'. Qed.']
    lines += ['Goal True. idtac "READ_DATA_AUDIT". exact I. Qed.',
              'Print Assumptions valid_sampled_read_values.']
    for r in ports:lines += [f'Print Assumptions read_port_{r["port"]}_current_token.']
    return '\n'.join(lines)+'\n'

def render(program,module,rows,carrier,valid):
    sample=f'(phase_driven_state {program} ev pre)'
    lines=['From Coq Require Import List ZArith Bool.',f'Require Import {module}',
      ' Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory',
      ' Lang.ExtendedSVScalarExpression Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCoveredField',
      ' Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVBootstrap Lang.ExtendedSVBoundedCatalogPhase',
      ' Ex.External.CPUInstructionFields GeneratedCapturedHistoryBoot.CapturedHistoryBoot.',
      'Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVCaptureBirth CPUInstructionFields.',
      'Module H:=GeneratedCapturedHistoryBoot.CapturedHistoryBoot. Module C:=H.C.',
      f'Local Opaque {program} PhaseSemantics.',
      f'Lemma protect ev:H.W.Environment ev ->changed_signal ev<>{carrier}%nat.',
      'Proof. intros[_ HE];unfold H.W.ExternalEvent in HE;apply existsb_exists in HE;',
      'destruct HE as[x[HX HE]];apply Nat.eqb_eq in HE;rewrite HE;unfold H.W.external_roots in HX;',
      'cbn in HX;repeat destruct HX as[<-|HX];try contradiction;discriminate. Qed.',
      'Lemma sample_evidence image events ev:Forall H.W.Environment events ->H.W.Environment ev ->',
      f'exists seed,CombLFP {program} seed(phase_driven_state {program} ev(phase_run {program} events(H.F.boot image))).',
      'Proof. intros HE HEv.',
      f'assert(HA:Forall(ExtendedSVBoundedCatalogPhase.CatalogEvent {program} Catalog.actual_catalog)events).',
      '{ eapply Forall_impl;[|exact HE];intros event HH;exact(proj1 HH). }',
      f'pose proof(ExtendedSVEmptyPipeline.catalog_shape_history {program} Catalog.actual_catalog Phase.actual_certificate events HA(H.F.boot image)(proj1(H.B.boot_runtime image)))as HS.',
      f'destruct(ExtendedSVBootstrap.catalog_phase_evidence {program} Catalog.actual_catalog Phase.actual_certificate ev _ (proj1 HEv)HS)as[HL _];eexists;exact HL. Qed.',
      'Theorem sampled_current_word image events ev token:',
      f'let pre:=phase_run {program} events(H.F.boot image) in',
      'Forall H.W.Environment events ->H.W.Environment ev ->',
      'current(fst(H.boot_history image events))=Some token ->',
      f'norm 32(read_signal {sample} {carrier})=norm 32(token_word token).',
      'Proof. intros pre HE HEv HT;',
      'destruct(H.boot_and_runtime_related image events HE)as[[[HI HC]HV]HW].',
      'destruct HI as[[Hcover Hvalue]Hrest].',
      f'rewrite(sampled_root_preserved {program} ev pre {carrier} C.B.root_{carrier}_comb_frame(protect ev HEv)).',
      'exact(Hvalue token HT). Qed.']
    for row in rows:
        r=row['root'];w=row['width'];field=row['field'];expr=row['expanded']
        lines += [f'Lemma address_{r}_field code:A.address_{r}_reference code=field_reference code {field}.',
          f'Proof. let e:=eval cbv in A.address_{r}_expanded in',
          f'change(norm {w}(eval_expr(write_signal [] {carrier} code)e)=field_reference code {field}).',
          f'pose proof(native_field_reference(write_signal [] {carrier} code){carrier} {field})as HF.',
          'unfold field_expr in HF;cbn[field_width field_offset eval_expr]in HF;',
          'cbn[eval_expr];rewrite !norm_idempotent in *;exact HF. Qed.',
          f'Theorem address_{r}_current_token image events ev token:',
          f'let pre:=phase_run {program} events(H.F.boot image) in',
          'Forall H.W.Environment events ->H.W.Environment ev ->',
          'current(fst(H.boot_history image events))=Some token ->',
          f'norm {w}(read_signal {sample} {r})=field_reference(token_word token){field}.',
          'Proof. intros pre HE HEv HT;destruct(sample_evidence image events ev HE HEv)as[seed HL].',
          f'exact(eq_trans(A.address_{r}_instruction seed _ (token_word token)HL(sampled_current_word image events ev token HE HEv HT))(address_{r}_field(token_word token))). Qed.']
    lines+=['Theorem valid_sampled_read_addresses image events ev:',
      f'let pre:=phase_run {program} events(H.F.boot image) in',
      'Forall H.W.Environment events ->H.W.Environment ev ->',
      f'norm 1(read_signal pre {valid})<>0%Z ->exists token,',
      'current(fst(H.boot_history image events))=Some token /\\',
      ' /\\ '.join(f'norm {r["width"]}(read_signal {sample} {r["root"]})=field_reference(token_word token){r["field"]}'for r in rows)+'.',
      'Proof. intros pre HE HEv HV;destruct(H.boot_and_runtime_related image events HE)as[[[HI HC]Hcover]HW].',
      'destruct HI as[[Hvalid Hvalue]Hrest];destruct(Hvalid HV)as[token HT].',
      'exists token;split;[exact HT|].']
    for i,r in enumerate(rows):
        proof=f'exact(address_{r["root"]}_current_token image events ev token HE HEv HT)'
        lines += [f'split;[{proof}|].'if i<len(rows)-1 else proof+'. Qed.']
    lines+=['Goal True. idtac "READ_TOKEN_AUDIT". exact I. Qed.',
      'Print Assumptions sampled_current_word. Print Assumptions valid_sampled_read_addresses.']
    for r in rows:lines += [f'Print Assumptions address_{r["root"]}_field. Print Assumptions address_{r["root"]}_current_token.']
    return '\n'.join(lines)+'\n'

def check(ast,module,history_provider,output,with_values=False):
    out=Path(output);out.mkdir(parents=True,exist_ok=False);hp=Path(history_provider)
    raw,profile,_=origins.origin.raw_binding(ast,module);program=profile['ast']['program']
    plan=json.loads((hp/'plan.json').read_text());hr=json.loads((hp/'report.json').read_text())
    ns={r['namespace']:Path(r['directory'])for r in plan['paths']}
    env=json.loads((ns['GeneratedSeedBoot']/'plan.json').read_text())['environment']
    _,validity=provenance.hb.boot.chain.render(ast,module)
    expected=provenance.hb.render(program,module,validity,env)
    if not(hr.get('accepted')is True and hr.get('coqc_exit')==hr.get('coqchk_exit')==0 and hr.get('assumptions_closed')is True
        and plan['ast_sha256']==raw['source_sha256'] and(hp/'CapturedHistoryBoot.v').read_text()==expected):raise ValueError('history provider mismatch')
    for file,sha in env['input_hashes'].items():
        if provenance.hb.boot.digest(file)!=sha:raise ValueError('environment changed')
    data,source,_,_=origins.render(ast,module)
    if source is None or data['residuals']:raise ValueError('read-address analysis incomplete')
    birth=validity['entry']['capture'];rows=classify(data['origins'],birth['carrier'])
    prefix='';read_ports=[]
    if with_values:
        analysis=origins.readers.analyze(raw);read_ports=match_read_ports(analysis,rows)
        prefix='Module B.\n'+origins.readers.render(profile['ast'],raw,analysis)+'\nEnd B.\n'
    source=prefix+'Module A.\n'+source+'\nEnd A.\n'+render(program,module,rows,birth['carrier'],birth['valid_root'])
    if with_values:source+=render_values(program,read_ports,birth['valid_root'])
    file=out/'CapturedReadAddresses.v';file.write_text(source)
    flags=list(rtl.framework.FLAGS)
    for row in plan['paths']:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedCapturedReads']
    start=time.monotonic();c,t=run_stage([str(origins.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    result=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,rows=rows,operand_freshness_proved=False,
      complete_R_generated=False,old_inv_read=False,source_sha256=hashlib.sha256(source.encode()).hexdigest())
    if c.returncode==0 and time.monotonic()-start<1200:
        tail=c.stdout.split('READ_TOKEN_AUDIT\n')[-1]
        closed=tail.count('Closed under the global context')==2+2*len(rows)+len(read_ports)+int(with_values)and 'Axioms:'not in tail
        k,t=run_stage([str(origins.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedCapturedReads.CapturedReadAddresses'],out/'coqchk.log',1200-(time.monotonic()-start))
        result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,accepted=closed and k.returncode==0)
    result['physical_read_ports_connected']=read_ports if result['accepted']else[]
    result['seconds']=time.monotonic()-start;(out/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for k in ['ast','ast-module','history-provider','output']:parser.add_argument('--'+k,required=True)
    parser.add_argument('--with-values',action='store_true')
    a=parser.parse_args();r=check(a.ast,a.ast_module,a.history_provider,a.output,a.with_values);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
