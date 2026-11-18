"""Discover PC companions of existing token stages; prove with shared recipes."""
import argparse,json,hashlib,re,time
from pathlib import Path
import cpu_captured_pc as pc
from cpu_certificate_acceptance import run_stage
rtl=pc.rtl

class RecipeParser(rtl.Parser):
    def parse(self):
        if self.pos<len(self.tokens) and self.tokens[self.pos]in ['Hold','Capture','Unknown','Select']:
            name=self.take()
            return rtl.Term(name,tuple(self.parse()for _ in range(3 if name=='Select'else 0)))
        return super().parse()

def match_recipe(expr,recipe,root):
    """Return capture sources plus proof, or reject an unsupported shape."""
    if recipe.name=='Unknown':return set(),'apply MatchesUnknown.'
    if recipe.name=='Hold':
        return (set(),'apply MatchesHold.') if expr.name=='EVar' and [a.name for a in expr.args]==['32',str(root)] else None
    if recipe.name=='Capture':
        return ({int(expr.args[1].name)},'apply MatchesCapture.') if expr.name=='EVar' and expr.args[0].name=='32' else None
    if recipe.name=='Select' and expr.name=='ECond' and expr.args[0].name=='32' and expr.args[1]==recipe.args[0]:
        a=match_recipe(expr.args[2],recipe.args[1],root);b=match_recipe(expr.args[3],recipe.args[2],root)
        if a and b:return a[0]|b[0],'apply MatchesSelect.\n{ '+a[1]+' }\n{ '+b[1]+' }'
    return None

def discover(ast,chain,captured_pc):
    scalars=pc.fetch.origin.pending.analyze(ast)['scalar_transitions']
    edges={e['target']:e['source']for e in chain['edges']};found={};pending=set(range(len(chain['rows'])))
    while pending:
        progress=False
        for i in sorted(pending):
            if i in edges and edges[i]not in found:continue
            row=chain['rows'][i];parent=found[edges[i]]['root']if i in edges else captured_pc
            matches=[]
            for s in scalars:
                if s['process']!=row['process']or s['width']!=32:continue
                m=match_recipe(rtl.Parser(s['next_expression']).complete(),RecipeParser(row['recipe']).complete(),s['root'])
                if m is None or len(m[0])!=1:continue
                source=next(iter(m[0]));route=pc.fetch.rom.aliases.trace(ast,source)
                if route['terminal']==parent:matches.append(dict(index=i,root=s['root'],source=source,parent=parent,
                    process=s['process'],recipe=row['recipe'],proof=m[1],route=route))
            if len(matches)!=1:raise ValueError(f'PC companion stage {i}: expected unique structural match, got {len(matches)}')
            found[i]=matches[0];pending.remove(i);progress=True
        if not progress:raise ValueError('cyclic or unresolved token chain')
    return [found[i]for i in range(len(chain['rows']))]

def render(program,module,rows,chain,captured_pc,ports):
    n=len(rows);edges={e['target']:e['source']for e in chain['edges']};ast=program.rsplit('.',1)[0]
    sample=f'(phase_driven_state {program} ev pre)'
    lines=['From Coq Require Import List ZArith Bool.',f'Require Import {module}.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarExpression',
        ' Lang.ExtendedSVProjectionOrigin Lang.ExtendedSVCompanionField Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPC',
        ' Lang.ExtendedSVRuntimeHistory Lang.ExtendedSVBoundedCatalogPhase GeneratedCapturedPC.CapturedPC.',
        'Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVWordInvariant ExtendedSVScalarExpression ExtendedSVProjectionOrigin ExtendedSVCaptureBirth ExtendedSVBoundedCatalogPhase.',
        'Module P:=GeneratedCapturedPC.CapturedPC. Module H:=P.H. Module C:=H.C.',
        f'Local Opaque {program} PhaseSemantics.']
    for r in rows:
        root=r['root'];i=r['index']
        lines += [f'Lemma self_{root}:self_widthb 32 {root} S.root_{root}_expression=true.',
            'Proof. vm_compute;reflexivity. Qed.',
            f'Definition scalar_{root}:ScalarCertificate {program} {root} 32 {ast}.{r["process"]} S.root_{root}_expression:=',
            f' Build_ScalarCertificate _ _ _ _ _ S.root_{root}_comb_frame self_{root} S.root_{root}_expression_phase.',
            f'Lemma matches_{i}:RecipeMatches 32 {root}(EVar 32 {r["source"]})S.root_{root}_expression C.C.projection_{i}_recipe.',
            f'Proof. unfold S.root_{root}_expression,C.C.projection_{i}_recipe. {r["proof"]} Qed.']
    lines += ['Definition Fields pre(tags:@C.C.ChainTags Token):Prop:=',
        ' /\\ '.join(f'ExtendedSVCompanionField.Related token_pc {r["root"]} pre(C.C.chain_tag{i} tags)'for i,r in enumerate(rows))+'.',
        f'Definition Joint pre(packed:C.Packed):=ExtendedSVCapturedPC.Related {captured_pc} pre(fst packed) /\\Fields pre(snd packed).',
        'Lemma protect ev root:H.W.Environment ev ->In root ['+';'.join(str(x)+'%nat'for x in [captured_pc]+[r['root']for r in rows])+'] ->changed_signal ev<>root.',
        'Proof. intros [_ HE] HI;unfold H.W.ExternalEvent in HE;apply existsb_exists in HE.',
        'destruct HE as[x[HX HE]];apply Nat.eqb_eq in HE;rewrite HE.',
        'unfold H.W.external_roots in HX;cbn in HX,HI;repeat destruct HX as[<-|HX];try contradiction;',
        'repeat destruct HI as[<-|HI];try contradiction;discriminate. Qed.',
        f'Theorem joint_phase seed ev pre packed:H.W.Environment ev ->CombLFP {program} seed {sample} ->Joint pre packed ->',
        f'Joint(PhaseSemantics {program} ev pre)(C.advance_capture_fields ev pre packed tt).',
        'Proof. destruct packed as[g tags];intros HE HL [HG HF];unfold Fields in HF;cbn[fst snd]in HG,HF.',
        ('rename HF into HO0.'if n==1 else 'destruct HF as['+''.join(f'HO{i} ['for i in range(n-2))+f'HO{n-2} HO{n-1}'+']'*(n-1)+'.')]
    for r in rows:
        i=r['index'];j=edges.get(i);incoming=f'(C.C.chain_tag{j} tags)'if j is not None else '(current g)'
        origin=f'HO{j}'if j is not None else 'HG';parent=r['parent']
        certificate=f'scalar_{parent}'if j is not None else 'P.pc_scalar'
        lines += [f'assert(HI{i}:ExtendedSVCompanionField.Related token_pc {r["source"]} {sample} {incoming}).',
            '{ intros token HT.']
        for e in r['route']['edges']:
            k=ports[e['root']];lines += [f'rewrite(W.port_{k}_lfp seed _ HL);unfold W.port_{k}_rhs;cbn[eval_expr];rewrite norm_idempotent.']
        lines += [f'rewrite(sampled_root_preserved {program} ev pre {parent}(history_comb_frame _ _ _ _ _ {certificate})(protect ev {parent} HE ltac:(simpl;tauto))).',
            f'exact({origin} token HT). }}',
            f'pose proof(ExtendedSVCompanionField.actual_phase token_pc {program} {r["root"]} {r["source"]} {ast}.{r["process"]}',
            f' S.root_{r["root"]}_expression C.C.projection_{i}_recipe scalar_{r["root"]} matches_{i} ev pre(C.C.chain_tag{i} tags){incoming}',
            f' (protect ev {r["root"]} HE ltac:(simpl;tauto)) HO{i} HI{i})as HP{i}.']
    lines += ['split;[exact(P.phase_pc seed ev pre(g,tags)HE HL HG)|].',
        'unfold Fields;cbn[C.advance_capture_fields fst snd C.C.advance_tags '+ ' '.join(f'C.C.chain_tag{i}'for i in range(n))+'].']
    for i in range(n-1):lines+= [f'split;[exact HP{i}|].']
    lines += [f'exact HP{n-1}. Qed.',
        f'Theorem runtime_joint events:Forall H.W.Environment events ->forall pre packed,CatalogShape {program} Catalog.actual_catalog pre ->Joint pre packed ->',
        f'Joint(phase_run {program} events pre)(H.history events pre packed).',
        f'Proof. exact(ExtendedSVCapturedPC.checked_history {program} Catalog.actual_catalog Phase.actual_certificate C.Packed C.advance_capture_fields Joint H.W.Environment(fun ev HE=>proj1 HE)joint_phase events). Qed.',
        f'Theorem boot_joint image events:Forall H.W.Environment events ->Joint(phase_run {program} events(H.F.boot image))(H.boot_history image events).',
        'Proof. intro HE;assert(HA:Forall H.W.Environment(H.F.boot_events++events))by(apply Forall_app;split;[exact H.W.boot_environment|exact HE]).',
        'pose proof(runtime_joint _ HA(H.F.seed image)H.empty(H.B.seed_shape image))as HR.',
        'assert(HI:Joint(H.F.seed image)H.empty)by(unfold Joint,Fields,H.empty;cbn;repeat split;intros token HT;discriminate).',
        'specialize(HR HI);rewrite ExtendedSVRuntimeHistory.phase_run_append in HR;exact HR. Qed.']
    last=rows[-1];component='HF'
    for _ in range(n-1):component=f'(proj2 {component})'
    lines += ['Theorem valid_terminal_identity image events:',
        f'let pre:=phase_run {program} events(H.F.boot image) in',
        'let packed:=H.boot_history image events in',
        f'Forall H.W.Environment events ->norm 1(read_signal pre {last["valid"]})<>0%Z ->',
        f'exists token,C.C.chain_tag{n-1}(snd packed)=Some token /\\',
        f'token_pc token=Some(norm 32(read_signal pre {last["root"]})) /\\',
        f'norm 5(read_signal pre {chain["rows"][-1]["root"]})=norm 5(C.C.chain_head_value(token_word token)).',
        'Proof. intros pre packed HE HV;destruct(H.boot_and_runtime_related image events HE)as[HC HW].',
        f'destruct(C.valid_field_{n-1}_has_value pre packed HC HV)as[token[HT HR]].',
        'destruct(boot_joint image events HE)as[HG HF];unfold Fields in HF.',
        f'exists token;split;[exact HT|];split;[exact({component} token HT)|exact HR]. Qed.',
        'Goal True. idtac "PC_COMPANION_AUDIT". exact I. Qed.',
        'Print Assumptions joint_phase. Print Assumptions runtime_joint. Print Assumptions boot_joint. Print Assumptions valid_terminal_identity.']
    return '\n'.join(lines)+'\n'

def render_write_identity(program,rows,chain,target,branch,with_rom=False):
    """Connect the actual bank endpoint, not the last enumerated stage."""
    indices=[i for i,r in enumerate(chain['rows'])if r['root']==target['endpoint']]
    if len(indices)!=1:raise ValueError('write endpoint must identify one token stage')
    i=indices[0];root=rows[i]['root'];sample=f'(phase_driven_state {program} ev pre)'
    component='HF'
    for _ in range(i):component=f'(proj2 {component})'
    if i<len(rows)-1:component=f'(proj1 {component})'
    guards=[f'Z.eqb(eval_expr {sample} {g})0%Z={str(not taken).lower()}'for g,taken in branch['guards']]
    names=' '.join(f'HG{k}'for k in range(len(guards)))
    name='actual_write_pc_rom_identity'if with_rom else'actual_write_pc_identity'
    prefix=['Require Import GeneratedCapturedROM.CapturedROM. Module RR:=GeneratedCapturedROM.CapturedROM.']if with_rom else[
        'Require Import GeneratedCoveredDestination.CoveredDestination GeneratedISADestinations.ISADestinations Lang.ExtendedSVBankPlan Lang.ExtendedSVRegisterBank.',
        'Module D:=GeneratedCoveredDestination.CoveredDestination.']
    body=[f'destruct(actual_write_pc_identity image events ev HE HEv HP {names})as[token[HT[HPC HW]]].',
          f'pose proof(RR.pipeline_field_{i}_content image events token HE HT)as HC.',
          'exists token;split;[exact HT|];split;[exact HPC|];split;',
          f'[exact(RR.content_at_pc image token _ HC HPC)|exact HW]. Qed.']if with_rom else[
        f'destruct(D.actual_write_destination_from_boot image events ev HE HEv HP {names})as[token[HT HW]].',
        'destruct(boot_joint image events HE)as[HG HF];unfold Fields in HF.',
        f'exists token;split;[exact HT|];split;[exact({component} token HT)|exact HW]. Qed.']
    return '\n'.join([
        *prefix,
        f'Theorem {name} image events ev:',
        f'let pre:=phase_run {program} events(H.F.boot image) in',
        'let packed:=H.boot_history image events in',
        'Forall H.W.Environment events ->H.W.Environment ev ->',
        f'process_matches_states pre {sample} {program.rsplit(".",1)[0]}.{branch["process"]}=true ->',
        *[g+' ->'for g in guards],
        f'exists token,C.C.chain_tag{i}(snd packed)=Some token /\\',
        f'token_pc token=Some(norm 32(read_signal pre {root})) /\\',
        *([f'token_word token=RR.lookup image(norm 32(read_signal pre {root})) /\\']if with_rom else[]),
        'forall instruction address rest,',
        'Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction instruction ->',
        'destination_registers instruction=address::rest ->',
        f'ExtendedSVBankPlan.bank_phase_operations {branch["total"]} pre {sample} GeneratedBank.AutoBank.bank_{branch["bank"]}_entries=',
        f'[ExtendedSVRegisterBank.WriteLane address(norm 32(eval_expr {sample} {branch["data"]}))].',
        'Proof. intros pre packed HE HEv HP '+names+'.',
        *body,
        'Goal True. idtac "WRITE_PC_AUDIT". exact I. Qed.',
        f'Print Assumptions {name}.',''])

def check(ast,module,history_provider,pc_provider,pair_provider,output,destination_provider=None,isa_provider=None,rom_provider=None):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    raw,profile,_=pc.fetch.origin.raw_binding(ast,module);program=profile['ast']['program']
    hp=Path(history_provider);pp=Path(pc_provider);fp=Path(pair_provider)
    plan=json.loads((hp/'plan.json').read_text());pr=json.loads((pp/'report.json').read_text())
    ns={b['namespace']:Path(b['directory'])for b in plan['paths']};env=json.loads((ns['GeneratedSeedBoot']/'plan.json').read_text())['environment']
    _,validity=pc.provenance.hb.boot.chain.render(ast,module);link=pc.provenance.hb.coverage.capture.discover(raw,{r['rd']for r in validity['rows']});chain=link['chain']
    pair=pr['pair'];scalars={r['root']:r for r in pc.fetch.origin.pending.analyze(raw)['scalar_transitions']}
    expr=lambda root:rtl.Parser(scalars[root]['next_expression']).complete()
    proof=pc.match(expr(pair['carrier']),expr(pair['valid_root']),expr(pair['pc_root']),pair['carrier'],pair['pc_root'],pair)
    expected=pc.render(program,module,pair,proof)
    if not(pr.get('accepted')is True and pr.get('coqc_exit')==pr.get('coqchk_exit')==0 and pr.get('assumptions_closed')is True
           and (pp/'CapturedPC.v').read_text()==expected and pr['source_sha256']==hashlib.sha256(expected.encode()).hexdigest()):raise ValueError('PC provider mismatch')
    rows=discover(raw,chain,pair['pc_root'])
    valid_by_rd={r['rd']:r['valid']for r in validity['rows']}
    for r in rows:r['valid']=valid_by_rd[chain['rows'][r['index']]['root']]
    for file,sha in env['input_hashes'].items():
        if pc.provenance.hb.boot.digest(file)!=sha:raise ValueError('environment data changed')
    if any(e['changed_signal']in [pair['pc_root']]+[r['root']for r in rows]for e in env['events'].values()):raise ValueError('environment overwrites PC companion')
    profile['coq_load_paths']=plan['paths']
    _,remaining,_,scalar_source,_=pc.fetch.origin.expressions.proposal(profile,{r['root']for r in rows})
    if remaining:raise ValueError('PC scalar residual')
    _,wires,wire_source=pc.fetch.rom.comb.proposal(profile,{e['root']for r in rows for e in r['route']['edges']})
    if wires['residuals']:raise ValueError('PC alias residual')
    ports={r['output_root']:i for i,r in enumerate(wires['ports'])}
    source='Module S.\n'+scalar_source+'\nEnd S.\nModule W.\n'+wire_source+'\nEnd W.\n'+render(program,module,rows,chain,pair['pc_root'],ports)
    extra_paths=[]
    if destination_provider is not None:
        import cpu_covered_write_destination as dest
        if isa_provider is None:raise ValueError('original ISA destination provider required')
        ip=Path(isa_provider);ir=json.loads((ip/'report.json').read_text())
        original=dest.history.isa.render((dest.history.isa.synthesis.ROOT/'dep/riscv-coq/src/riscv/Spec/ExecuteI.v').read_text())
        if not(ir.get('accepted')is True and ir.get('original_assumptions_only')is True
               and ir.get('coqc_exit')==ir.get('coqchk_exit')==0
               and (ip/'ISADestinations.v').read_text()==original):
            raise ValueError('ISA destination provider differs from original ExecuteI')
        dp=Path(destination_provider);dr=json.loads((dp/'report.json').read_text())
        targets,_=dest.history.discover(raw)
        if len(targets)!=1:raise ValueError('ambiguous actual write endpoint')
        target=targets[0];branches=dest.single.discover(raw,target['aliases'][0]if target['aliases']else target['endpoint'])
        if len(branches)!=1:raise ValueError('ambiguous actual write branch')
        _,covered=dest.coverage.render(ast,module,set(target['roots']))
        aliases=json.loads((dp/'aliases/report.json').read_text())
        dports={r['output_root']:i for i,r in enumerate(aliases['outputs'])}
        expected_dest=dest.render(raw,profile,target,covered,branches[0],dports,validity,True)
        if not(dr.get('accepted')is True and dr.get('coqc_exit')==dr.get('coqchk_exit')==0
               and dr.get('assumptions_closed')is True and dr.get('history_and_validity_derived_from_boot')is True
               and (dp/'CoveredDestination.v').read_text()==expected_dest
               and dr['source_sha256']==hashlib.sha256(expected_dest.encode()).hexdigest()):
            raise ValueError('write provider differs from raw reconstruction')
        source+=render_write_identity(program,rows,chain,target,branches[0])
        extra_paths=[(dp,'GeneratedCoveredDestination'),(dp/'bank','GeneratedBank'),
                     (dp/'aliases','GeneratedScalarComb'),(Path(isa_provider),'GeneratedISADestinations')]
    if rom_provider is not None:
        import cpu_captured_rom as rom
        if destination_provider is None:raise ValueError('ROM connection requires actual write destination')
        rp=Path(rom_provider);rr=json.loads((rp/'report.json').read_text());rplan=json.loads((rp/'plan.json').read_text())
        _,rs=pc.fetch.rom.render(ast,module);_,fs=pc.fetch.render(ast,module)
        reader=pair['reader'];reader_expr=f'(ESel 32 (EVar {reader["bank_width"]} {reader["bank_root"]}) {reader["offset"]})'
        rports=[int(i)for i,e in re.findall(r'Definition port_(\d+)_rhs : Expr := (.*)\.',fs)if e==reader_expr]
        if len(rports)!=1:raise ValueError('ROM expression ambiguous')
        lookup=rom.abstract_read(rtl.Parser(reader_expr).complete(),reader['bank_root'],pair['address_root'])
        content=rom.content_proof(expr(pair['carrier']),expr(pair['valid_root']),pair['carrier'],pair['word_input'])
        expected_rom='Module R.\n'+rs+'\nEnd R.\nModule G.\n'+pc.provenance.render(program,chain,module)+'\nEnd G.\n'+rom.render(program,module,pair,rports[0],lookup,content)+rom.render_pipeline(chain)
        if not(rr.get('accepted')is True and rr.get('coqc_exit')==rr.get('coqchk_exit')==0 and rr.get('assumptions_closed')is True
               and rplan['paths']==plan['paths'] and rplan['ast_sha256']==raw['source_sha256']
               and (rp/'CapturedROM.v').read_text()==expected_rom
               and rr['source_sha256']==hashlib.sha256(expected_rom.encode()).hexdigest()):raise ValueError('ROM history provider mismatch')
        source+=render_write_identity(program,rows,chain,target,branches[0],True)
        extra_paths.append((rp,'GeneratedCapturedROM'))
    file=out/'PCCompanions.v';file.write_text(source);flags=list(rtl.framework.FLAGS)
    for b in plan['paths']:flags+=['-R',b['directory'],b['namespace']]
    for folder,name in [(pp,'GeneratedCapturedPC'),(fp,'GeneratedFetchPairs'),(out,'GeneratedPCCompanions')]:flags+=['-R',str(folder.resolve()),name]
    for folder,name in extra_paths:flags+=['-R',str(folder.resolve()),name]
    (out/'plan.json').write_text(json.dumps(dict(rows=rows,ast_sha256=raw['source_sha256']),indent=2)+'\n')
    start=time.monotonic();c,t=run_stage([str(pc.fetch.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    result=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,complete_R_generated=False,isa_pc_order_proved=False,old_inv_read=False,source_sha256=hashlib.sha256(source.encode()).hexdigest())
    if c.returncode==0 and time.monotonic()-start<1200:
        marks=list(re.finditer(r'^PC_COMPANION_AUDIT\s*$',c.stdout,re.M));tail=c.stdout[marks[-1].end():]if marks else ''
        closed=len(marks)==1 and tail.count('Closed under the global context')==(4+bool(destination_provider)+bool(rom_provider)) and 'Axioms:'not in tail
        k,t=run_stage([str(pc.fetch.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedPCCompanions.PCCompanions'],out/'coqchk.log',1200-(time.monotonic()-start))
        result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,accepted=closed and k.returncode==0)
    result['actual_write_pc_connected']=bool(destination_provider and result['accepted'])
    result['actual_write_rom_content_connected']=bool(rom_provider and result['accepted'])
    result['seconds']=time.monotonic()-start;(out/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ['ast','ast-module','history-provider','pc-provider','pair-provider','output']:parser.add_argument('--'+key,required=True)
    parser.add_argument('--destination-provider');parser.add_argument('--isa-provider');parser.add_argument('--rom-provider')
    a=parser.parse_args();r=check(a.ast,a.ast_module,a.history_provider,a.pc_provider,a.pair_provider,a.output,a.destination_provider,a.isa_provider,a.rom_provider)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
