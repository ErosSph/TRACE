"""Discharge the actual RF effect of a zero source word, not all CPU effects."""
import argparse,json,time,hashlib,re
from pathlib import Path
import cpu_bank_adapter as banks
import cpu_pending_origins as origin
import cpu_comb_scalar_bindings as comb
from cpu_certificate_acceptance import run_stage
rtl=origin.pending.rtl


def address_roots(plan):
    if plan.name=='BPEmpty':return set()
    if plan.name=='BPSeq':return set().union(*(address_roots(p)for p in plan.args[0].args))
    if plan.name=='BPIf':return address_roots(plan.args[1])|address_roots(plan.args[2])
    if plan.name!='BPWord':raise ValueError('full-bank reset or unsupported operation')
    offset=plan.args[0]
    if offset.name=='EBinary'and offset.args[1].name=='BMul':
        for index,scale in [(offset.args[2],offset.args[3]),(offset.args[3],offset.args[2])]:
            if banks.literal(scale)==32 and index.name=='EVar'and index.args[0].name=='5':return {int(index.args[1].name)}
    raise ValueError('write index is not a direct five-bit lane address')


def plan_proof(plan):
    if plan.name=='BPEmpty':return 'constructor.'
    if plan.name=='BPWord':
        return 'constructor;[cbn[OnlyZeroWrite];cbn[eval_expr];rewrite HX;reflexivity|constructor].'
    if plan.name=='BPSeq':
        parts=['apply zero_plan_seq.']
        for child in plan.args[0].args:parts+=['constructor. { '+plan_proof(child)+' }']
        return '\n'.join(parts+['constructor.'])
    if plan.name=='BPIf':return 'apply zero_plan_if. { '+plan_proof(plan.args[1])+' } { '+plan_proof(plan.args[2])+' }'
    raise ValueError('unsupported plan')


def discover(ast):
    analysis=banks.analyze(ast);rows=[];residuals=list(analysis['residuals'])
    carriers=set(origin.pending.analyze(ast)['instruction_word_candidates'])
    for bank in analysis['banks']:
        try:
            addresses=set().union(*(address_roots(bp)for _,_,bp in bank['plans']))
            if len(addresses)!=1:raise ValueError('requires one common write-address field')
            addr=next(iter(addresses));writers=[p for p in ast['processes']if p['kind']!='Initial'and addr in p['writers']]
            if len(writers)!=1 or writers[0]['kind']!='Combinational':raise ValueError('write address needs temporal provenance')
            body=writers[0]['body']
            if body.name!='SAssign'or body.args[0].name!='false':raise ValueError('address writer is not a direct blocking expression')
            rhs=body.args[1]
            if not(rhs.name=='ESel'and rhs.args[0].name=='5'and rhs.args[1].name=='EVar'
                and rhs.args[1].args[0].name=='32'and rhs.args[2].name=='EConst'):
                raise ValueError('address is not a constant slice of a word')
            word=int(rhs.args[1].args[1].name)
            if word not in carriers:raise ValueError('source is not an instruction-word structural candidate')
            rows.append(dict(bank=bank,address=addr,word=word))
        except ValueError as exc:residuals.append(dict(root=bank['root'],reason=str(exc)))
    return rows,residuals


def render(ast_path,ast_module):
    ast,profile,paths=origin.raw_binding(ast_path,ast_module);rows,residuals=discover(ast)
    if not rows:raise ValueError('no direct zero-word RF path: '+json.dumps(residuals))
    analysis=dict(banks=[r['bank']for r in rows],residuals=[],candidate_count=len(rows))
    bank_source=banks.render_bank_adapter(profile['ast'],ast,analysis)
    _,ports,comb_source=comb.proposal(profile,[r['address']for r in rows])
    if ports['residuals']:raise ValueError('unproved actual address connection')
    port_index={p['output_root']:i for i,p in enumerate(ports['ports'])};p=profile['ast']['program']
    lines=['Require Import Ex.External.CPUZeroRegisterEffect Ex.RvCore.FormalSpec.',
        'Import CPUZeroRegisterEffect CPURegisterEffectRelation.',f'Local Opaque {p}.']
    for row in rows:
        bank=row['bank'];root=bank['root'];addr=row['address'];word=row['word'];i=port_index[addr]
        lines += [f'Lemma zero_word_address_{root} seed fixed:CombLFP {p} seed fixed ->',
            f' norm 32(read_signal fixed {word})=0%Z ->norm 5(read_signal fixed {addr})=0%Z.',
            f'Proof. intros HL HZ;rewrite(port_{i}_lfp seed fixed HL).',
            f' unfold port_{i}_rhs;cbn[eval_expr];rewrite HZ;reflexivity. Qed.']
        for proc,nb,bp in bank['plans']:
            name=f'bank_{root}_{proc["name"]}_plan'
            lines += [f'Lemma zero_plan_{root}_{proc["name"]} fixed:norm 5(read_signal fixed {addr})=0%Z ->',
                f' Forall OnlyZeroWrite(eval_bank_plan {bank["total"]} fixed {name}).',
                f'Proof. intro HX;unfold {name}. {plan_proof(bp)} Qed.']
        lines += [f'Lemma zero_word_operations_{root} seed ev pre:',
            f' CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
            f' norm 32(read_signal(phase_driven_state {p} ev pre){word})=0%Z ->',
            f' Forall OnlyZeroWrite(bank_phase_operations {bank["total"]} pre(phase_driven_state {p} ev pre)bank_{root}_entries).',
            f'Proof. intros HL HZ;pose proof(zero_word_address_{root} _ _ HL HZ)as HX.',
            f' apply zero_phase_entries;unfold bank_{root}_entries.']
        for proc,_,_ in bank['plans']:
            lines += [f' constructor;[exact(zero_plan_{root}_{proc["name"]} _ HX)|].']
        lines += [' constructor. Qed.',f'Section Register{root}.',
            'Context {word:Interface.word 32}{Registers:map.map Z word}{Mem:map.map word byte}.',
            f'Theorem zero_word_rf_{root} seed ev pre(before:FormalSpec.State):',
            f' changed_signal ev<>{root}%nat ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->',
            f' norm 32(read_signal(phase_driven_state {p} ev pre){word})=0%Z ->',
            f' RegisterRelated(lane_read 32(read_signal pre {root}))before ->',
            f' RegisterRelated(lane_read 32(read_signal(PhaseSemantics {p} ev pre){root}))before.',
            f'Proof. intros HE HL HZ HR;exact(actual_phase_preserves_registers {p} {root} {bank["total"]}',
            f' bank_{root}_entries bank_{root}_certificate ev pre before HE HR(zero_word_operations_{root} seed ev pre HL HZ)). Qed.',
            f'End Register{root}.',f'Goal True. idtac "ZERO_RF_AUDIT_{root}". exact I. Qed.',
            f'Print Assumptions zero_word_rf_{root}.']
    return dict(paths=paths,rows=[dict(bank=r['bank']['root'],address=r['address'],word=r['word'])for r in rows],residuals=residuals),bank_source+'\n'+comb_source+'\n'+'\n'.join(lines)+'\n'


def render_condition(ast_path,ast_module):
    """Generate a guarded RF preservation obligation; do not assert its reachability."""
    ast,profile,paths=origin.raw_binding(ast_path,ast_module)
    analysis=banks.analyze(ast)
    if not analysis['banks']:raise ValueError('no checked physical bank candidate')
    p=profile['ast']['program'];lines=[banks.render_bank_adapter(profile['ast'],ast,analysis),
        'Require Import Ex.External.CPUZeroRegisterEffect Ex.RvCore.FormalSpec.',
        'Import CPUZeroRegisterEffect CPURegisterEffectRelation.',f'Local Opaque {p}.']
    rows=[]
    for bank in analysis['banks']:
        root,total=bank['root'],bank['total']
        # Depth bound is a proposal. The generic checker rejects exhausted fuel.
        def depth(t):
            if t.name=='BPSeq':return 1+max((depth(x)for x in t.args[0].args),default=0)
            if t.name=='BPIf':return 1+max(depth(t.args[1]),depth(t.args[2]))
            return 1
        fuel=max((depth(bp)for _,_,bp in bank['plans']),default=1)
        rows.append(dict(bank=root,fuel=fuel,processes=[proc['name']for proc,_,_ in bank['plans']]))
        lines += [f'Definition rf_stutter_condition_{root} ev pre :=',
            f' zero_phase_condition {fuel} pre (phase_driven_state {p} ev pre) bank_{root}_entries.',
            f'Section Register{root}.',
            'Context {word:Interface.word 32}{Registers:map.map Z word}{Mem:map.map word byte}.',
            f'Theorem guarded_rf_{root} ev pre(before:FormalSpec.State):',
            f' changed_signal ev<>{root}%nat ->',
            f' rf_stutter_condition_{root} ev pre=true ->',
            f' RegisterRelated(lane_read 32(read_signal pre {root}))before ->',
            f' RegisterRelated(lane_read 32(read_signal(PhaseSemantics {p} ev pre){root}))before.',
            f'Proof. intros HE HC HR;exact(actual_phase_preserves_registers {p} {root} {total}',
            f' bank_{root}_entries bank_{root}_certificate ev pre before HE HR',
            f' (zero_phase_condition_sound {fuel} {total} pre (phase_driven_state {p} ev pre) bank_{root}_entries HC)). Qed.',
            f'End Register{root}.',f'Goal True. idtac "ZERO_RF_AUDIT_{root}". exact I. Qed.',
            f'Print Assumptions guarded_rf_{root}.']
    return dict(paths=paths,rows=rows,residuals=analysis['residuals']), '\n'.join(lines)+'\n'


def render_reference(ast_path,ast_module):
    """Derive lane-level ISA write obligations from every real bank writer."""
    ast,profile,paths=origin.raw_binding(ast_path,ast_module)
    analysis=banks.analyze(ast)
    if not analysis['banks']:raise ValueError('no checked physical bank candidate')
    p=profile['ast']['program'];lines=[banks.render_bank_adapter(profile['ast'],ast,analysis),
        'Require Import Ex.External.CPURegisterLastWrite Ex.External.CPUISAReferenceWrites Ex.RvCore.FormalSpec.',
        'Import CPURegisterLastWrite CPURegisterEffectRelation.',f'Local Opaque {p}.']
    rows=[]
    for bank in analysis['banks']:
        root,total=bank['root'],bank['total']
        rows.append(dict(bank=root,processes=[proc['name']for proc,_,_ in bank['plans']],
            indices=list(range(1,32))))
        lines += [f'Section Reference{root}.',
            'Context {word:Interface.word 32}{Registers:map.map Z word}{Mem:map.map word byte}.',
            f'Definition reference_obligations_{root} ev pre (before:FormalSpec.State) write :=',
            f' forall index:Z,(0<index<32)%Z ->reference_lane_obligation before write',
            f' (bank_phase_operations {total} pre(phase_driven_state {p} ev pre)bank_{root}_entries)index.',
            f'Theorem actual_reference_rf_{root} ev pre (before after:FormalSpec.State) write:',
            f' changed_signal ev<>{root}%nat ->',
            f' RegisterRelated(lane_read 32(read_signal pre {root}))before ->',
            ' CPUISAReferenceWrites.write_effect before after write ->',
            f' reference_obligations_{root} ev pre before write ->',
            f' RegisterRelated(lane_read 32(read_signal(PhaseSemantics {p} ev pre){root}))after.',
            f'Proof. exact(actual_phase_reference_write {p} {root} {total} bank_{root}_entries',
            f' bank_{root}_certificate ev pre before after write). Qed.',
            f'End Reference{root}.',f'Goal True. idtac "ZERO_RF_AUDIT_{root}". exact I. Qed.',
            f'Print Assumptions actual_reference_rf_{root}.']
    return dict(paths=paths,rows=rows,residuals=analysis['residuals']), '\n'.join(lines)+'\n'


def last_expression(plan,total,index,state):
    """Symbolic option value with exact last-writer priority, no CPU-specific rules."""
    expr=lambda t:f'(eval_expr {state} ({rtl.render(t)}))'
    def later(a,b):return b if a=='(@None Z)' else a if b=='(@None Z)' else f'(match {b} with Some v=>Some v|None=>{a} end)'
    if plan.name=='BPEmpty':return '(@None Z)'
    if plan.name=='BPWord':
        offset,value=plan.args
        return f'(if Z.eqb {index} (Z.div {expr(offset)} 32) then Some(norm 32(norm 32 {expr(value)})) else None)'
    if plan.name=='BPReset':return f'(Some(lane_read 32(norm {total} {expr(plan.args[0])}) {index}%Z))'
    if plan.name=='BPIf':
        guard,yes,no=plan.args
        return f'(if Z.eqb {expr(guard)} 0 then {last_expression(no,total,index,state)} else {last_expression(yes,total,index,state)})'
    if plan.name=='BPSeq':
        result='(@None Z)'
        for child in plan.args[0].args:result=later(result,last_expression(child,total,index,state))
        return result
    raise ValueError('unsupported bank-plan constructor; no update dropped')


def render_slices(ast_path,ast_module):
    ast,profile,paths=origin.raw_binding(ast_path,ast_module)
    analysis=banks.analyze(ast)
    if not analysis['banks']:raise ValueError('no checked physical bank candidate')
    p=profile['ast']['program'];mod=ast['module']
    lines=[banks.render_bank_adapter(profile['ast'],ast,analysis),
        'Require Import Ex.External.CPURegisterLastWrite.',
        'Import CPURegisterLastWrite.',f'Local Opaque {p}.']
    rows=[]
    for bank in analysis['banks']:
        root,total=bank['root'],bank['total'];names=[]
        # A symbolic index covers all lanes, including physical lane zero.
        result='(@None Z)'
        for proc,_,plan in bank['plans']:
            name=f'lane_{root}_{proc["name"]}';names.append(name)
            body=last_expression(plan,total,'index','driven')
            plan_name=f'bank_{root}_{proc["name"]}_plan'
            lines += [f'Definition {name} (index:Z)(driven:State):option Z := {body}.',
                f'Lemma {name}_exact index driven:last_value 32 index(eval_bank_plan {total} driven {plan_name})={name} index driven.',
                f'Proof. unfold {plan_name},{name}.',
                ' repeat first [rewrite last_value_append | rewrite last_value_if | rewrite eval_bank_plan_if | rewrite option_value_identity | progress (cbn [eval_bank_plan flat_map last_value operation_value])].',
                ' reflexivity. Qed.']
            current=f'(if process_matches_states pre driven {mod}.{proc["name"]} then {name} index driven else None)'
            result=current if result=='(@None Z)' else f'(match {current} with Some v=>Some v|None=>{result} end)'
        lines += [f'Definition lane_{root}_last (index:Z)(pre driven:State):option Z := {result}.',
            f'Theorem lane_{root}_exact index pre driven:',
            f' last_value 32 index(bank_phase_operations {total} pre driven bank_{root}_entries)=lane_{root}_last index pre driven.',
            'Proof. intros.']
        # Rewrite list concatenation rather than asking conversion to split
        # a conditional list with unknown process triggers.
        definitions=', '.join(['bank_'+str(root)+'_entries',f'lane_{root}_last'])
        lines += [f' unfold {definitions}.',
            ' cbn [bank_phase_operations flat_map bank_plan bank_process].',
            ' repeat first [rewrite last_value_append | rewrite last_value_if | rewrite option_value_identity | progress (cbn [last_value])].',
            ' '+''.join(f'repeat rewrite {name}_exact. 'for name in names),
            ' repeat rewrite option_value_associate.',
            ' reflexivity. Qed.',
            f'Goal True. idtac "ZERO_RF_AUDIT_{root}". exact I. Qed.',f'Print Assumptions lane_{root}_exact.']
        rows.append(dict(bank=root,processes=[p['name']for p,_,_ in bank['plans']],
            symbolic_index=True,condition_discharged=False))
    return dict(paths=paths,rows=rows,residuals=analysis['residuals']), '\n'.join(lines)+'\n'


def check(ast_path,ast_module,output,derive_condition=False,derive_reference=False,derive_slices=False):
    if sum([derive_condition,derive_reference,derive_slices])>1:raise ValueError('choose one generation mode')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    report=dict(accepted=False,old_inv_read=False,complete_R_generated=False,all_architectural_effects_proved=False,
        scope='zero sampled word preserves actual RF relation; PC/memory/IO not covered')
    if derive_condition:
        report.update(scope='generated sufficient RF stutter condition implies actual RF preservation',
            condition_discharged=False,initialization_proved=False,
            condition_kind='all triggered bank operations target lane zero; resets rejected')
    if derive_reference:
        report.update(scope='actual bank last-write obligations imply original ISA RF effect correspondence',
            condition_discharged=False,isa_execution_proved=False,initialization_proved=False)
    if derive_slices:
        report.update(scope='symbolic last-write expressions equal actual ordered bank effects',
            condition_discharged=False,isa_execution_proved=False)
    renderer=render_slices if derive_slices else render_reference if derive_reference else render_condition if derive_condition else render
    try:data,source=renderer(ast_path,ast_module)
    except ValueError as exc:
        report.update(status='unsupported_zero_word_rf',residual=str(exc))
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    file=output/'ZeroWordRF.v';file.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for row in data['paths']:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedZeroWordRF']
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],output/'coqc.log',1200)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,rows=data['rows'],source_sha256=hashlib.sha256(source.encode()).hexdigest())
    if c.returncode==0 and time.monotonic()<deadline:
        markers=list(re.finditer(r'^ZERO_RF_AUDIT_\d+\s*$',c.stdout,re.M))
        segments=[c.stdout[m.end():markers[i+1].start()if i+1<len(markers)else len(c.stdout)]for i,m in enumerate(markers)]
        closed=len(segments)==len(data['rows'])and all(x.count('Closed under the global context')==1 and'Axioms:'not in x for x in segments)
        report['export_assumptions_closed']=closed
        k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedZeroWordRF.ZeroWordRF'],output/'coqchk.log',deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0 and closed)
    report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:p.add_argument('--'+name,required=True)
    p.add_argument('--derive-condition',action='store_true')
    p.add_argument('--derive-reference',action='store_true')
    p.add_argument('--derive-slices',action='store_true')
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output,a.derive_condition,a.derive_reference,a.derive_slices);print(json.dumps(r,indent=2))
    raise SystemExit(0 if r['accepted']else 1)
