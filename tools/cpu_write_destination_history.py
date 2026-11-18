"""Discover write-index stage chains and connect captured Rd history to ISA."""
import argparse, hashlib, json, time
from pathlib import Path
import cpu_field_chain_history as chain
import cpu_bank_index_certificate as index
import cpu_isa_destination_certificate as isa
from cpu_certificate_acceptance import run_stage


def discover(ast):
    graph=chain.discover(ast);rows=graph['rows'];byroot={r['root']:i for i,r in enumerate(rows)}
    targets=[];residuals=[]
    for site in index.ownership.analyze(ast)['writes']:
        match=index.recognize(site['offset'])if site['offset'] is not None else None
        expr=index.rtl.Parser(match['index']).complete()if match else None
        if expr is None or expr.name!='EVar' or expr.args[0].name!='5':
            reason=('whole-bank update requires separate reset proof' if site['offset'] is None
                    else 'index is not a supported five-bit registered field; constant lanes need enable decoding')
            item=dict(process=site['process'],reason=reason)
            if item not in residuals:residuals.append(item)
            continue
        current=int(expr.args[1].name);seen=set();aliases=[]
        while current not in byroot and current not in seen:
            seen.add(current);writers=[p for p in ast['processes']if current in p['writers']]
            if len(writers)!=1 or writers[0]['kind']!='Combinational':break
            st=writers[0]['body']
            if st.name!='SAssign' or st.args[0].name!='false':break
            rhs,lhs=st.args[1:]
            if rhs.name!='EVar' or rhs.args[0].name!='5' or lhs.name!='LVar' or lhs.args[0].name!='5':break
            aliases.append(current);current=int(rhs.args[1].name)
        if current not in byroot:
            residuals.append(dict(process=site['process'],reason='no supported registered index history'));continue
        roots={current}
        while True:
            more={rows[e['source']]['root']for e in graph['edges']if rows[e['target']]['root']in roots}-roots
            if not more:break
            roots.update(more)
        selected=chain.discover(ast,roots);head=selected['head']
        field=chain.rf.rtl.Parser(head['expression']).complete()if head else None
        import cpu_instruction_fields as fields
        layout=fields.match_field(field,5)if field else None
        if not layout or layout['field']!='Rd':
            residuals.append(dict(process=site['process'],reason='history head is not a proved Rd extraction'));continue
        targets.append(dict(endpoint=current,roots=sorted(roots),aliases=aliases,head=head))
    # Distinct actual index routes may share a pipeline endpoint. Do not
    # discard one merely because their history subgraphs are identical.
    unique={(tuple(t['roots']),t['endpoint'],tuple(t['aliases'])):t for t in targets}
    return list(unique.values()),residuals


def check(ast_path,ast_module,isa_provider,output,chain_provider=None):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    ast,profile,paths=chain.p.origins.raw_binding(ast_path,ast_module)
    targets,residuals=discover(ast)
    report=dict(accepted=False,targets=targets,residuals=residuals,old_inv_read=False,
        boundary_identity_proved=False,history_presence_proved=False,
        actual_write_event_connected=False,complete_R_generated=False)
    if len(targets)!=1:
        report['status']='no_unique_supported_destination_history'
        (out/'report.json').write_text(json.dumps(report,indent=2));return report
    target=targets[0];source,data=chain.render(ast_path,ast_module,set(target['roots']))
    if chain_provider is None:
        chain_provider=out/'chain'
        generated=chain.check(ast_path,ast_module,chain_provider,set(target['roots']))
        if generated.get('accepted') is not True:
            report.update(status='history_certificate_not_available',history_certificate=generated)
            (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
            return report
    chain_provider=Path(chain_provider);rp=json.loads((chain_provider/'report.json').read_text())
    if not(rp.get('accepted')is True and rp.get('coqc_exit')==rp.get('coqchk_exit')==0
           and rp.get('export_assumptions_closed')is True
           and rp.get('source_sha256')==hashlib.sha256(source.encode()).hexdigest()
           and(chain_provider/'FieldChain.v').read_text()==source
           and(chain_provider/'FieldChain.vo').is_file()):raise ValueError('raw history provider mismatch')
    isa_provider=Path(isa_provider);ir=json.loads((isa_provider/'report.json').read_text())
    original=isa.render((isa.synthesis.ROOT/'dep/riscv-coq/src/riscv/Spec/ExecuteI.v').read_text())
    if not(ir.get('accepted')is True and ir.get('coqc_exit')==ir.get('coqchk_exit')==0
           and ir.get('original_assumptions_only') is True
           and(isa_provider/'ISADestinations.vo').is_file()
           and ir.get('source_sha256')==hashlib.sha256(original.encode()).hexdigest()
           and(isa_provider/'ISADestinations.v').read_text()==original):raise ValueError('ISA provider mismatch')
    root=target['endpoint'];n=next(i for i,r in enumerate(data['rows'])if r['root']==root)
    src=target['head']['source'];count=len(data['rows'])
    profile['coq_load_paths']=paths
    alias_ports={}
    if target['aliases']:
        aliases=chain.rf.comb.check_profile(profile,out/'aliases',target['aliases'])
        report['alias_certificate']=aliases
        if not aliases.get('accepted'):
            report['status']='write_index_alias_certificate_unavailable'
            (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
        alias_ports={r['output_root']:i for i,r in enumerate(aliases['outputs'])}
    lines=['From Coq Require Import List ZArith.',f'Require Import {ast_module}.',
        'Require Import GeneratedFieldChain.FieldChain GeneratedISADestinations.ISADestinations',
        ' Ex.External.CPUInstructionFields Lang.ExtendedSV Lang.ExtendedSVWordInvariant.',
        'Import ListNotations ExtendedSV ExtendedSVWordInvariant CPUInstructionFields.',
        'Lemma destination_head code:norm 5(chain_head_value code)=field_reference code Rd.',
        'Proof.',f'change (norm 5 (norm 5 (eval_expr (write_signal [] {src} code) (field_expr {src} Rd))) = field_reference code Rd).',
        f'exact(eq_trans(norm_idempotent 5 (eval_expr(write_signal [] {src} code)(field_expr {src} Rd)))',
        f' (eq_trans(native_field_reference (write_signal [] {src} code) {src} Rd)',
        f' (f_equal(fun value=>field_reference value Rd)(read_signal_write_same [] {src} code)))). Qed.',
        'Theorem captured_destination {Label:Type}(word:Label->Z)pre tags events post final label instruction address rest:',
        'ChainExecution word pre tags events post final ->ChainRelated word pre tags ->',
        f'chain_tag{n} final=Some label ->',
        'Decode.decode Decode.RV32I(word label)=Decode.IInstruction instruction ->',
        'destination_registers instruction=address::rest ->',
        f'norm 5(read_signal post {root})=address.',
        'Proof. intros HX HR HT HD HS.',
        'pose proof(chain_history_preserved word pre tags events post final HX HR)as HP.',
        'unfold ChainRelated in HP.']
    # Project one component without proof search or unfolding the RTL program.
    for i in range(count-1):
        if i==n:lines+=['destruct HP as[Hdest Hrest].'];break
        lines+=['destruct HP as[Hskip HP];clear Hskip.']
    else:lines+=['rename HP into Hdest.']
    lines += ['specialize(Hdest label HT);rewrite destination_head in Hdest.',
        'exact(eq_trans Hdest(eq_sym(original_destination_address(word label)instruction address rest HD HS))). Qed.',
        'Print Assumptions destination_head. Print Assumptions captured_destination.']
    program=profile['ast']['program'];index_root=target['aliases'][0] if target['aliases'] else root
    if alias_ports:lines+=['Require Import GeneratedScalarComb.ScalarCombBindings.']
    lines+=['Require Import Lang.ExtendedSVScalarHistory Lang.ExtendedSVRootProjection Lang.ExtendedSVScalarExpression.',
        'Import ExtendedSVScalarHistory ExtendedSVRootProjection ExtendedSVScalarExpression.',
        'Theorem sampled_destination {Label:Type}(word:Label->Z) pre tags events post final',
        ' label instruction address rest ev seed:',
        'ChainExecution word pre tags events post final ->ChainRelated word pre tags ->',
        f'chain_tag{n} final=Some label ->',
        'Decode.decode Decode.RV32I(word label)=Decode.IInstruction instruction ->',
        'destination_registers instruction=address::rest ->',
        f'changed_signal ev<>{root}%nat ->',
        f'CombLFP {program} seed(phase_driven_state {program} ev post) ->',
        f'norm 5(read_signal(phase_driven_state {program} ev post){index_root})=address.',
        'Proof. intros HX HR HT HD HS HE HL.']
    for alias in target['aliases']:
        i=alias_ports[alias]
        lines += [f'rewrite(GeneratedScalarComb.ScalarCombBindings.port_{i}_lfp seed _ HL).',
                  f'unfold GeneratedScalarComb.ScalarCombBindings.port_{i}_rhs;cbn[eval_expr];rewrite norm_idempotent.']
    lines += [f'rewrite(sampled_root_preserved {program} ev post {root}%nat',
        f' (history_comb_frame _ _ _ _ _ root_{root}_projection_certificate) HE).',
        'exact(captured_destination word pre tags events post final label instruction address rest HX HR HT HD HS). Qed.',
        'Print Assumptions sampled_destination.']
    # Connect the history endpoint to a COMPLETE guarded bank update. Do not
    # select a leaf while silently dropping other simultaneous writes.
    import cpu_single_bank_branch as single
    branches=single.discover(ast,index_root)
    exports=3
    if len(branches)==1:
        branch=branches[0]
        bank_check=index.ownership.bank.check_profile(profile,out/'bank')
        report['bank_certificate']=bank_check
        if bank_check.get('accepted') is not True:
            report['status']='complete_bank_certificate_unavailable'
            (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
        lines += ['From Coq Require Import Lia.',
                  'Require Import GeneratedBank.AutoBank Lang.ExtendedSVRegisterBank.',
                  'Import ExtendedSVRegisterBank.',single.render(ast,branch)]
        br=branch['bank'];proc=ast['module']+'.'+branch['process']
        sample=f'(phase_driven_state {program} ev post)'
        value=f'(norm 32(eval_expr {sample} {branch["data"]}))'
        guards=[f'Z.eqb(eval_expr {sample} {g})0={str(not taken).lower()}' for g,taken in branch['guards']]
        params=['{Label:Type}(word:Label->Z) pre tags events post final',
                'label instruction address rest ev seed']
        assumptions=['ChainExecution word pre tags events post final ->ChainRelated word pre tags ->',
            f'chain_tag{n} final=Some label ->',
            'Decode.decode Decode.RV32I(word label)=Decode.IInstruction instruction ->',
            'destination_registers instruction=address::rest ->',
            f'changed_signal ev<>{root}%nat ->',
            f'CombLFP {program} seed {sample} ->',
            f'process_matches_states post {sample} {proc}=true ->',
            *[g+' ->' for g in guards]]
        names=' '.join(f'HG{i}' for i in range(len(guards)))
        lines += ['Theorem history_actual_bank_destination '+ ' '.join(params)+':',*assumptions,
            f'bank_phase_operations {branch["total"]} post {sample} bank_{br}_entries=[WriteLane address {value}].',
            'Proof. intros HX HR HT HD HS HE HL HP '+names+'.',
            f'exact(selected_bank_write post {sample} address HP {names}',
            ' (sampled_destination word pre tags events post final label instruction address rest ev seed HX HR HT HD HS HE HL)). Qed.',
            'Print Assumptions history_actual_bank_destination.',
            'Theorem history_actual_phase_destination '+ ' '.join(params)+':',*assumptions,
            f'changed_signal ev<>{br}%nat ->',
            f'read_signal(PhaseSemantics {program} ev post){br}=',
            f'apply_updates_root_value {br}(read_signal post {br})(operation_updates {br} 32 [WriteLane address {value}]).',
            'Proof. intros HX HR HT HD HS HE HL HP '+names+' HB.',
            f'pose proof(history_actual_bank_destination word pre tags events post final label instruction address rest ev seed HX HR HT HD HS HE HL HP {names})as HO.',
            f'exact(eq_trans(bank_phase_updates {program} {br}%nat {branch["total"]}%nat bank_{br}_entries bank_{br}_certificate ev post HB)',
            f' (f_equal(fun ops=>apply_updates_root_value {br}(read_signal post {br})(operation_updates {br} 32 ops))HO)). Qed.',
            'Print Assumptions history_actual_phase_destination.']
        exports+=3
    text='\n'.join(lines)+'\n';file=out/'DestinationHistory.v';file.write_text(text)
    flags=list(index.rtl.framework.FLAGS)
    for p in paths:flags+=['-R',p['directory'],p['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedDestinationHistory','-R',str(chain_provider.resolve()),'GeneratedFieldChain','-R',str(isa_provider.resolve()),'GeneratedISADestinations']
    if alias_ports:flags+=['-R',str((out/'aliases').resolve()),'GeneratedScalarComb']
    if len(branches)==1:flags+=['-R',str((out/'bank').resolve()),'GeneratedBank']
    start=time.monotonic();c,t=run_stage([str(index.rtl.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(text.encode()).hexdigest())
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==exports and'Axioms:'not in c.stdout
        k,t=run_stage([str(index.rtl.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedDestinationHistory.DestinationHistory'],out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,
            sampled_write_index_connected=closed and k.returncode==0,accepted=closed and k.returncode==0)
        report['conditional_actual_write_event_connected']=len(branches)==1 and closed and k.returncode==0
    report['seconds']=time.monotonic()-start
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for arg in ['ast','ast-module','isa-provider','output']:p.add_argument('--'+arg,required=True)
    p.add_argument('--chain-provider');a=p.parse_args()
    r=check(a.ast,a.ast_module,a.isa_provider,a.output,a.chain_provider);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
