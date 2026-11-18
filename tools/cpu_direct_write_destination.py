"""Join a same-sample decoded Rd to the actual single bank-write operation.
Cross-stage cases are residuals, never connected by signal naming alone.
"""
import argparse, hashlib, json, time
from pathlib import Path
import cpu_bank_index_certificate as indices
import cpu_destination_field_connection as destinations
from cpu_certificate_acceptance import run_stage
ownership=indices.ownership
rtl=ownership.rtl


def discover(ast, fields):
    banks=ownership.bank.analyze(ast)
    candidates=[r for r in fields if r['field']=='Rd' and r['kind']=='Combinational']
    byroot={r['root']:r for r in candidates if sum(x['root']==r['root'] for x in candidates)==1}
    rows=[];residuals=[]
    for bank in banks['banks']:
        leaves=[(proc,path,guards,leaf) for proc,_,plan in bank['plans']
                for path,guards,leaf in ownership.leaves(plan)]
        if len(bank['plans'])!=1 or len(leaves)!=1:
            residuals.append(dict(bank=bank['root'],reason='requires ordered multiple/guarded write composition'))
            continue
        proc,path,guards,leaf=leaves[0]
        if guards or leaf.name!='BPWord':
            residuals.append(dict(bank=bank['root'],reason='not an unconditional single lane write'))
            continue
        offset,data=leaf.args; match=indices.recognize(rtl.render(offset))
        index=rtl.Parser(match['index']).complete() if match else None
        if index is None or index.name!='EVar' or int(index.args[1].name) not in byroot:
            residuals.append(dict(bank=bank['root'],reason='write index needs stage history or other field connection'))
            continue
        field=byroot[int(index.args[1].name)]
        if field['width']!=int(index.args[0].name):
            residuals.append(dict(bank=bank['root'],reason='index/field width mismatch'));continue
        rows.append(dict(bank=bank['root'],total=bank['total'],process=proc['name'],
                         offset=rtl.render(offset),data=rtl.render(data),index=match,field=field))
    return rows,residuals


def check(ast_path, ast_module, field_provider, isa_provider, bank_provider, output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    ast,profile,paths=ownership.origin.raw_binding(ast_path,ast_module)
    profile['coq_load_paths']=paths
    _,remaining,fields,field_source,_,_=destinations.inputs.fields.proposal(profile)
    rows,residuals=discover(ast,fields)
    report=dict(accepted=False,connections=len(rows),residuals=residuals,old_inv_read=False,
        write_value_is_isa_result_proved=False,current_token_identity_proved=False,complete_R_generated=False)
    if not rows:
        report['status']='requires_nonlocal_write_destination_connection'
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    # Reuse the same checked-provider gate as the destination connector.
    dr=destinations.check(ast_path,ast_module,field_provider,isa_provider,out/'destination')
    if not dr['accepted']:raise ValueError('destination field component failed')
    bank_provider=Path(bank_provider);br=json.loads((bank_provider/'report.json').read_text())
    bank_source=ownership.bank.render_bank_adapter(profile['ast'],ast,ownership.bank.analyze(ast))
    bf=bank_provider/'AutoBank.v'
    if not(br.get('accepted') is True and br.get('coqc_exit')==br.get('coqchk_exit')==0
           and bf.read_text()==bank_source and bf.with_suffix('.vo').is_file()
           and br.get('generated_source_sha256')==hashlib.sha256(bank_source.encode()).hexdigest()):
        raise ValueError('original bank provider mismatch')
    p=profile['ast']['program']
    lines=[f'Require Import {ast_module}.',
        'From Coq Require Import List ZArith Lia.',
        'Require Import GeneratedBank.AutoBank GeneratedDestinationFields.DestinationFields',
        ' GeneratedInstructionFields.InstructionFields GeneratedISADestinations.ISADestinations',
        ' Lang.ExtendedSV Lang.ExtendedSVBankPlan Lang.ExtendedSVBankIndex Lang.ExtendedSVRegisterBank',
        ' Lang.ExtendedSVExpressionPath Lang.ExtendedSVRootProjection.',
        'Require Import Ex.External.CPUSingleWriteEffect Ex.External.CPURegisterEffectRelation',
        ' Ex.External.CPUOriginalISAReference Ex.RvCore.FormalSpec coqutil.Word.Interface',
        ' coqutil.Map.Interface coqutil.Byte coqutil.Word.Bitwidth.',
        'Import CPURegisterEffectRelation CPUOriginalISAReference.',
        'Import ListNotations ExtendedSV ExtendedSVBankPlan ExtendedSVBankIndex ExtendedSVRegisterBank ExtendedSVExpressionPath ExtendedSVRootProjection.']
    for n,row in enumerate(rows):
        f=row['field'];root=row['bank'];proc=ast['module']+'.'+row['process']
        entries=f'bank_{root}_entries';plan=f'bank_{root}_{row["process"]}_plan'
        value=f'(norm 32(eval_expr driven {row["data"]}))'
        lines += [f'Theorem write_{n}_actual_destination pre driven seed code instruction address rest:',
            f'CombLFP {p} seed driven ->',
            f'PathHolds driven {f["original"]} {f["name"]}_choices ->',
            f'norm 32(read_signal driven {f["source"]})=norm 32 code ->',
            'Decode.decode Decode.RV32I code=Decode.IInstruction instruction ->',
            'destination_registers instruction=address::rest ->',
            f'process_matches_states pre driven {proc}=true ->',
            f'bank_phase_operations {row["total"]} pre driven {entries}=[WriteLane address {value}].',
            'Proof. intros HL HP HW HD HS HT.',
            f'pose proof({f["name"]}_destination seed driven code instruction address rest HL HP HW HD HS)as HA.',
            f'unfold bank_phase_operations,{entries};cbn[flat_map bank_process bank_plan];rewrite HT.',
            f'cbn[{plan} eval_bank_plan flat_map app].',
            f'change([WriteLane (Z.div(eval_expr driven {row["offset"]})32) {value}]=[WriteLane address {value}]).']
        offset=rtl.Parser(row['offset']).complete()
        if row['index']['rule'] in ('multiply_index','multiply_index_left'):
            scale=offset.args[3] if row['index']['rule']=='multiply_index' else offset.args[2]
            lines += [f'rewrite({row["index"]["rule"]} driven {offset.args[0].name}%nat {row["index"]["index"]} {rtl.render(scale)} ltac:(clear;lia) ltac:(reflexivity) eq_refl).']
        else:lines+=['rewrite shifted_index.']
        lines += [f'change([WriteLane (norm {f["width"]}(read_signal driven {f["root"]})) {value}]=[WriteLane address {value}]).',
                  'now rewrite HA. Qed.',f'Print Assumptions write_{n}_actual_destination.']
        sampled=f'(phase_driven_state {p} ev pre)'
        lines += [f'Theorem write_{n}_actual_phase ev pre seed code instruction address rest:',
            f'let driven:={sampled} in',
            f'changed_signal ev<>{root}%nat ->CombLFP {p} seed driven ->',
            f'PathHolds driven {f["original"]} {f["name"]}_choices ->',
            f'norm 32(read_signal driven {f["source"]})=norm 32 code ->',
            'Decode.decode Decode.RV32I code=Decode.IInstruction instruction ->',
            'destination_registers instruction=address::rest ->',
            f'process_matches_states pre driven {proc}=true ->',
            f'read_signal(PhaseSemantics {p} ev pre){root}=',
            f'apply_updates_root_value {root}(read_signal pre {root})',
            f' (operation_updates {root} 32 [WriteLane address {value}]).',
            'Proof. cbv zeta;intros HE HL HP HW HD HS HT.',
            f'pose proof(write_{n}_actual_destination pre {sampled} seed code instruction address rest HL HP HW HD HS HT)as HO.',
            f'exact(eq_trans(bank_phase_updates {p} {root}%nat {row["total"]}%nat {entries}',
            f' bank_{root}_certificate ev pre HE)',
            f' (f_equal(fun ops=>apply_updates_root_value {root}(read_signal pre {root})(operation_updates {root} 32 ops))HO)). Qed.',
            f'Print Assumptions write_{n}_actual_phase.']
        lines += [f'Section RegisterPreservation{n}.',
            'Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}',
            ' {word_ok:word.ok word}{registers_ok:map.ok Registers}.',
            f'Theorem write_{n}_register_preservation {{Token:Type}} (token_pc token_word:Token->Z)',
            ' token ev pre seed (before after:FormalSpec.State) instruction address:',
            f'let driven:={sampled} in',
            f'changed_signal ev<>{root}%nat ->CombLFP {p} seed driven ->',
            f'PathHolds driven {f["original"]} {f["name"]}_choices ->',
            f'norm 32(read_signal driven {f["source"]})=norm 32(token_word token) ->',
            'Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction instruction ->',
            'destination_registers instruction=[address] ->',
            f'process_matches_states pre driven {proc}=true ->',
            'instruction_effect token_pc token_word token before=Some after ->',
            f'(address<>0%Z ->ISAView after address=norm 32 {value}) ->',
            f'RegisterRelated(lane_read 32(read_signal pre {root}))before ->',
            f'RegisterRelated(lane_read 32(read_signal(PhaseSemantics {p} ev pre){root}))after.',
            'Proof. cbv zeta;intros HE HL HP HW HD HS HT HX HV HR.',
            f'pose proof(write_{n}_actual_destination pre {sampled} seed (token_word token)',
            ' instruction address [] HL HP HW HD HS HT)as HO.',
            f'apply(actual_phase_register_transport {p} {root}%nat {row["total"]}%nat',
            f' {entries} bank_{root}_certificate ev pre before after HE HR).',
            'rewrite HO;apply single_write_projected_effects;[exact HV|].',
            'intros index HB HN.',
            'apply(original_token_frame token_pc token_word token before after instruction index HX HD HB).',
            'rewrite HS;cbn;intros[H|H];[apply HN;symmetry;exact H|exact H]. Qed.',
            f'End RegisterPreservation{n}.',
            f'Print Assumptions write_{n}_register_preservation.']
    source='\n'.join(lines)+'\n';file=out/'WriteDestination.v';file.write_text(source)
    flags=list(rtl.framework.FLAGS)
    for r in paths:flags+=['-R',r['directory'],r['namespace']]
    for folder,namespace in [(out,'GeneratedWriteDestination'),(field_provider,'GeneratedInstructionFields'),
            (isa_provider,'GeneratedISADestinations'),(bank_provider,'GeneratedBank'),
            (out/'destination','GeneratedDestinationFields')]:
        flags+=['-R',str(Path(folder).resolve()),namespace]
    start=time.monotonic()
    c,t=run_stage([str(rtl.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest())
    if c.returncode==0:
        import cpu_operand_reference_requirements as references
        closed=references.audit('\nSOURCE_REFERENCE_AUDIT\n'+c.stdout,len(rows),closed=2*len(rows))
        k,t=run_stage([str(rtl.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedWriteDestination.WriteDestination'],out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,original_assumptions_only=closed,
                      conditional_register_preservation_checked=closed and k.returncode==0,
                      accepted=closed and k.returncode==0)
    report['seconds']=time.monotonic()-start
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for arg in ['ast','ast-module','field-provider','isa-provider','bank-provider','output']:p.add_argument('--'+arg,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.field_provider,a.isa_provider,a.bank_provider,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
