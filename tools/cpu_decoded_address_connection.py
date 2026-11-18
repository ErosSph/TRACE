"""Raw-generated actual field updates -> original decoded register operands.

Checked field providers may be reused only if their source is exactly freshly
regenerated from this AST. Decoding the sampled word does not prove token age.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_origins as origin
import cpu_instruction_fields as fields
from cpu_certificate_acceptance import run_stage


def provider_ok(folder,source):
    folder=Path(folder);rp=folder/'report.json';sp=folder/'InstructionFields.v'
    if not rp.is_file()or not sp.is_file():return False
    r=json.loads(rp.read_text())
    return (r.get('accepted')is True and r.get('coqc_exit')==r.get('coqchk_exit')==0
        and r.get('assumptions_closed')is True and sp.read_text()==source
        and r.get('source_sha256')==hashlib.sha256(source.encode()).hexdigest()
        and sp.with_suffix('.vo').is_file())


def render(ast,profile,exports):
    p=profile['ast']['program']
    selected=fields.discover(ast)
    _,_,expressions,_,_=fields.paths.expressions.proposal(profile,selected['Sequential']) if selected['Sequential'] else(None,None,[],None,None)
    procs={x['root']:x['process']for x in expressions}
    lines=['From Coq Require Import ZArith List.',
        'Require Import GeneratedInstructionFields.InstructionFields Ex.External.CPUISADecodeInputs Ex.External.CPUISANormalizedInputs',
        ' Ex.External.CV32E40PReq41Instruction Ex.External.CPUIndexedSource Lang.ExtendedSV Lang.ExtendedSVExpressionPath.',
        'Import ListNotations ExtendedSV ExtendedSVExpressionPath CPUISADecodeInputs CPUISANormalizedInputs CV32E40PReq41Instruction.']
    used=[]
    for item in exports:
        if item['field']not in ('Rs1','Rs2'):continue
        name=item['name'];root=item['root'];src=item['source'];width=item['width']
        extra='first 'if item['field']=='Rs2'else''
        shape='first::address::rest'if extra else'address::rest'
        rule='actual_second_address'if extra else'actual_first_address'
        if item['kind']=='Combinational':
            args='seed fixed';sample='fixed';post='fixed'
            premises=[f'CombLFP {p} seed fixed',f'PathHolds fixed {item["original"]} {name}_choices']
            intro='HL HP';actual=f'{name}_actual seed fixed HL HP'
        else:
            args='ev pre';sample=f'(phase_driven_state {p} ev pre)';post=f'(PhaseSemantics {p} ev pre)'
            choices=item['base'][:-len('_phase')]+'_choices'
            premises=[f'changed_signal ev<>{root}%nat',
                f'process_matches_states pre {sample} {ast["module"]}.{procs[root]}=true',
                f'PathHolds {sample} {item["original"]} {choices}']
            intro='HE HT HP';actual=f'{name}_actual ev pre HE HT HP'
        lines += [f'Theorem {name}_decoded {args} instruction {extra}address rest:',
            ' ->\n'.join(premises)+' ->',
            f'Decode.decode Decode.RV32I(read_signal {sample} {src})=Decode.IInstruction instruction ->',
            f'source_registers instruction={shape} ->',
            f'norm {width}(read_signal {post} {root})=address.',
            f'Proof. intros {intro} HD HS;eapply {rule};[exact({actual})|exact HD|exact HS]. Qed.',
            f'Print Assumptions {name}_decoded.']
        normalized_rule='normalized_second_address'if extra else'normalized_first_address'
        lines += [f'Theorem {name}_token_word {args} code instruction {extra}address rest:',
            ' ->\n'.join(premises)+' ->',
            f'norm 32(read_signal {sample} {src})=norm 32 code ->',
            'Decode.decode Decode.RV32I code=Decode.IInstruction instruction ->',
            f'source_registers instruction={shape} ->',
            f'norm {width}(read_signal {post} {root})=address.',
            f'Proof. intros {intro} HW HD HS;eapply {normalized_rule};[exact({actual})|exact HW|exact HD|exact HS]. Qed.',
            f'Print Assumptions {name}_token_word.']
        position=1 if extra else 0
        lines += [f'Definition {name}_operand_R (observed:State)(instruction:Decode.InstructionI):Prop:=',
            f' IndexedSourceAddress {width} {root} observed instruction {position}%nat.',
            f'Theorem {name}_operand_R_from_token {args} code instruction:',
            ' ->\n'.join(premises)+' ->',
            f'norm 32(read_signal {sample} {src})=norm 32 code ->',
            'Decode.decode Decode.RV32I code=Decode.IInstruction instruction ->',
            f'{name}_operand_R {post} instruction.',
            f'Proof. intros {intro} HW HD;unfold {name}_operand_R,IndexedSourceAddress.',
            'destruct(source_registers instruction)as[|first rest]eqn:HS;[exact I|].']
        if position==1:
            lines += ['destruct rest as[|address rest];[exact I|].',
                f'exact({name}_token_word {args} code instruction first address rest {intro} HW HD HS). Qed.']
        else:
            lines += [f'exact({name}_token_word {args} code instruction first rest {intro} HW HD HS). Qed.']
        lines += [f'Print Assumptions {name}_operand_R_from_token.']
        used.append(item)
    return '\n'.join(lines)+'\n',used


def run(ast_path,ast_module,output,provider=None):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    ast,profile,paths=origin.raw_binding(ast_path,ast_module);profile['coq_load_paths']=paths
    _,res,exports,source,_,_=fields.proposal(profile)
    if res:raise ValueError('field residuals require explicit handling')
    if provider is None:
        provider=output/'fields';r=fields.check_profile(profile,provider)
        if not r['accepted']:raise ValueError('new field provider did not pass')
    if not provider_ok(provider,source):raise ValueError('fresh raw field provider mismatch')
    text,used=render(ast,profile,exports)
    # raw_binding's module spelling is authoritative for the Require.
    text=f'Require Import {ast_module}.\n'+text
    path=output/'DecodedAddresses.v';path.write_text(text)
    flags=list(origin.pending.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    # Bind parent first: a freshly built provider can be nested under output.
    flags+=['-R',str(output.resolve()),'GeneratedDecodedAddresses',
            '-R',str(Path(provider).resolve()),'GeneratedInstructionFields']
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',deadline-time.monotonic())
    report=dict(accepted=False,old_inv_read=False,coqc_exit=c.returncode,coqc_timed_out=t,
        provider=str(provider),source_sha256=hashlib.sha256(text.encode()).hexdigest(),
        decoded_fields=len(used),normalized_history_interfaces=len(used),current_token_identity_proved=False,
        indexed_operand_relations_generated=len(used),source_list_shape_required=False,
        inactive_operand_case='None means ISA does not request this operand; not an invalid hardware slot',
        operand_freshness_proved=False,complete_R_generated=False)
    if c.returncode==0 and used:
        report['assumptions_closed']=c.stdout.count('Closed under the global context')==3*len(used)and'Axioms:'not in c.stdout
        k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedDecodedAddresses.DecodedAddresses'],output/'coqchk.log',max(.1,deadline-time.monotonic()))
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                      accepted=k.returncode==0 and report['assumptions_closed'])
    report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['ast','ast-module','output']:p.add_argument('--'+key,required=True)
    p.add_argument('--provider');a=p.parse_args()
    result=run(a.ast,a.ast_module,a.output,a.provider);print(json.dumps(result,indent=2))
    raise SystemExit(0 if result['accepted']else 1)
