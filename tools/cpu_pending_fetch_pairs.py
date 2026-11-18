"""Infer and check PC/instruction capture pairs against an actual RTL ROM port.

Same-process 32-bit peers alone are NOT PC bindings. A supported pair needs
the same capture guards and a real alias path to the ROM read's address.
Original ISA address/image correspondence remains a separate obligation.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_readonly_inputs as rom
import cpu_scalar_expression_paths as paths
from cpu_certificate_acceptance import run_stage

origin=rom.origin;rtl=origin.pending.rtl


def paired_leaf(word,peer,choices):
    for yes in choices:
        if word.name!=peer.name or word.name!='ECond'or word.args[0].name!=peer.args[0].name or word.args[1]!=peer.args[1]:return None
        word=word.args[2 if yes else 3];peer=peer.args[2 if yes else 3]
    return peer


def discover(ast):
    plan=origin.pending.analyze(ast);readers={row['source']:row for row in rom.discover(ast)}
    scalar={row['root']:row for row in plan['scalar_transitions']};pairs=[];residuals=[]
    for slot in plan['slots']:
        word=rtl.Parser(slot['capture']['next_expression']).complete();candidates=[]
        for choices,leaf in paths.leaf_paths(word,32):
            if leaf.name!='EVar'or leaf.args[0].name!='32':continue
            reader=readers.get(int(leaf.args[1].name))
            if reader is None or len(reader['address_dependencies'])!=1:continue
            address=reader['address_dependencies'][0];address_chain=rom.aliases.trace(ast,address)
            for peer in slot['pc_candidates']:
                expr=rtl.Parser(scalar[peer]['next_expression']).complete();value=paired_leaf(word,expr,choices)
                if value is None or value.name!='EVar'or value.args[0].name!='32':continue
                source=int(value.args[1].name)
                if source==peer:continue
                pc_chain=rom.aliases.trace(ast,source)
                if pc_chain['terminal']!=address_chain['terminal']:continue
                candidates.append(dict(carrier=slot['carrier'],pc_root=peer,pc_input=source,
                    word_input=reader['source'],capture_path=list(choices),process=slot['capture']['process'],
                    address_root=address,pc_alias_chain=pc_chain,address_alias_chain=address_chain,reader=reader))
        if len(candidates)==1:pairs+=candidates
        else:residuals.append(dict(carrier=slot['carrier'],reason='no unique capture-address pair at a supported ROM',candidates=candidates))
    return dict(pairs=pairs,residuals=residuals,old_inv_read=False,old_pending_read=False,
        original_isa_address_correspondence_proved=False,global_inv_proved=False,itree_refinement_proved=False)


def alias_term(chain,ports,seed='seed',fixed='fixed',hl='HL'):
    result='eq_refl'
    for edge in reversed(chain['edges']):
        step=f'(eq_trans(port_{ports[edge["root"]]}_lfp {seed} {fixed} {hl})(norm_idempotent 32(read_signal {fixed} {edge["parent"]})))'
        result=f'(eq_trans {step} {result})'
    return result


def render(ast_path,ast_module,selected=None):
    ast,profile,loadpaths=origin.raw_binding(ast_path,ast_module);data=discover(ast)
    if selected is not None:
        actual={f'slot_{row["carrier"]}.pc':f'root_{row["pc_root"]}'for row in data['pairs']}
        if not selected or any(role not in actual or ident!=actual[role]for role,ident in selected.items()):
            raise ValueError('selected PC has no raw-RTL capture-address derivation')
        data['pairs']=[row for row in data['pairs']if f'slot_{row["carrier"]}.pc'in selected]
        data['selected_bindings']=selected
    if not data['pairs']:raise ValueError('no supported unique ROM capture pair')
    chains=[chain for row in data['pairs']for chain in(row['pc_alias_chain'],row['address_alias_chain'],row['reader']['alias_chain'])]
    roots=sorted({edge['root']for chain in chains for edge in chain['edges']}|{row['reader']['terminal']for row in data['pairs']})
    _,comb,prefix=rom.comb.proposal(profile,roots)
    if comb['residuals']:raise ValueError('actual combination port residual')
    ports={row['output_root']:i for i,row in enumerate(comb['ports'])};count=len(comb['ports'])
    selected=sorted({r for row in data['pairs']for r in(row['carrier'],row['pc_root'])})
    _,remaining,outputs,source,audits=origin.expressions.proposal(profile,selected)
    if remaining:raise ValueError('actual scalar certificate residual')
    count+=audits;program=profile['ast']['program'];lines=[
        'Require Import Lang.ExtendedSVExpressionPath Lang.ExtendedSVWordInvariant.',
        'Import ExtendedSVExpressionPath ExtendedSVWordInvariant.',f'Local Opaque {program}.']
    for index,row in enumerate(data['pairs']):
        stem=f'fetch_pair_{index}';w=row['carrier'];pc=row['pc_root'];wi=row['word_input'];pi=row['pc_input'];addr=row['address_root']
        bits='['+';'.join('true'if x else'false'for x in row['capture_path'])+']'
        lines += [f'Definition {stem}_choices:list bool:={bits}.',
            f'Lemma {stem}_guards s: PathHolds s root_{w}_expression {stem}_choices ->',
            f' PathHolds s root_{pc}_expression {stem}_choices.',
            'Proof. exact(fun H=>H). Qed.']
        for root,input in[(w,wi),(pc,pi)]:
            lines += [f'Lemma {stem}_{root}_path:expression_path 32 root_{root}_expression {stem}_choices=Some(EVar 32 {input}).',
                'Proof. vm_compute. reflexivity. Qed.']
        lines += [f'Theorem {stem}_sampled_pc seed fixed:CombLFP {program} seed fixed ->',
            f' norm 32(read_signal fixed {pi})=norm 32(read_signal fixed {addr}).',
            f'Proof. intro HL. exact(eq_trans {alias_term(row["pc_alias_chain"],ports)}',
            f' (eq_sym {alias_term(row["address_alias_chain"],ports)})). Qed.']
        wordterm=f'(port_{ports[row["reader"]["terminal"]]}_lfp seed fixed HL)'
        for edge in reversed(row['reader']['alias_chain']['edges']):
            step=f'(eq_trans(port_{ports[edge["root"]]}_lfp seed fixed HL)(norm_idempotent 32(read_signal fixed {edge["parent"]})))'
            wordterm=f'(eq_trans {step} {wordterm})'
        reader_port=ports[row['reader']['terminal']]
        lines += [f'Theorem {stem}_sampled_word seed fixed:CombLFP {program} seed fixed ->',
            f' norm 32(read_signal fixed {wi})=norm 32(eval_expr fixed port_{reader_port}_rhs).',
            f'Proof. intro HL. exact {wordterm}. Qed.']
        proc=ast['module']+'.'+row['process'];frame=f'(phase_driven_state {program} ev pre)'
        lines += [f'Theorem {stem}_actual_phase ev pre seed:',
            f' changed_signal ev<>{w}%nat ->changed_signal ev<>{pc}%nat ->',
            f' process_matches_states pre {frame} {proc}=true ->',
            f' PathHolds {frame} root_{w}_expression {stem}_choices ->',
            f' CombLFP {program} seed {frame} ->',
            f' norm 32(read_signal(PhaseSemantics {program} ev pre){pc})=norm 32(read_signal {frame} {addr}) /\\',
            f' norm 32(read_signal(PhaseSemantics {program} ev pre){w})=norm 32(eval_expr {frame} port_{reader_port}_rhs).',
            'Proof. intros HEw HEpc HS HP HL. split.',
            f' - rewrite(root_{pc}_expression_phase ev pre HEpc),HS.',
            f'   pose proof(selected_expression_sound 32 {stem}_choices root_{pc}_expression(EVar 32 {pi})',
            f'    {frame} {stem}_{pc}_path({stem}_guards {frame} HP))as HC.',
            f'   cbn[eval_expr]in HC. rewrite norm_idempotent in HC.',
            f'   exact(eq_trans HC({stem}_sampled_pc seed {frame} HL)).',
            f' - rewrite(root_{w}_expression_phase ev pre HEw),HS.',
            f'   pose proof(selected_expression_sound 32 {stem}_choices root_{w}_expression(EVar 32 {wi})',
            f'    {frame} {stem}_{w}_path HP)as HC.',
            f'   cbn[eval_expr]in HC. rewrite norm_idempotent in HC.',
            f'   exact(eq_trans HC({stem}_sampled_word seed {frame} HL)). Qed.']
        for suffix in['guards','sampled_pc','sampled_word','actual_phase']:
            lines.append(f'Print Assumptions {stem}_{suffix}.');count+=1
    return dict(**data,ast_sha256=ast['source_sha256'],coq_load_paths=loadpaths,audited_exports=count),prefix+'\n'+source+'\n'+'\n'.join(lines)+'\n'


def check(ast_path,ast_module,output,timeout=1200,selected=None):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    data,source=render(ast_path,ast_module,selected);output=Path(output);output.mkdir(parents=True,exist_ok=False)
    path=output/'FetchPairs.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedFetchPairs'];start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report=dict(accepted=False,scope='actual phase jointly captures original RTL ROM word and its address',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        ast_sha256=data['ast_sha256'],pair_count=len(data['pairs']),old_inv_read=False,old_pending_read=False,
        original_isa_address_correspondence_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    if selected is not None:report['selected_bindings']=selected
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout
        report['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedFetchPairs.FetchPairs'],
                output/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True)
    p.add_argument('--ast-module',required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
