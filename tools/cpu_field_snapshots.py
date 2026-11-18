"""Bundle unconditional real LFP field equations at one registered word.

The ISA word identity and phase convergence remain separate obligations.
Sequential sampled fields, guards and mux origins are not silently bypassed.
"""
from __future__ import annotations
import argparse,hashlib,json,time
from pathlib import Path
import cpu_auto_adapter as adapter
import cpu_auto_pipeline as pipeline
import cpu_instruction_fields as fields
import cpu_instruction_word_aliases as aliases
from cpu_certificate_acceptance import run_stage


def plan(profile):
    ast,fr,outputs,_,_,_=fields.proposal(profile)
    _,wr,chains,_,_=aliases.proposal(profile)
    origin={row['source']:row for row in chains};groups={};residuals=[*fr,*wr]
    for row in outputs:
        if row['kind']!='Combinational' or row['path']:
            residuals.append(dict(root=row['root'],reason='not an unconditional combinational field'));continue
        chain=origin.get(row['source'])
        if not chain or chain['boundary']!='sequential_carrier':
            residuals.append(dict(root=row['root'],reason='source does not resolve through checked aliases to a sequential carrier'));continue
        carrier=chain['terminal'];writers=[(i,p)for i,p in enumerate(ast['processes'])if carrier in p['writers']]
        if len(writers)!=1 or writers[0][1]['kind']!='Sequential':raise ValueError('inconsistent carrier registration proposal')
        group=groups.setdefault(carrier,dict(carrier=carrier,process=writers[0][1]['name'],
            process_index=writers[0][0],bindings=[]))
        group['bindings'].append(row)
    for group in groups.values():
        if len({b['root']for b in group['bindings']})!=len(group['bindings']):
            raise ValueError('ambiguous output field binding')
    return ast,dict(groups=[groups[k]for k in sorted(groups)],residuals=residuals,
        current_isa_identity_proved=False,operand_freshness_proved=False)


def render(profile,fields_module='GeneratedInstructionFields.InstructionFields',
           aliases_module='GeneratedInstructionWordAliases.InstructionWordAliases'):
    if not all(adapter.SYMBOL.fullmatch(m)for m in (fields_module,aliases_module)):
        raise ValueError('closed provider module symbols required')
    ast,data=plan(profile);program=profile['ast']['program']
    imports=[profile['ast']['module'],*profile['ast'].get('program_imports',[])]
    lines=['From Coq Require Import List ZArith Bool.',
        'Require Import Lang.ExtendedSV Ex.External.CPUInstructionFields Ex.External.CPUInstructionFieldSnapshot '+
        ' '.join([*imports,fields_module,aliases_module])+'.',
        'Import ListNotations ExtendedSV CPUInstructionFields CPUInstructionFieldSnapshot.',
        'Module F := '+fields_module+'.','Module W := '+aliases_module+'.']
    for group in data['groups']:
        carrier=group['carrier'];proc=ast['module']+'.'+group['process'];bindings=group['bindings']
        values=['(Build_Binding '+str(b['root'])+'%nat '+str(b['width'])+'%nat '+b['field']+')'for b in bindings]
        lines += [f'Definition bindings_{carrier} : list Binding := ['+';'.join(values)+'].',
            f'Lemma carrier_{carrier}_registered : nth_error(processes {program}) {group["process_index"]}%nat=Some {proc} /\\',
            f' process_kind {proc}=Sequential /\\ existsb(Nat.eqb {carrier}%nat)(stmt_writers(process_body {proc}))=true.',
            'Proof. split;[reflexivity|]. split;[reflexivity|vm_compute;reflexivity]. Qed.',
            f'Theorem snapshot_{carrier} seed fixed : CombLFP {program} seed fixed ->Snapshot {carrier}%nat bindings_{carrier} fixed.',
            f'Proof. intro HL. unfold Snapshot,Decoded,bindings_{carrier}.']
        for binding in bindings:
            lines += [' constructor;[exact(eq_trans (F.'+binding['name']+'_actual seed fixed HL I)',
                '     (W.source_'+str(binding['source'])+'_field_origin seed fixed '+binding['field']+' HL))|].']
        lines += [' constructor. Qed.',
            f'Theorem snapshot_{carrier}_with_word seed fixed code : CombLFP {program} seed fixed ->',
            f' norm 32(read_signal fixed {carrier}%nat)=norm 32 code ->Decoded code bindings_{carrier} fixed.',
            f'Proof. intros HL HW. exact(snapshot_with_word {carrier}%nat bindings_{carrier} fixed code',
            f' (snapshot_{carrier} seed fixed HL) HW). Qed.',
            f'Print Assumptions carrier_{carrier}_registered.',f'Print Assumptions snapshot_{carrier}.',
            f'Print Assumptions snapshot_{carrier}_with_word.']
    return ast,data,'\n'.join(lines)+'\n'


def validate_provider(profile,directory,kind):
    directory=Path(directory)
    if kind=='fields':
        ast,_,_,source,_,_=fields.proposal(profile);name='InstructionFields'
    elif kind=='aliases':
        ast,_,_,source,_=aliases.proposal(profile);name='InstructionWordAliases'
    else:raise ValueError('unknown snapshot provider kind')
    report=json.loads((directory/'report.json').read_text());path=directory/(name+'.v')
    if not(report.get('accepted')is True and report.get('assumptions_closed')is True
        and report.get('coqchk_exit')==0 and report['ast_sha256']==ast['source_sha256']
        and path.read_text()==source and path.with_suffix('.vo').is_file()
        and report['source_sha256']==hashlib.sha256(source.encode()).hexdigest()):
        raise ValueError('exact checked current AST '+kind+' provider required')
    return dict(source_sha256=report['source_sha256'],object_sha256=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest())


def check(profile,field_provider,alias_provider,output,analyze_only=False):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    ast,data,source=render(profile)
    result=dict(accepted=False,ast_sha256=ast['source_sha256'],actual_program=profile['ast']['program'],
        **data,proof_started=False,analysis_only=analyze_only,carrier_is_current_isa_word=False,
        global_invariant_synthesized=False,itree_refinement_proved=False,llm_calls=0)
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    if not data['groups']:result['status']='no_supported_comb_snapshot'
    elif not analyze_only:
        result['field_provider']=validate_provider(profile,field_provider,'fields')
        result['alias_provider']=validate_provider(profile,alias_provider,'aliases')
        path=output/'FieldSnapshots.v';path.write_text(source)
        flags=list(pipeline.adapter.framework.FLAGS)
        for row in profile.get('coq_load_paths',[]):flags+=['-R',row['directory'],row['namespace']]
        flags+=['-R',str(Path(field_provider).resolve()),'GeneratedInstructionFields',
                '-R',str(Path(alias_provider).resolve()),'GeneratedInstructionWordAliases',
                '-R',str(output.resolve()),'GeneratedFieldSnapshots']
        result.update(source_sha256=hashlib.sha256(source.encode()).hexdigest(),proof_started=True)
        start=time.monotonic();deadline=start+1200
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',1200)
        result.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
        if c.returncode==0:
            ok,axioms=pipeline.audit_shared_output(source,c.stdout);result.update(assumptions_accepted=ok,assumptions=axioms)
            if ok and time.monotonic()<deadline:
                ks=time.monotonic();k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                    'GeneratedFieldSnapshots.FieldSnapshots'],output/'coqchk.log',deadline-ks)
                result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,accepted=k.returncode==0)
        result['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--fields',type=Path);p.add_argument('--aliases',type=Path)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--analyze-only',action='store_true');a=p.parse_args()
    result=check(json.loads(a.profile.read_text()),a.fields,a.aliases,a.output,a.analyze_only)
    print(json.dumps({k:v for k,v in result.items()if k not in ('groups','residuals')},indent=2))
    raise SystemExit(0 if a.analyze_only or result['accepted']else 1)
