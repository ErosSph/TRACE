"""Compile actual guarded RF readers to checked projected-register contracts.

Branch-local zero demands are explicit. Recognized hardware x0 bypasses discharge
them without assuming physical lane zero is zero. This does not establish age.
"""
from __future__ import annotations
import argparse,hashlib,json,time
from pathlib import Path
import cpu_auto_adapter as a
import cpu_rf_read_ports as ports
import cpu_bank_reads as reads
import cpu_auto_pipeline as pipeline
from cpu_certificate_acceptance import run_stage

def touches(term,root):
    return any(node.name=='EVar'and int(node.args[1].name)==root for node in a.walk(term))

def tree(term,root,total):
    n,x=term.name,term.args
    if n=='ECond'and x[0].name=='32':
        if touches(x[1],root):raise ValueError('guard reads the physical bank')
        return f'(Choose {a.render(x[1])} {tree(x[2],root,total)} {tree(x[3],root,total)})'
    if n=='ESel'and x[0].name=='32'and x[1]==a.Parser(f'EVar {total} {root}').complete():
        if touches(x[2],root):raise ValueError('bank-dependent read address')
        return f'(BankRead {a.render(x[2])})'
    if touches(term,root):raise ValueError('unsupported bank-containing expression')
    if x[0].name!='32':raise ValueError('only complete 32-bit operand expressions supported')
    return f'(Independent {a.render(term)})'

def index_of(offset):
    # These are proposals. Both index identities are checked by public Coq
    # arithmetic lemmas on the actual offset, never accepted from Python.
    candidates=[n for n in a.walk(offset)if n.name in ('EVar','ESel')and n.args[0].name=='5']
    for index in candidates:
        text=a.render(index)
        for template,lemma in (
            (f'EBinary 12 BMul {text} (EConst 12 32)','mul12_index'),
            (f'ESel 10 (EBinary 32 BShiftL (EExtend 32 false {text}) (EConst 32 5)) (EConst 32 0)','shift_low10_index')):
            if a.Parser(template).complete()==offset:return index,lemma
    return None

def bypass(term,root,total):
    if term.name!='ECond'or term.args[0].name!='32':return None
    _,guard,yes,no=term.args;zero=a.Parser('EConst 32 0').complete()
    for bank,other,kind in ((yes,no,'nonzero'),(no,yes,'zero_eq')):
        if other!=zero or bank.name!='ESel'or bank.args[1]!=a.Parser(f'EVar {total} {root}').complete():continue
        found=index_of(bank.args[2])
        if found is None:continue
        index,lemma=found;text=a.render(index)
        shape=f'EUnary 1 URedOr {text}'if kind=='nonzero'else f'EBinary 1 BEq (EConst 5 0) {text}'
        if guard==a.Parser(shape).complete():return dict(kind=kind,index=text,offset=a.render(bank.args[2]),lemma=lemma)
    return None

def render(profile):
    library=Path(profile['rf_port_library'])
    if library.is_absolute()or '..'in library.parts or library.suffix!='.v':raise ValueError('project RF library required')
    logical='.'.join(library.relative_to('src').with_suffix('').parts)
    ports.emit_library(profile,a.ROOT/library,check=True)
    ast=a.load_ast(a.ROOT/profile['ast']['file']);analysis=ports.analyze(ast)
    banks={row['root']:row['total']for row in reads.analyze(ast)['sites']}
    if analysis['residuals']or len(banks)!=1:raise ValueError('complete single-bank readers required')
    root,total=next(iter(banks.items()));rf=library.stem;program=profile['ast']['program']
    lines=['From Coq Require Import ZArith Lia.',
        f'Require Import Lang.ExtendedSV Lang.ExtendedSVRegisterBank Lang.ExtendedSVProjectedRead {logical} '+
          ' '.join([profile['ast']['module'],*profile['ast'].get('program_imports',[])])+'.',
        'Import ExtendedSV ExtendedSVRegisterBank ExtendedSVProjectedRead.']
    rows=[]
    for i,port in enumerate(analysis['ports']):
        if port['width']!=32:raise ValueError('non-32-bit output')
        name=f'port_{i}';parsed=tree(port['rhs'],root,total);mask=bypass(port['rhs'],root,total)
        rows.append(dict(output_root=port['output_root'],process=port['process'],zero_bypass=mask is not None,
                         inferred_bypass=mask,demand_discharge_proposed=mask is not None,demand_discharged=False))
        lines += [f'Definition {name}_tree : ReadTree := {parsed}.',
            f'Lemma {name}_checked : checked {name}_tree=true. Proof. reflexivity. Qed.',
            f'Lemma {name}_source : {rf}.{name}_rhs=original {root}%nat {total}%nat {name}_tree.',
            'Proof. reflexivity. Qed.',
            f'Theorem {name}_projected_lfp seed fixed view : CombLFP {program} seed fixed ->',
            f' ProjectedRelated(lane_read 32(read_signal fixed {root}%nat))view ->',
            f' Demand fixed(read_signal fixed {root}%nat){name}_tree ->',
            f' norm 32(read_signal fixed {port["output_root"]}%nat)=norm 32(evaluate fixed view {name}_tree).',
            f'Proof. exact(checked_lfp_projected {program} {root}%nat {total}%nat {port["output_root"]}%nat',
            f' {rf}.{name}_rhs {name}_tree ltac:(lia) {name}_checked {name}_source {rf}.{name}_lfp seed fixed view). Qed.',
            f'Print Assumptions {name}_projected_lfp.']
        if mask:
            idx,off,kind,lemma=(mask[k]for k in ('index','offset','kind','lemma'))
            index_proof=f'({lemma} {idx} fixed eq_refl)'
            lines += [f'Lemma {name}_domain fixed : Demand fixed(read_signal fixed {root}%nat){name}_tree.',
                f'Proof. exact({kind}_bypass_demand {idx} {off} fixed (read_signal fixed {root}%nat) {index_proof}). Qed.',
                f'Theorem {name}_masked_lane seed fixed : CombLFP {program} seed fixed ->',
                f' norm 32(read_signal fixed {port["output_root"]}%nat)=zeroed_lanes(read_signal fixed {root}%nat)(eval_expr fixed {idx}).',
                'Proof. intro HL. etransitivity.',
                f' - exact({name}_projected_lfp seed fixed _ HL (zeroed_lanes_related _) ({name}_domain fixed)).',
                f' - exact({kind}_bypass_value {idx} {off} fixed (read_signal fixed {root}%nat) {index_proof}).',
                'Qed.',f'Print Assumptions {name}_domain.',f'Print Assumptions {name}_masked_lane.']
    return '\n'.join(lines)+'\n',rows,ast

def check(profile,output,publish=None,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('proof budget must be within 1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:source,rows,ast=render(profile)
    except ValueError as error:
        report=dict(accepted=False,proof_started=False,llm_calls=0,
            residual=dict(id='projected_register_read',reason=str(error)),operand_age_proved=False,
            global_invariant_synthesized=False)
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    path=output/'ProjectedRead.v';extra=['-R',str(output.resolve()),'GeneratedProjectedRead'];logical='GeneratedProjectedRead.ProjectedRead'
    if publish:
        path=(a.ROOT/publish).resolve()
        if not path.is_relative_to(a.ROOT/'src')or path.suffix!='.v':raise ValueError('project source required')
        if path.exists()and path.read_text()!=source:raise ValueError('refuse differing published source')
        path.parent.mkdir(parents=True,exist_ok=True);extra=[]
        logical='Pfv.'+'.'.join(path.relative_to(a.ROOT/'src').with_suffix('').parts)
    path.write_text(source);flags=list(a.framework.FLAGS)
    for entry in profile.get('coq_load_paths',[]):flags+=['-R',entry['directory'],entry['namespace']]
    flags+=extra;start=time.monotonic();deadline=start+timeout
    report=dict(accepted=False,ports=rows,ast_sha256=ast['source_sha256'],
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),source=str(path),logical_library=logical,
        llm_calls=0,operand_age_proved=False,global_invariant_synthesized=False)
    c,t=run_stage([str(a.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        ok,axioms=pipeline.audit_shared_output(source,c.stdout);report.update(assumptions_accepted=ok,assumptions=axioms)
        if ok and time.monotonic()<deadline:
            ks=time.monotonic();k,t=run_stage([str(a.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',logical],output/'coqchk.log',deadline-ks)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:
        report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
        for row in rows:row['demand_discharged']=row['demand_discharge_proposed']
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

def check_isa(profile,provider,output,timeout=1200):
    """Instantiate the SAME checked reads at the original FormalSpec view."""
    if not 0<timeout<=1200:raise ValueError('proof budget must be within 1200 seconds')
    provider=Path(provider);parent=json.loads((provider/'report.json').read_text())
    source,rows,ast=render(profile);path=(a.ROOT/parent['source']).resolve()
    if not(parent.get('accepted')is True and parent.get('coqc_exit')==parent.get('coqchk_exit')==0
            and parent.get('assumptions_accepted')is True and parent.get('assumptions')==[]
            and parent['ast_sha256']==ast['source_sha256']
            and parent['source_sha256']==hashlib.sha256(source.encode()).hexdigest()
            and path.read_text()==source and parent['object_sha256']==hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()):
        raise ValueError('exact checked current projected-read provider required')
    logical=parent['logical_library']
    if not a.SYMBOL.fullmatch(logical):raise ValueError('invalid checked library name')
    root=next(iter({s['root']for s in reads.analyze(a.load_ast(a.ROOT/profile['ast']['file']))['sites']}))
    lines=['From Coq Require Import ZArith.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVRegisterBank Lang.ExtendedSVProjectedRead',
        ' Ex.External.CPURegisterEffectRelation Ex.RvCore.FormalSpec',
        ' coqutil.Word.Interface coqutil.Map.Interface coqutil.Byte '+logical+'.',
        'Import ExtendedSV ExtendedSVRegisterBank ExtendedSVProjectedRead CPURegisterEffectRelation.',
        'Section OriginalISA.',
        'Context {word:Interface.word 32}{Registers:map.map Z word}{Mem:map.map word byte}.']
    program=profile['ast']['program'];audits=[]
    # The provider directly imports the Program, but it does not re-export the
    # AST namespace. Use the original explicit imports again.
    lines[1:1]=['Require Import '+' '.join([profile['ast']['module'],*profile['ast'].get('program_imports',[])])+'.']
    for i,row in enumerate(rows):
        name=f'port_{i}';api=f'{logical}.{name}'
        lines += [f'Theorem {name}_original_isa seed fixed (isa:FormalSpec.State) :',
            f' CombLFP {program} seed fixed ->RegisterRelated(lane_read 32(read_signal fixed {root}%nat))isa ->',
            f' Demand fixed(read_signal fixed {root}%nat){api}_tree ->',
            f' norm 32(read_signal fixed {row["output_root"]}%nat)=norm 32(evaluate fixed(ISAView isa){api}_tree).',
            f'Proof. intros HL HR HD;exact({api}_projected_lfp seed fixed(ISAView isa)HL HR HD). Qed.']
        audits.append(name+'_original_isa')
        if row['demand_discharge_proposed']:
            lines += [f'Theorem {name}_original_isa_bypass seed fixed (isa:FormalSpec.State) :',
                f' CombLFP {program} seed fixed ->RegisterRelated(lane_read 32(read_signal fixed {root}%nat))isa ->',
                f' norm 32(read_signal fixed {row["output_root"]}%nat)=norm 32(evaluate fixed(ISAView isa){api}_tree).',
                f'Proof. intros HL HR;exact({api}_projected_lfp seed fixed(ISAView isa)HL HR({api}_domain fixed)). Qed.']
            audits.append(name+'_original_isa_bypass')
    lines+=['End OriginalISA.']+[f'Print Assumptions {name}.'for name in audits]
    text='\n'.join(lines)+'\n';output=Path(output);output.mkdir(parents=True,exist_ok=False)
    generated=output/'OriginalISA.v';generated.write_text(text)
    flags=list(a.framework.FLAGS)
    for entry in profile.get('coq_load_paths',[]):flags+=['-R',entry['directory'],entry['namespace']]
    if not logical.startswith('Pfv.'):
        flags+=['-R',str(path.parent),logical.rsplit('.',1)[0]]
    flags+=['-R',str(output.resolve()),'GeneratedProjectedISA']
    report=dict(accepted=False,llm_calls=0,port_count=len(rows),audited_exports=len(audits),
        original_formal_spec_used=True,operand_age_proved=False,global_invariant_synthesized=False,
        parent_object_sha256=parent['object_sha256'],source_sha256=hashlib.sha256(text.encode()).hexdigest())
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(a.ROOT/'_opam/bin/coqc'),'-time',*flags,str(generated.resolve())],output/'coqc.log',timeout)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        ok,axioms=pipeline.audit_shared_output(text,c.stdout);report.update(assumptions_accepted=ok,assumptions=axioms)
        if ok and time.monotonic()<deadline:
            ks=time.monotonic();k,t=run_stage([str(a.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedProjectedISA.OriginalISA'],output/'coqchk.log',deadline-ks)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    mode=p.add_mutually_exclusive_group()
    mode.add_argument('--publish-library',type=Path);mode.add_argument('--isa-provider',type=Path)
    x=p.parse_args();profile=json.loads(x.profile.read_text())
    r=check_isa(profile,x.isa_provider,x.output)if x.isa_provider else check(profile,x.output,x.publish_library)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
