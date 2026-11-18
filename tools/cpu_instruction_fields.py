"""Discover and prove RV32 field-layout bindings from actual AST expressions.

Source-word candidates are structural only: the generated equalities do not
prove that this word is the current ISA instruction, a retirement, or a fresh
operand. Native and explicit unsigned-32-bit field extraction are supported.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import time
import cpu_auto_adapter as adapter
import cpu_comb_scalar_bindings as comb
import cpu_scalar_expression_paths as paths
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage

LAYOUT={(5,7):'Rd',(5,15):'Rs1',(5,20):'Rs2',(7,0):'Opcode',
    (3,12):'Funct3',(7,25):'Funct7'}


def match_field(e,output_width):
    shape='native'
    if e.name=='EExtend' and e.args[0].name=='32' and e.args[1].name=='false':
        shape='widened';e=e.args[2]
    if e.name!='ESel':return None
    width,word,offset=e.args
    if word.name!='EVar' or word.args[0].name!='32' or offset.name!='EConst' or offset.args[0].name!='5':return None
    key=int(width.name),int(offset.args[1].name)%32
    if key not in LAYOUT:return None
    expected=32 if shape=='widened' else key[0]
    if output_width!=expected:return None
    return dict(field=LAYOUT[key],source=int(word.args[1].name),shape=shape)


def discover(ast):
    selected={'Combinational':set(),'Sequential':set()}
    for proc in ast['processes']:
        if proc['kind'] not in selected:continue
        for st in adapter.walk(proc['body']):
            if st.name!='SAssign' or st.args[2].name!='LVar':continue
            nba,rhs,lhs=st.args
            if nba.name!=('true' if proc['kind']=='Sequential' else 'false'):continue
            width,root=map(lambda x:int(x.name),lhs.args)
            for _,leaf in paths.leaf_paths(rhs,width):
                if match_field(leaf,width):selected[proc['kind']].add(root)
    return {kind:sorted(roots) for kind,roots in selected.items()}


def proposal(profile):
    ast=adapter.load_ast(adapter.ROOT/profile['ast']['file'])
    selected=discover(ast);residuals=[];exports=[];prefix=[];count=0
    comb_analysis={'ports':[]};seq_outputs=[]
    if selected['Combinational']:
        _,comb_analysis,source=comb.proposal(profile,selected['Combinational'])
        residuals+=comb_analysis['residuals']
        prefix.append(re.sub(r'RF_PORT_ASSUMPTIONS_(\d+)',
            lambda m:'AUTO_ADAPTER_ASSUMPTIONS_'+str(int(m.group(1))),source))
        count=source.count('Print Assumptions ')
    if selected['Sequential']:
        _,remaining,seq_outputs,source,audits=paths.proposal(profile,selected['Sequential'])
        residuals+=remaining
        offset=count
        prefix.append(re.sub(r'AUTO_ADAPTER_ASSUMPTIONS_(\d+)',
            lambda m:'AUTO_ADAPTER_ASSUMPTIONS_'+str(offset+int(m.group(1))),source))
        count+=audits
    lines=['Require Import Ex.External.CPUInstructionFields Lang.ExtendedSVExpressionPath.',
        'Import CPUInstructionFields ExtendedSVExpressionPath.']
    program=profile['ast']['program']
    candidates=[]
    for index,item in enumerate(comb_analysis['ports']):
        for path_index,(path,leaf) in enumerate(paths.leaf_paths(item['rhs'],item['width'])):
            field=match_field(leaf,item['width'])
            if field:
                candidates.append(dict(kind='Combinational',root=item['output_root'],width=item['width'],
                    path=list(path),leaf=leaf,original=f'port_{index}_rhs',base=f'port_{index}_lfp',
                    name=f'comb_root_{item["output_root"]}_path_{path_index}',**field))
    for item in seq_outputs:
        leaf=adapter.Parser(item['leaf']).complete();field=match_field(leaf,item['width'])
        if field:
            candidates.append(dict(kind='Sequential',root=item['root'],width=item['width'],
                path=item['path'],leaf=leaf,original=f'root_{item["root"]}_expression',
                base=item['theorem'],name='seq_'+item['theorem'][:-len('_phase')],**field))
    _,_,expressions,_,_=paths.expressions.proposal(profile,selected['Sequential']) if selected['Sequential'] else (None,None,[],None,None)
    procs={x['root']:x['process'] for x in expressions}
    for item in candidates:
        name,width,root=item['name'],item['width'],item['root']
        source,field=item['source'],item['field']
        bits='['+'; '.join('true' if b else 'false' for b in item['path'])+']'
        lines += [f'Definition {name}_choices : list bool := {bits}.',
            f'Definition {name}_leaf : Expr := {adapter.render(item["leaf"])}.',
            f'Lemma {name}_layout s : norm {width}%nat (eval_expr s {name}_leaf)=',
            f' field_reference (read_signal s {source}%nat) {field}.',
            f'Proof. exact ({"native" if item["shape"]=="native" else "widened"}_field_reference s {source}%nat {field}). Qed.']
        if item['kind']=='Combinational':
            lines += [f'Lemma {name}_path_checked : expression_path {width}%nat {item["original"]}',
                f' {name}_choices=Some {name}_leaf.',
                'Proof. vm_compute. reflexivity. Qed.',
                f'Theorem {name}_actual seed fixed : CombLFP {program} seed fixed ->',
                f' PathHolds fixed {item["original"]} {name}_choices ->',
                f' norm {width}%nat (read_signal fixed {root}%nat)=',
                f' field_reference (read_signal fixed {source}%nat) {field}.',
                'Proof. intros HL HP.',
                f' exact (eq_trans ({item["base"]} seed fixed HL)',
                f'  (eq_trans (selected_expression_sound {width}%nat {name}_choices',
                f'   {item["original"]} {name}_leaf fixed {name}_path_checked HP) ({name}_layout fixed))). Qed.']
        else:
            base_choices=item['base'][:-len('_phase')]+'_choices'
            lines += ['Local Opaque PhaseSemantics phase_driven_state read_signal.',
                f'Theorem {name}_actual ev pre : changed_signal ev<>{root}%nat ->',
                f' process_matches_states pre (phase_driven_state {program} ev pre)',
                f' {ast["module"]}.{procs[root]}=true ->',
                f' PathHolds (phase_driven_state {program} ev pre) {item["original"]} {base_choices} ->',
                f' norm {width}%nat (read_signal (PhaseSemantics {program} ev pre) {root}%nat)=',
                f' field_reference (read_signal (phase_driven_state {program} ev pre) {source}%nat) {field}.',
                'Proof. intros HE HS HP.',
                f' exact (eq_trans ({item["base"]} ev pre HE HS HP)',
                f'  ({name}_layout (phase_driven_state {program} ev pre))). Qed.']
        for suffix in ['layout','actual']:
            lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
                f'Print Assumptions {name}_{suffix}.']
            count+=1
        exports.append({k:v for k,v in item.items() if k!='leaf'})
    return ast,residuals,exports,'\n'.join(prefix+['\n'.join(lines)])+'\n',count,selected


def emit_library(profile,destination,check=False):
    _,residuals,exports,source,count,_=proposal(profile)
    if residuals or not exports:raise ValueError('unsupported instruction field selection')
    path=Path(destination)
    if check:
        if not path.is_file() or path.read_text()!=source:
            raise ValueError('persistent instruction field source differs from generation')
    elif path.exists():raise ValueError('destination exists; use --check-source')
    else:
        path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
    return dict(source=str(path),source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        fields=len(exports),audited_exports=count,source_matches_generator=True,coq_checked=False,
        current_isa_token_identity_proved=False)


def check_profile(profile,output,timeout=1200):
    output=Path(output)
    if output.exists():raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    ast,residuals,exports,source,count,selected=proposal(profile)
    file=output/'InstructionFields.v';file.write_text(source)
    groups={}
    for item in exports:
        key=(item['kind'],item['source'])
        groups.setdefault(key,set()).add(item['field'])
    report=dict(accepted=False,ast_sha256=ast['source_sha256'],
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),actual_program=profile['ast']['program'],
        outputs=exports,selected_roots=selected,residuals=residuals,audited_exports=count,llm_calls=0,
        source_groups=[dict(kind=k[0],source=k[1],fields=sorted(v),
            missing_register_fields=sorted({'Rd','Rs1','Rs2'}-v)) for k,v in groups.items()],
        current_isa_token_identity_proved=False,operand_freshness_proved=False,
        instruction_semantic_roles_proved=False,
        role_interpretation='RV32 fixed bit positions only; Rd does not assert that the instruction writes a destination register.',
        global_invariant_synthesized=False)
    if residuals or not exports:report['status']='unsupported_instruction_field_selection'
    else:
        flags=list(adapter.framework.FLAGS)
        for extra in profile.get('coq_load_paths',[]):flags+=['-R',extra['directory'],extra['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedInstructionFields']
        start=time.monotonic()
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(file.resolve())],output/'coqc.log',timeout)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
        if c.returncode==0:
            report['assumptions_closed']=scalar.audit_output(c.stdout,count)
            start=time.monotonic()
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedInstructionFields.InstructionFields'],output/'coqchk.log',timeout)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-start)
            report['accepted']=report['assumptions_closed'] and k.returncode==0
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile',type=Path,required=True)
    mode=p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--output',type=Path);mode.add_argument('--emit-source',type=Path)
    mode.add_argument('--check-source',type=Path)
    p.add_argument('--timeout',type=float,default=1200);a=p.parse_args()
    if not 0<a.timeout<=1200:p.error('timeout must be positive and at most1200 seconds')
    profile=json.loads(a.profile.read_text())
    if a.emit_source or a.check_source:
        print(json.dumps(emit_library(profile,a.emit_source or a.check_source,
            check=bool(a.check_source)),indent=2));return 0
    r=check_profile(profile,a.output,a.timeout)
    print(json.dumps(r,indent=2));return 0 if r['accepted'] else 1


if __name__=='__main__':raise SystemExit(main())
