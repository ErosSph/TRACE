"""Bind raw RTL data to an explicitly declared runtime configuration.

Only a closed Program record is extracted. CPU theorem parameters are never
used; data/phase/initialization equality to the named target is kernel checked.
The original AST and its negative results are not overwritten.
"""
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_pending_origins as origin
from cpu_certificate_acceptance import run_stage
ROOT=origin.ROOT;rtl=origin.pending.rtl
PROGRAM=re.compile(r'Definition\s+(\w+)\s*:\s*Program\s*:=\s*\{\|([\s\S]*?)\|\}\s*\.')


def configuration_data(source,raw_program):
    modules=re.findall(r'^Module\s+(\w+)\.',source,re.M);records=list(PROGRAM.finditer(source))
    if len(modules)!=1 or len(records)!=1:raise ValueError('one module and one closed runtime Program record required')
    fields={}
    for row in records[0].group(2).split(';'):
        match=re.fullmatch(r'\s*(\w+)\s*:=\s*(.*?)\s*',row,re.S)
        if match is None or match[1]in fields:raise ValueError('closed distinct configuration fields required')
        fields[match[1]]=' '.join(match[2].split())
    if set(fields)!={'signal_count','processes','statement_fuel','lfp_fuel'}:raise ValueError('exact original Program fields required')
    allowed={raw_program,raw_program.rsplit('.',1)[-1]}
    for key in['signal_count','processes','statement_fuel']:
        match=re.fullmatch(key+r'\s+([A-Za-z_][A-Za-z_0-9.]*)',fields[key])
        if match is None or match[1]not in allowed:raise ValueError('configuration may not replace RTL processes, signal count or statement fuel')
    if not re.fullmatch(r'\d+',fields['lfp_fuel']):raise ValueError('runtime iteration budget must be explicit natural data')
    return dict(module=modules[0],definition=records[0][1],lfp_fuel=int(fields['lfp_fuel']),
        preserved_fields=['signal_count','processes','statement_fuel'])


def configured_source(source,raw_module,config):
    records=list(PROGRAM.finditer(source))
    if len(records)!=1:raise ValueError('unique raw Program record required')
    prefix=source[:records[0].end()]
    if re.search(r'^\s*(Theorem|Lemma|Example|Axiom|Parameter|Hypothesis|Goal|Proof|Admitted)\b',prefix,re.M):
        raise ValueError('configured AST copies data only, not an earlier CPU proof')
    if len(re.findall(r'^Module\s+',prefix,re.M))!=1:raise ValueError('one generated AST data module required')
    digest=hashlib.sha256(json.dumps(config,sort_keys=True).encode()).hexdigest()[:10]
    module=raw_module+'Configured'+digest
    prefix,count=re.subn(r'(?m)^Module '+re.escape(raw_module)+r'\.', 'Module '+module+'.',prefix)
    if count!=1:raise ValueError('raw AST module mismatch')
    prefix,count=re.subn(r'\blfp_fuel\s*:=\s*\d+',lambda _: 'lfp_fuel := '+str(config['lfp_fuel']),prefix)
    if count!=1:raise ValueError('one raw iteration-budget field required')
    return module,prefix+'\nEnd '+module+'.\n'


def proposal(ast_path,ast_module,config_path,config_module):
    if not rtl.SYMBOL.fullmatch(config_module):raise ValueError('closed configuration module symbol required')
    ast,profile,paths=origin.raw_binding(ast_path,ast_module)
    original=Path(ast_path).read_text();config_text=Path(config_path).read_text()
    config=configuration_data(config_text,profile['ast']['program'])
    module,configured=configured_source(original,ast['module'],config)
    program_name=profile['ast']['program'].rsplit('.',1)[-1];program=module+'.'+program_name
    target=config['module']+'.'+config['definition'];old=profile['ast']['program'];fuel=config['lfp_fuel']
    data=dict(raw_ast_sha256=ast['source_sha256'],configuration_source_sha256=hashlib.sha256(config_text.encode()).hexdigest(),
        configuration=config,raw_program=old,configured_program=program,target_program=target,
        ast_module='GeneratedRuntimeInput.ConfiguredAST',coq_load_paths=paths,
        configured_source_sha256=hashlib.sha256(configured.encode()).hexdigest(),
        old_inv_read=False,old_pending_read=False,configuration_proof_text_consumed=False,
        old_cpu_theorems_used_as_premises=False,legacy_target_module_imported_for_data_comparison=True,
        iteration_budget_from_declared_target=True,raw_program_modified=False,
        global_inv_proved=False,itree_refinement_proved=False)
    lines=['From Coq Require Import List.',
        f'Require Import Lang.ExtendedSV {ast_module} {config_module} GeneratedRuntimeInput.ConfiguredAST.',
        'Import ExtendedSV.',
        f'Definition declared_runtime:Program:={{|signal_count:=signal_count {old};processes:=processes {old};',
        f' statement_fuel:=statement_fuel {old};lfp_fuel:={fuel}|}}.',
        f'Theorem configured_eq_declared:{program}=declared_runtime.',
        'Proof. vm_compute;reflexivity. Qed.',
        f'Theorem configured_eq_original_target:{program}={target}.',
        'Proof. vm_compute;reflexivity. Qed.',
        f'Theorem processes_unchanged:processes {program}=processes {old}.',
        'Proof. rewrite configured_eq_declared;reflexivity. Qed.',
        f'Theorem statement_fuel_unchanged:statement_fuel {program}=statement_fuel {old}.',
        'Proof. rewrite configured_eq_declared;reflexivity. Qed.',
        f'Theorem signal_count_unchanged:signal_count {program}=signal_count {old}.',
        'Proof. rewrite configured_eq_declared;reflexivity. Qed.',
        f'Theorem actual_phase_is_original_target ev pre:PhaseSemantics {program} ev pre=PhaseSemantics {target} ev pre.',
        'Proof. rewrite configured_eq_original_target;reflexivity. Qed.',
        f'Theorem actual_initialization_is_original_target seed:initialize {program} seed=initialize {target} seed.',
        'Proof. rewrite configured_eq_original_target;reflexivity. Qed.']
    exports=['configured_eq_declared','configured_eq_original_target','processes_unchanged','statement_fuel_unchanged',
        'signal_count_unchanged','actual_phase_is_original_target','actual_initialization_is_original_target']
    lines+=['Print Assumptions '+name+'.'for name in exports]
    return data,configured,'\n'.join(lines)+'\n'


def missing_ast_path(log):
    match=re.search(r'Cannot load ([A-Za-z_][A-Za-z_0-9.]*):\s*no physical path bound to ([A-Za-z_][A-Za-z_0-9.]*)',log)
    if match is None:return None
    module=match[1];name=module.rsplit('.',1)[-1]
    if not name.endswith('AST')or'.'not in module:return None
    files=[]
    for root in[ROOT/'experiments/framework/generated',ROOT/'src/Ex/Generated']:
        files+=list(root.rglob(name+'.v'))
    if len(files)!=1:return None
    return dict(module=module,directory=str(files[0].parent.resolve()),namespace=module.rsplit('.',1)[0])


def check(ast_path,ast_module,config_path,config_module,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    data,source,binding=proposal(ast_path,ast_module,config_path,config_module)
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    ast=output/'ConfiguredAST.v';ast.write_text(source);proof=output/'ConfigBinding.v';proof.write_text(binding)
    flags=list(rtl.framework.FLAGS)
    for path in data['coq_load_paths']:flags+=['-R',path['directory'],path['namespace']]
    config=Path(config_path).resolve()
    if not config.is_relative_to(ROOT/'src'):flags+=['-R',str(config.parent),config_module.rsplit('.',1)[0]]
    flags+=['-R',str(output.resolve()),'GeneratedRuntimeInput'];start=time.monotonic();deadline=start+timeout
    report=dict(accepted=False,scope='data/actual phase/initialization equal original declared configuration; no LFP/INV/ISA claim',
        old_inv_read=False,old_pending_read=False,old_cpu_theorems_used_as_premises=False,
        legacy_target_module_imported_for_data_comparison=True,configured_iteration_budget=data['configuration']['lfp_fuel'],
        source_sha256=data['configured_source_sha256'],binding_source_sha256=hashlib.sha256(binding.encode()).hexdigest(),
        raw_program_modified=False,configuration_binding_proved=False,runtime_lfp_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    for name,path,exports in [('ConfiguredAST',ast,0),('ConfigBinding',proof,7)]:
        remaining=deadline-time.monotonic()
        if remaining<=0:report['residual']='cumulative native point budget exhausted';break
        attempts=[];repairs=[]
        while True:
            label=name+(''if not attempts else'.retry'+str(len(attempts)))
            c,t=run_stage([str(ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/(label+'.coqc.log'),deadline-time.monotonic())
            attempts.append(dict(log=label+'.coqc.log',coqc_exit=c.returncode,coqc_timed_out=t))
            fix=missing_ast_path(c.stdout+'\n'+c.stderr)if c.returncode!=0 and not t else None
            if fix is None or fix in repairs or time.monotonic()>=deadline:break
            repairs.append(fix);flags+=['-R',fix['directory'],fix['namespace']]
        item=dict(coqc_exit=c.returncode,coqc_timed_out=t,attempts=attempts,data_load_path_repairs=repairs);report[name]=item
        if c.returncode!=0:break
        closed=exports==0 or(c.stdout.count('Closed under the global context')==exports and'Axioms:'not in c.stdout)
        item['assumptions_closed']=closed
        if not closed or time.monotonic()>=deadline:break
        k,t=run_stage([str(ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedRuntimeInput.'+name],output/(name+'.coqchk.log'),deadline-time.monotonic())
        item.update(coqchk_exit=k.returncode,coqchk_timed_out=t)
        if k.returncode!=0:break
        item['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
        if exports:report.update(accepted=True,configuration_binding_proved=True)
    report['raw_source_unchanged']=hashlib.sha256(Path(ast_path).read_bytes()).hexdigest()==data['raw_ast_sha256']
    report['accepted']=report['accepted']and report['raw_source_unchanged'];report['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in['ast','config','output']:p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--ast-module',required=True);p.add_argument('--config-module',required=True);a=p.parse_args()
    report=check(a.ast,a.ast_module,a.config,a.config_module,a.output);print(json.dumps(report,indent=2));raise SystemExit(0 if report['accepted']else 1)
