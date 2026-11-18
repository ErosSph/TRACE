"""Generate exact RF restoration conditions from complete raw bank writers.

No CPU names or old invariant theorems are inputs. Checking the generated
equivalence is NOT discharging its left-hand-side condition.
"""
import argparse
import hashlib
import json
import re
import time
from pathlib import Path
import cpu_write_ownership_frontier as ownership
from cpu_certificate_acceptance import run_stage
bank=ownership.bank
rtl=ownership.rtl


def audit(log, count):
    chunks=re.split(r'^BANK_REQUIREMENT_AUDIT\s*$',log,flags=re.M)
    ok,_=bank.audit_bank_output(chunks[0],count)
    return ok and len(chunks)==count+1 and all(
        x.count('Closed under the global context')==2 and 'Axioms:'not in x
        for x in chunks[1:])


class Compiler:
    def __init__(self):
        self.lines=[]
        self.memo={}

    def compile(self, plan):
        key=rtl.render(plan)
        if key in self.memo:return self.memo[key]
        n,a=plan.name,plan.args
        if n=='BPEmpty':wp,proof='empty','empty_correct'
        elif n in ('BPWord','BPReset'):
            args=' '.join(rtl.render(x) for x in a)
            stem='word' if n=='BPWord' else 'reset'
            wp=stem+' '+args;proof=stem+'_correct '+args
        elif n=='BPIf':
            y,no=self.compile(a[1]),self.compile(a[2]);g=rtl.render(a[0])
            wp=f'branch {g} {y} {no}'
            proof=f'branch_correct {g} _ _ _ _ {y}_correct {no}_correct'
        elif n=='BPSeq':
            children=[self.compile(x) for x in a[0].args]
            wp='sequence ['+';'.join(children)+']'
            proof='list_nil_correct'
            for child in reversed(children):
                proof=f'(list_cons_correct _ _ _ _ {child}_correct {proof})'
            proof='sequence_correct _ _ '+proof
        else:raise ValueError('unsupported bank plan '+n)
        name='bank_wp_'+str(len(self.memo));self.memo[key]=name
        self.lines += [f'Definition {name}:WP:={wp}.',
                       f'Lemma {name}_correct:Correct {key} {name}.',
                       f'Proof. exact({proof}). Qed.']
        return name


def render(ast, binding, analysis):
    compiler=Compiler();entries=[]
    for b in analysis['banks']:
        pairs=[];proof='entries_nil_correct'
        compiled=[(p,compiler.compile(bp)) for p,_,bp in b['plans']]
        for p,wp in compiled:pairs.append(f'({ast["module"]}.{p["name"]},{wp})')
        for p,wp in reversed(compiled):
            prefix=f'bank_{b["root"]}_{p["name"]}'
            entry=f'(Build_BankEntry {ast["module"]}.{p["name"]} {prefix}_nb {prefix}_plan)'
            proof=f'(entries_cons_correct {entry} _ _ _ {wp}_correct {proof})'
        entries.append((b,'['+';'.join(pairs)+']',proof))
    lines=[bank.render_bank_adapter(binding,ast,analysis),
           'Require Import Lang.ExtendedSVBankRequirements Ex.External.CPUBankRequirements.',
           'Import ExtendedSVBankRequirements.',*compiler.lines]
    for b,pairs,proof in entries:
        root=b['root'];stem=f'bank_{root}'
        lines += [f'Definition {stem}_requirements:list(Process*WP):={pairs}.',
                  f'Lemma {stem}_requirements_checked:EntriesCorrect {stem}_entries {stem}_requirements.',
                  f'Proof. exact({proof}). Qed.',
                  f'Definition {stem}_restore_exact {{word:Interface.word 32}}',
                  ' {Registers:map.map Z word}{Mem:map.map word byte}:=',
                  f' @actual_requirement_exact word Registers Mem {binding["program"]} {root}%nat',
                  f' {stem}_entries {stem}_requirements {stem}_certificate {stem}_requirements_checked.',
                  'Goal True. idtac "BANK_REQUIREMENT_AUDIT". exact I. Qed.',
                  f'Print Assumptions {stem}_requirements_checked.',
                  f'Print Assumptions {stem}_restore_exact.']
    return '\n'.join(lines)+'\n',len(compiler.memo)


def check(ast_path, ast_module, output, timeout=1200):
    if not 0<timeout<=1200:raise ValueError('budget must be <=1200 seconds')
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    ast,profile,paths=ownership.origin.raw_binding(ast_path,ast_module)
    analysis=bank.analyze(ast)
    report=dict(accepted=False,old_inv_read=False,complete_R_generated=False,
                restoration_conditions_discharged=False,
                residuals=analysis['residuals'],
                banks=[dict(root=b['root'],writers=[p['name'] for p,_,_ in b['plans']])
                       for b in analysis['banks']])
    if not analysis['banks'] or analysis['residuals']:
        report['status']='unsupported_complete_bank'
    else:
        source,nodes=render(ast,profile['ast'],analysis)
        path=out/'BankRequirements.v';path.write_text(source)
        flags=list(rtl.framework.FLAGS)
        for row in paths:flags+=['-R',row['directory'],row['namespace']]
        flags+=['-R',str(out.resolve()),'GeneratedBankRequirements']
        start=time.monotonic();deadline=start+timeout
        c,t=run_stage([str(rtl.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],
                      out/'coqc.log',timeout)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,transformer_nodes=nodes,
                      source_sha256=hashlib.sha256(source.encode()).hexdigest())
        if c.returncode==0 and time.monotonic()<deadline:
            closed=audit(c.stdout,len(analysis['banks']))
            k,t=run_stage([str(rtl.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                           'GeneratedBankRequirements.BankRequirements'],out/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                          assumptions_closed=closed,accepted=closed and k.returncode==0)
        report['seconds']=time.monotonic()-start
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for arg in ['ast','ast-module','output']:parser.add_argument('--'+arg,required=True)
    a=parser.parse_args();r=check(a.ast,a.ast_module,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted'] else 1)
