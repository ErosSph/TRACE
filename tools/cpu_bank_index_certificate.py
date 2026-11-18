"""Exact lane-index expressions for raw physical bank writes, not ownership."""
import argparse, hashlib, json, time
from pathlib import Path
import cpu_write_ownership_frontier as ownership
from cpu_certificate_acceptance import run_stage
rtl = ownership.rtl


def recognize(text):
    term = rtl.Parser(text).complete()
    literal = ownership.bank.literal(term)
    if literal is not None:
        if literal % 32 or not 0 <= literal // 32 < 32:
            return None
        return dict(index=f'(EConst 5 {literal//32})', rule='constant')
    if term.name == 'EBinary' and term.args[1].name == 'BMul' and int(term.args[0].name) >= 10:
        a, b = term.args[2:]
        if ownership.bank.literal(b) == 32 and int(a.args[0].name) <= 5:
            return dict(index=rtl.render(a), rule='multiply_index')
        if ownership.bank.literal(a) == 32 and int(b.args[0].name) <= 5:
            return dict(index=rtl.render(b), rule='multiply_index_left')
    # Exact structural shape used by packed-array frontends; no CPU IDs.
    if term.name == 'ESel' and term.args[0].name == '10' and rtl.render(term.args[2]) == '(EConst 32 0)':
        inner = term.args[1]
        if inner.name == 'EBinary' and inner.args[0].name == '32' and inner.args[1].name == 'BShiftL' and rtl.render(inner.args[3]) == '(EConst 32 5)':
            arg = inner.args[2]
            if arg.name == 'EExtend' and arg.args[0].name == '32' and arg.args[1].name == 'false':
                value = arg.args[2]
                if value.name == 'EVar' and value.args[0].name == '5':
                    return dict(index=rtl.render(value), rule='shifted_index')
    return None


def check(ast_path, ast_module, output):
    ast, profile, paths = ownership.origin.raw_binding(ast_path, ast_module)
    plan = ownership.analyze(ast)
    out = Path(output); out.mkdir(parents=True, exist_ok=False)
    rows, residuals = [], []
    for site in plan['writes']:
        if site['offset'] is None:
            residuals.append(dict(process=site['process'], path=site['path'], reason='whole-bank write has no single index'))
            continue
        match = recognize(site['offset'])
        if match is None:
            residuals.append(dict(process=site['process'], path=site['path'], reason='unsupported exact index encoding'))
            continue
        rows.append(dict(process=site['process'], path=site['path'], offset=site['offset'], **match))
    lines = ['From Coq Require Import ZArith Lia.',
             'Require Import Lang.ExtendedSV Lang.ExtendedSVBankIndex.',
             'Import ExtendedSV ExtendedSVBankIndex.']
    for i, row in enumerate(rows):
        lines += [f'Theorem write_{i}_index s: Z.div (eval_expr s {row["offset"]}) 32=eval_expr s {row["index"]}.', 'Proof.']
        if row['rule'] == 'constant':
            lines += ['vm_compute;reflexivity.']
        elif row['rule'] == 'shifted_index':
            lines += ['apply shifted_index.']
        else:
            lines += [f'apply {row["rule"]};[simpl;lia|simpl;lia|reflexivity].']
        lines += ['Qed.', f'Print Assumptions write_{i}_index.']
    source = '\n'.join(lines)+'\n'; file = out/'BankIndices.v'; file.write_text(source)
    report = dict(accepted=False, exact_indices=len(rows), rows=rows, residuals=residuals,
        ast_sha256=ast['source_sha256'], old_inv_read=False, token_ownership_proved=False,
        actual_selected_write_proved=False, complete_R_generated=False,
        source_sha256=hashlib.sha256(source.encode()).hexdigest())
    if rows:
        flags=list(rtl.framework.FLAGS)+['-R',str(out.resolve()),'GeneratedBankIndices']
        start=time.monotonic()
        c,t=run_stage([str(rtl.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t)
        if c.returncode == 0:
            closed=c.stdout.count('Closed under the global context')==len(rows) and 'Axioms:' not in c.stdout
            k,t=run_stage([str(rtl.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedBankIndices.BankIndices'],out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,accepted=closed and k.returncode==0)
        report['seconds']=time.monotonic()-start
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for arg in ['ast','ast-module','output']:parser.add_argument('--'+arg,required=True)
    a=parser.parse_args(); result=check(a.ast,a.ast_module,a.output)
    print(json.dumps({k:v for k,v in result.items()if k!='rows'},indent=2))
    raise SystemExit(0 if result['accepted']else 1)
