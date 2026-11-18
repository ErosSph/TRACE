"""Compile complete RF RHS expressions to checked abstract-register views.

The expression contexts and guards remain intact. Coq checks every replacement
using BankRelated; this is not a proof of operand freshness or retirement age.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import time
import cpu_auto_adapter as adapter
import cpu_bank_adapter as banks
import cpu_bank_reads as reads
import cpu_rf_read_ports as ports
from cpu_certificate_acceptance import run_stage


def lower(term, root, total):
    """Return expression and explicit compositional proof, not a tactic search."""
    a, name = term.args, term.name
    original = adapter.render(term)
    if name == 'ESel' and a[0].name == '32' and a[1].name == 'EVar':
        width, signal = map(lambda x:int(x.name),a[1].args)
        if signal == root:
            if width != total or not banks.bounded32(a[2]):
                raise ValueError('bank slice is not a checked bounded 32-bit lane')
            offset = adapter.render(a[2])
            expr = f'(EConst 32 (view (Z.div (eval_expr s {offset}) 32)))'
            proof = f'(bank_read_equivalent {root}%nat {total}%nat {offset} ltac:(lia) eq_refl s view HR)'
            return expr, proof
    if name in ('EConst','EVar'):
        if name == 'EVar' and int(a[1].name) == root:
            raise ValueError('raw bank reference was not abstracted')
        return original, f'(value_refl s {original})'
    signatures = {
        'ESel':('select_equivalent',1,2),
        'EConcat':('concat_equivalent',1,2),
        'EReplicate':('replicate_equivalent',2),
        'EExtend':('extend_equivalent',2),
        'EUnary':('unary_equivalent',2),
        'EBinary':('binary_equivalent',2,3),
        'ECond':('cond_equivalent',1,2,3)}
    if name not in signatures:
        raise ValueError('unsupported expression context '+name)
    theorem,*indices=signatures[name]
    children = {i:lower(a[i],root,total) for i in indices}
    prefix = [adapter.render(x) for x in a[:indices[0]]]
    expression = '('+' '.join([name,*prefix,*[children[i][0] for i in indices]])+')'
    args = ['s',*prefix]
    for i in indices:
        args += [adapter.render(a[i]),children[i][0]]
    args += [children[i][1] for i in indices]
    return expression,'('+' '.join([theorem,*args])+')'


def render(profile):
    library=Path(profile['rf_port_library'])
    if library.is_absolute() or '..' in library.parts or library.suffix!='.v':
        raise ValueError('expected relative project RF source')
    logical='.'.join(library.relative_to('src').with_suffix('').parts)
    if not adapter.SYMBOL.fullmatch(logical):raise ValueError('invalid RF library')
    ports.emit_library(profile,adapter.ROOT/library,check=True)
    ast=adapter.load_ast(adapter.ROOT/profile['ast']['file'])
    analysis=ports.analyze(ast)
    raw=reads.analyze(ast)
    roots={site['root']:site['total'] for site in raw['sites']}
    if analysis['residuals'] or len(roots)!=1:
        raise ValueError('requires complete supported reads of one physical bank')
    root,total=next(iter(roots.items()))
    rf, program=library.stem, profile['ast']['program']
    lines=['(** Generated complete RHS register-view transport; not freshness. *)',
        'From Coq Require Import ZArith Lia.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankReadExpression',
        ' Ex.External.CPURegisterEffectRelation Ex.External.CPURegisterReadExpression',
        ' Ex.RvCore.FormalSpec coqutil.Map.Interface coqutil.Word.Interface coqutil.Byte',
        f' {logical} ' + ' '.join([profile['ast']['module'],*profile['ast'].get('program_imports',[])])+'.',
        'Import ExtendedSV ExtendedSVRegisterBank ExtendedSVBankReadExpression',
        ' CPURegisterEffectRelation CPURegisterReadExpression.']
    for n,port in enumerate(analysis['ports']):
        name=f'port_{n}'
        expression,proof=lower(port['rhs'],root,total)
        w,out=port['width'],port['output_root']
        lines += [f'Definition {name}_view_rhs (s:State) (view:Z->Z) : Expr := {expression}.',
            f'Lemma {name}_rhs_equivalent s view',
            f' (HR:BankRelated 32 32 (read_signal s {root}%nat) view) :',
            f' ValueEquivalent s {rf}.{name}_rhs ({name}_view_rhs s view).',
            f'Proof. exact {proof}. Qed.',
            f'Theorem {name}_lfp_view seed fixed view : CombLFP {program} seed fixed ->',
            f' BankRelated 32 32 (read_signal fixed {root}%nat) view ->',
            f' norm {w} (read_signal fixed {out}%nat)=norm {w}(eval_expr fixed ({name}_view_rhs fixed view)).',
            'Proof.',
            f' intros HL HR;rewrite ({rf}.{name}_lfp seed fixed HL).',
            f' now rewrite (proj2 ({name}_rhs_equivalent fixed view HR)).',
            'Qed.',
            'Section ISA_'+str(n)+'.',
            'Context {word:Interface.word 32}{Registers:map.map Z word}{Mem:map.map word byte}.',
            f'Theorem {name}_original_isa_view seed fixed (isa:FormalSpec.State) :',
            f' CombLFP {program} seed fixed ->',
            f' RegisterRelated (lane_read 32 (read_signal fixed {root}%nat)) isa ->',
            f' norm {w} (read_signal fixed {out}%nat)=norm {w}(eval_expr fixed',
            f' ({name}_view_rhs fixed (PhysicalZeroISAView (read_signal fixed {root}%nat) isa))).',
            'Proof.',
            f' intros HL HR;exact ({name}_lfp_view seed fixed _ HL',
            '   (register_related_physical_view _ isa HR)).',
            'Qed.',
            f'Theorem {name}_original_isa_view_zero seed fixed (isa:FormalSpec.State) :',
            f' CombLFP {program} seed fixed ->',
            f' RegisterRelated (lane_read 32 (read_signal fixed {root}%nat)) isa ->',
            f' lane_read 32 (read_signal fixed {root}%nat) 0=0%Z ->',
            f' norm {w} (read_signal fixed {out}%nat)=norm {w}(eval_expr fixed',
            f' ({name}_view_rhs fixed (ISAView isa))).',
            'Proof.',
            f' intros HL HR Hzero;exact ({name}_lfp_view seed fixed _ HL',
            '   (register_related_zero_view _ isa HR Hzero)).',
            'Qed.',
            'End ISA_'+str(n)+'.']
    audits=[f'port_{n}_{suffix}' for n in range(len(analysis['ports']))
        for suffix in ['rhs_equivalent','lfp_view','original_isa_view','original_isa_view_zero']]
    for n,theorem in enumerate(audits):
        lines += [f'Goal True. idtac "RF_PORT_ASSUMPTIONS_{n}". exact I. Qed.',
            f'Print Assumptions {theorem}.']
    return '\n'.join(lines)+'\n',analysis


def check_profile(profile,output,timeout=1200):
    output=Path(output)
    if output.exists():raise ValueError('output must be fresh')
    source,analysis=render(profile)
    output.mkdir(parents=True)
    path=output/'AutoRFViewExpression.v';path.write_text(source)
    flags=list(adapter.framework.FLAGS)
    for extra in profile.get('coq_load_paths',[]):
        flags+=['-R',extra['directory'],extra['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedRFViewExpression']
    report={'accepted':False,'ports':len(analysis['ports']),'llm_calls':0,
        'generated_source_sha256':hashlib.sha256(source.encode()).hexdigest(),
        'physical_lane_zero_retained':True,'operand_freshness_proved':False,
        'global_invariant_synthesized':False}
    started=time.monotonic()
    compiled,timed=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q','-time',*flags,
        str(path.resolve())],output/'coqc.log',timeout)
    report.update(coqc_exit=compiled.returncode,coqc_timed_out=timed,coqc_seconds=time.monotonic()-started)
    if compiled.returncode==0:
        audited=ports.audit_output(compiled.stdout,4*len(analysis['ports']))
        started=time.monotonic()
        checked,timed=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,
            '-norec','GeneratedRFViewExpression.AutoRFViewExpression'],output/'coqchk.log',timeout)
        report.update(coqchk_exit=checked.returncode,coqchk_timed_out=timed,
            coqchk_seconds=time.monotonic()-started,assumptions_accepted=audited)
        report['accepted']=bool(analysis['ports']) and audited and checked.returncode==0
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',type=Path,required=True)
    destination=parser.add_mutually_exclusive_group(required=True)
    destination.add_argument('--output',type=Path)
    destination.add_argument('--emit-source',type=Path)
    parser.add_argument('--check-source',action='store_true')
    parser.add_argument('--timeout',type=float,default=1200)
    args=parser.parse_args()
    if not 0<args.timeout<=1200:parser.error('timeout must be in (0,1200] seconds')
    profile=json.loads(args.profile.read_text())
    if args.emit_source:
        print(json.dumps(emit_library(profile,args.emit_source,args.check_source),indent=2))
        return 0
    if args.check_source:parser.error('--check-source requires --emit-source')
    report=check_profile(profile,args.output,args.timeout)
    print(json.dumps(report,indent=2))
    return 0 if report['accepted'] else 1


def emit_library(profile,destination,check=False):
    source,analysis=render(profile)
    if not analysis['ports'] or analysis['residuals']:
        raise ValueError('persistent view source requires complete supported ports')
    destination=Path(destination)
    if check:
        if not destination.is_file() or destination.read_text()!=source:
            raise ValueError('persistent view source differs from AST generation')
    elif destination.exists():raise ValueError('destination exists; use --check-source')
    else:
        destination.parent.mkdir(parents=True,exist_ok=True)
        destination.write_text(source)
    return dict(source=str(destination),source_matches_generator=True,coq_checked=False,
        generated_source_sha256=hashlib.sha256(source.encode()).hexdigest())


if __name__=='__main__':raise SystemExit(main())
