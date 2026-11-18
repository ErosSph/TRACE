"""Certify correlated controller outputs from complete raw blocking ASTs.

Recognize gate:=1; ...; if hazard then {gate:=0; write:=0; ...}; ... .
No CPU name, old invariant or instruction theorem is consulted. Static
non-write tests are repeated as Coq-checked frame certificates.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
import cpu_pending_stall_flush as sf
from cpu_certificate_acceptance import run_stage
origin, rtl = sf.origin, sf.rtl


def sequence(st):
    wrappers = 0
    while st.name == 'SSeq' and len(st.args[0].args) == 1:
        wrappers += 1
        st = st.args[0].args[0]
    return (list(st.args[0].args) if st.name == 'SSeq' else [st]), wrappers


def writes(st):
    return {rtl.root_of(n.args[2]) for n in rtl.walk(st) if n.name == 'SAssign'}


def discover(ast):
    rows = []
    for index, proc in enumerate(ast.get('processes', [])):
        if proc['kind'] != 'Combinational':
            continue
        if any(n.args[0].name != 'false' for n in rtl.walk(proc['body']) if n.name == 'SAssign'):
            continue
        sts, wrappers = sequence(proc['body'])
        for i, st in enumerate(sts):
            if st.name != 'SAssign' or st.args[2].name != 'LVar' or st.args[2].args[0].name != '1':
                continue
            gate = int(st.args[2].args[1].name)
            if not sf.scalar_set(st, 1, gate, 1):
                continue
            for j in range(i + 1, len(sts)):
                branch = sts[j]
                if any(gate in writes(x) for x in sts[i + 1:j]):
                    break
                if branch.name != 'SIf' or branch.args[2].name != 'SSkip':
                    continue
                clear, _ = sequence(branch.args[1])
                if not any(sf.scalar_set(x, 1, gate, 0) for x in clear):
                    continue
                for k, assignment in enumerate(clear):
                    if assignment.name != 'SAssign' or assignment.args[2].name != 'LVar':
                        continue
                    write = int(assignment.args[2].args[1].name)
                    if write == gate or not sf.scalar_set(assignment, 1, write, 0):
                        continue
                    if any(write in writes(x) for x in clear[k + 1:]):
                        continue
                    if any({gate, write} & writes(x) for x in sts[j + 1:]):
                        continue
                    if any({gate, write} & writes(p['body']) for p in ast['processes'][index + 1:] if p['kind'] == 'Combinational'):
                        continue
                    rows.append(dict(process=proc['name'], index=index, gate=gate, write=write,
                        wrappers=wrappers, before=[rtl.render(x) for x in sts[:i]],
                        middle=[rtl.render(x) for x in sts[i + 1:j]],
                        clear_before=[rtl.render(x) for x in clear[:k]],
                        clear_after=[rtl.render(x) for x in clear[k + 1:]],
                        clear=rtl.render(branch.args[1]), guard=rtl.render(branch.args[0]),
                        after=[rtl.render(x) for x in sts[j + 1:]]))
    return rows


def render(ast_path, module):
    ast, profile, paths = origin.raw_binding(ast_path, module)
    rows = discover(ast)
    if not rows:
        raise ValueError('no supported correlated whole-controller pair')
    program = profile['ast']['program']
    lines = ['From Coq Require Import List ZArith Bool.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVAutoAdapterEffects Lang.ExtendedSVBlocking',
        f' Lang.ExtendedSVStallFlush Lang.ExtendedSVGuardedWrite Lang.ExtendedSVCombCut {module}.',
        'Import ListNotations ExtendedSV ExtendedSVAutoAdapterEffects ExtendedSVBlocking',
        ' ExtendedSVStallFlush ExtendedSVGuardedWrite ExtendedSVCombCut.']
    def effects(sts):
        return '[' + ';'.join(rtl.render(rtl.effect_of(rtl.Parser(s).complete())) for s in sts) + ']'
    for n, row in enumerate(rows):
        a, g, w = f'pair_{n}', row['gate'], row['write']
        proc = ast['module'] + '.' + row['process']
        for part in ['before', 'middle', 'clear_before', 'clear_after', 'after']:
            lines += [f'Definition {a}_{part}:list EffectPlan:={effects(row[part])}.',
                f'Definition {a}_{part}_stmt:Stmt:=SSeq[' + ';'.join(row[part]) + '].']
        clear = rtl.render(rtl.effect_of(rtl.Parser(row['clear']).complete()))
        lines += [f'Definition {a}_clear:EffectPlan:={clear}.',
            f'Definition {a}_prefix_code:={a}_before++FAssign false(EConst 1 1)(LVar 1 {g})::{a}_middle.',
            f'Definition {a}_prefix:=FSeq {a}_prefix_code.',
            f'Definition {a}_branch:=FIf {row["guard"]} {a}_clear FEmpty.']
        effect = f'FSeq({a}_prefix_code++{a}_branch::{a}_after)'
        for _ in range(row['wrappers']):
            effect = f'FSeq[{effect}]'
        lines += [f'Definition {a}_effect:EffectPlan:={effect}.',
            f'Lemma {a}_compiled:compile_effect(statement_fuel {program})(process_body {proc})=Some {a}_effect.',
            'Proof. vm_compute;reflexivity. Qed.',
            f'Lemma {a}_blocking:blocking_onlyb(process_body {proc})=true. Proof. vm_compute;reflexivity. Qed.',
            f'Lemma {a}_registered:nth_error(processes {program}){row["index"]}=Some {proc}. Proof. vm_compute;reflexivity. Qed.']
        for part, roots in [('middle', [g]), ('clear_after', [w]), ('after', [g, w])]:
            lines += [f'Lemma {a}_{part}_compiled:compile_effect(statement_fuel {program}){a}_{part}_stmt=Some(FSeq {a}_{part}). Proof. vm_compute;reflexivity. Qed.']
            for root in roots:
                lines += [f'Lemma {a}_{part}_avoids_{root}:existsb(Nat.eqb {root})(stmt_writers {a}_{part}_stmt)=false. Proof. vm_compute;reflexivity. Qed.',
                    f'Lemma {a}_{part}_frame_{root} es:read_signal(blocking_state(eval_effect(FSeq {a}_{part})es)){root}=read_signal(blocking_state es){root}.',
                    f'Proof. exact(checked_effect_frame _ _ _ _ {a}_{part}_compiled {a}_{part}_avoids_{root} es). Qed.']
        for root in [g, w]:
            lines += [f'Lemma {a}_suffix_{root}:avoids_root {root}(filter is_comb(skipn(S {row["index"]})(processes {program})))=true. Proof. vm_compute;reflexivity. Qed.']
        lines += [f'Local Opaque {program} {a}_before {a}_middle {a}_clear_before {a}_clear_after {a}_after.',
            f'Lemma {a}_prefix_one es:norm 1(read_signal(blocking_state(eval_effect {a}_prefix es)){g})=1%Z.',
            f'Proof. unfold {a}_prefix,{a}_prefix_code. rewrite(effect_seq_sandwich {a}_before {a}_middle),{a}_middle_frame_{g}.',
            f' change(norm 1(read_signal(scalar_write 1 {g} 1(blocking_state(eval_effect(FSeq {a}_before)es))){g})=1%Z).',
            ' rewrite scalar_write_same;reflexivity. Qed.',
            f'Lemma {a}_clear_zero es:norm 1(read_signal(blocking_state(eval_effect {a}_clear es)){w})=0%Z.',
            f'Proof. change(norm 1(read_signal(blocking_state(eval_effect(FSeq({a}_clear_before++FAssign false(EConst 1 0)(LVar 1 {w})::{a}_clear_after))es)){w})=0%Z).',
            f' rewrite(effect_seq_sandwich {a}_clear_before {a}_clear_after),{a}_clear_after_frame_{w}.',
            f' change(norm 1(read_signal(scalar_write 1 {w} 0(blocking_state(eval_effect(FSeq {a}_clear_before)es))){w})=0%Z).',
            ' rewrite scalar_write_same;reflexivity. Qed.',
            f'Local Opaque {a}_prefix_code {a}_branch.',
            f'Lemma {a}_split es:eval_effect {a}_effect es=eval_effect(FSeq[{a}_prefix;{a}_branch;FSeq {a}_after])es.',
            f'Proof. unfold {a}_effect. repeat rewrite sequence_single. unfold {a}_prefix. exact(sequence_group {a}_prefix_code {a}_branch {a}_after es). Qed.',
            f'Theorem {a}_process s:norm 1(read_signal(run_process {program} s {proc}){w})<>0%Z ->norm 1(read_signal(run_process {program} s {proc}){g})<>0%Z.',
            f'Proof. rewrite(blocking_run_process _ _ _ {a}_blocking),(compile_effect_sound _ _ _ _ {a}_compiled),{a}_split.',
            f' apply safe_implies_enabled. exact(guarded_clear _ _ _ _ _ _ {a}_prefix_one {a}_clear_zero {a}_after_frame_{g} {a}_after_frame_{w} _). Qed.',
            f'Theorem {a}_actual_lfp seed fixed:CombLFP {program} seed fixed ->norm 1(read_signal fixed {w})<>0%Z ->norm 1(read_signal fixed {g})<>0%Z.',
            f'Proof. exact(actual_lfp_relation {program} {row["index"]} {proc} {g} {w} (fun x y=>norm 1 y<>0%Z ->norm 1 x<>0%Z)',
            f' {a}_registered eq_refl {a}_suffix_{g} {a}_suffix_{w} {a}_process seed fixed). Qed.',
            f'Print Assumptions {a}_process. Print Assumptions {a}_actual_lfp.',
            f'Local Transparent {program}.']
    return '\n'.join(lines)+'\n', dict(pairs=rows, coq_load_paths=paths, ast_sha256=ast['source_sha256'])


def check(ast_path, module, output):
    out = Path(output); out.mkdir(parents=True, exist_ok=False)
    source, data = render(ast_path, module)
    path = out/'GuardedWrite.v'; path.write_text(source)
    (out/'plan.json').write_text(json.dumps(data, indent=2)+'\n')
    flags = list(rtl.framework.FLAGS)
    for b in data['coq_load_paths']: flags += ['-R', b['directory'], b['namespace']]
    flags += ['-R', str(out.resolve()), 'GeneratedGuardedWrite']
    start = time.monotonic(); deadline = start+1200
    c, t = run_stage([str(origin.ROOT/'_opam/bin/coqc'), '-time', *flags, str(path.resolve())], out/'coqc.log', 1200)
    report = dict(accepted=False, coqc_exit=c.returncode, coqc_timed_out=t,
        old_inv_read=False, complete_R_generated=False, pairs=len(data['pairs']),
        source_sha256=hashlib.sha256(source.encode()).hexdigest(), ast_sha256=data['ast_sha256'])
    if c.returncode == 0:
        closed = c.stdout.count('Closed under the global context') == 2*len(data['pairs']) and 'Axioms:' not in c.stdout
        report['assumptions_closed'] = closed
        if closed and time.monotonic() < deadline:
            k, t = run_stage([str(origin.ROOT/'_opam/bin/coqchk'), '-silent', *flags, '-norec', 'GeneratedGuardedWrite.GuardedWrite'], out/'coqchk.log', deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode, coqchk_timed_out=t, accepted=k.returncode == 0)
    report['seconds'] = time.monotonic()-start
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ['ast', 'ast-module', 'output']: parser.add_argument('--'+key, required=True)
    args = parser.parse_args()
    result = check(args.ast, args.ast_module, args.output)
    print(json.dumps(result, indent=2)); raise SystemExit(0 if result['accepted'] else 1)
