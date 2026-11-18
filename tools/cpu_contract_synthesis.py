#!/usr/bin/env python3
"""Assemble dependent contract obligations from trusted local evidence profiles.

Global invariants and semantic proofs are REUSED, not inferred or synthesized.
The kernel checks every generated obligation against the selected runtime fields.
"""
import argparse
import json
from pathlib import Path

APIS = {
    'cycle': ('CPUDesignContract', 'DesignContract', 'cpu_',
              ['state', 'cycle', 'commits', 'reset', 'boot', 'isa_initial', 'joint', 'wait_rank'],
              ['startup_checked', 'initial_checked', 'cycle_checked', 'progress_checked'],
              'design_contract_infinite_refinement'),
    'boundary': ('CPUCommitBoundaryContract', 'BoundaryContract', 'boundary_',
                 ['state', 'step', 'commits', 'reset', 'boot', 'isa_initial', 'cut'],
                 ['startup_checked', 'initial_checked', 'segment_checked'],
                 'boundary_contract_infinite_refinement'),
}


def render(profile):
    module, typ, prefix, fields, obligations, lift = APIS[profile['api']]
    if set(profile['fields']) != set(fields):
        raise ValueError('profile must bind every runtime field exactly once')
    if set(profile['evidence']) != set(obligations):
        raise ValueError('profile must supply every dependent proof obligation')
    if profile.get('evidence_origin') != 'existing_hand_proved_global_evidence':
        raise ValueError('evidence provenance must be explicit')
    imports = list(dict.fromkeys(profile['imports'] +
        ['Ex.External.' + m.split('.')[0] for m in profile.get('open_modules', [])]))
    lines = ['(** Automatically assembled; global semantic evidence is reused. *)',
             'From Coq Require Import ZArith List Lia.',
             'From ITree Require Import ITree ITreeFacts.',
             'Require Import Ex.External.CPUDesignContract Ex.External.CPUCommitBoundaryContract',
             ' ' + ' '.join(imports) + '.',
             'Import ' + module + ' ' + ' '.join(profile.get('open_modules', [])) + '.',
             'Local Open Scope itree_scope.',
             'Module GeneratedContract.',
             f"Definition assembled {profile['binders']} : {typ}.", 'Proof.', ' refine {|']
    entries = [f" {prefix}{f} := {profile['fields'][f]}" for f in fields]
    entries += [f' {prefix}{f} := _' for f in obligations]
    lines.append(';\n'.join(entries) + ' |}.')
    for obligation in obligations:
        lines.append(' - ' + profile['evidence'][obligation])
    lines += ['Defined.', 'Local Opaque assembled.',
              f"Definition infinite_refinement {profile['binders']} :=",
              f" {lift} (assembled {' '.join(profile['arguments'])}).",
              'End GeneratedContract.']
    if profile.get('print_assumptions', True):
        lines.extend(['Print Assumptions GeneratedContract.assembled.',
                      'Print Assumptions GeneratedContract.infinite_refinement.'])
    lines.append('')
    return '\n'.join(lines)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    source = render(json.loads(a.profile.read_text()))
    with a.output.open('x') as out:
        out.write(source)


if __name__ == '__main__':
    main()
