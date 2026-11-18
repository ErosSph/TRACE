#!/usr/bin/env python3
"""LFP module for designs whose known-bit certificate must avoid the strict `exhaustive` enumeration (case on a wide scrutinee
without default arm, e.g. unrolled `for` loops).  Same output statement as tools/cpu_tmpl_lfpnl.py; the proof uses
Lang.ExtendedSVBitStabilityLazy (Kiter0_l / comb_stable0_l, proved equal to the accepted Kiter0).  generalized_rule.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
"""
import cpu_tmpl_lfpnl as L


def build(design, module, n):
    text, ex = L.build(design, module, n)
    text = text.replace('Lang.ExtendedSVBitStabilityNoLatch Lang.ExtendedSVPhaseLength',
                        'Lang.ExtendedSVBitStabilityNoLatch Lang.ExtendedSVBitStabilityLazy Lang.ExtendedSVPhaseLength', 1)
    text = text.replace('ExtendedSVBitStabilityNoLatch ExtendedSVPhaseLength.', 'ExtendedSVBitStabilityNoLatch ExtendedSVBitStabilityLazy ExtendedSVPhaseLength.', 1)
    a = f'all_known (Kiter0 P {n}) (signal_count P) = true'
    assert a in text
    text = text.replace(a, f'all_known (Kiter0_l P {n}) (signal_count P) = true')
    assert f'apply (comb_stable0_b P {n} cert_ok known_ok)' in text
    text = text.replace(f'apply (comb_stable0_b P {n} cert_ok known_ok)', f'apply (comb_stable0_l P {n} cert_ok known_ok)')
    return text, ex


if __name__ == '__main__':      # additive CLI (route driver)
    import argparse
    from pathlib import Path
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', required=True); ap.add_argument('--module', required=True); ap.add_argument('--rounds', type=int, default=1); ap.add_argument('--out', required=True)
    a = ap.parse_args()
    Path(a.out).write_text(build(a.design, a.module, a.rounds)[0])
