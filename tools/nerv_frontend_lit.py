#!/usr/bin/env python3
"""NERV import front end, literal-index variant (additive; the phase-A tools/nerv_frontend.py and NervAST.v are untouched).

Same pipeline as tools/nerv_frontend.py (x constants -> 0, casez -> if chain, static-trip `while` loops unrolled) with ONE
extra, semantics-preserving step in the unrolling: inside the i-th copy of a loop body every read of the loop counter is
replaced by the literal value the counter has in that iteration (counter = init + i*delta; the body never assigns it, checked),
and constant sub-expressions of the shapes that appear in index arithmetic (`mul`/`muls`/`add`/`sub` of two constants and a
part select `sel(const, const, const)`) are folded.  The counter assignments (`i = i + 1`) stay in the sequence, so the
unrolled statement sequence is still exactly the loop's execution; only the index expressions of the lane reads and lane writes
(`next[i*32 +: 32]`) become literals.  Reason (log 20261104-template-nerv.md): the all-states known-bit certificate
(`ExtendedSVBitStability.slx`) only follows part-select writes whose offset is an `EConst`; with a variable offset the 32-lane
CSR counter arrays stay "unknown" and no combinational-convergence certificate can be produced.
Output: experiments/framework/generated/nerv-lit/NervLitAST.v (module Nerv.NervLitAST).  Equivalence with the phase-A AST is
tested signal-by-signal on every cycle (tools/nerv_lit_equiv.py).  translation_equivalence stays not_mechanized.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
"""
import argparse
import copy
import hashlib
import json
import sys
from pathlib import Path
import xml.etree.ElementTree as ET

sys.path.insert(0, str(Path(__file__).resolve().parent))
import nerv_frontend as NF  # noqa: E402
from cv32e40p_extended_frontend import write_coq  # noqa: E402


def const_node(like, width, value, signed=False):
    n = ET.Element("const", dict(like.attrib))
    n.set("name", f"{width}'{'s' if signed else ''}h{value & ((1 << width) - 1):x}")
    return n


def substitute(node, var, value, width=32):
    """Replace every read varref(var) below `node` by a literal; returns the number of replacements."""
    cnt = 0
    for parent in list(node.iter()):
        for i, c in enumerate(list(parent)):
            if c.tag == "varref" and c.get("name") == var:
                parent[i] = const_node(c, width, value, signed=True)
                cnt += 1
    return cnt


def unroll_literal(root):
    """As NF.unroll_loops, but the counter reads of each body copy become literals."""
    total = subs = 0
    inits = {}          # counter name -> (always-body element, init node) for counters initialised only inside a branch
    while True:
        found = False
        pm = {c: p for p in root.iter() for c in p}
        for parent in list(root.iter()):
            kids = list(parent)
            for idx, w in enumerate(kids):
                if w.tag != "while":
                    continue
                found = True
                parts = list(w)
                cond, body, incr = parts[0], parts[1:-1], parts[-1]
                var = incr[-1].get("name") if incr.tag == "assign" and incr[-1].tag == "varref" else None
                prev = kids[idx - 1] if idx else None
                if (var is None or prev is None or prev.tag != "assign" or prev[-1].tag != "varref"
                        or prev[-1].get("name") != var):
                    raise ValueError(f"loop at {w.get('loc')} lacks an adjacent init of its counter")
                for b in body:
                    for a in b.iter():
                        if a.tag in {"assign", "assigndly"} and a[-1].tag == "varref" and a[-1].get("name") == var:
                            raise ValueError(f"loop body assigns its counter at {a.get('loc')}")
                init = NF._cval(prev[0])
                anc = w
                while anc.tag != "always":
                    anc = pm[anc]
                top = list(anc)[0]
                if parent is not top and var not in inits:
                    z = copy.deepcopy(prev)
                    z[0].set("name", "32'sh0")
                    inits[var] = (top, z)
                n = NF._loop_trip(init, cond, incr, var)
                step_expr = list(incr)[0]
                a, b = list(step_expr)
                c = NF._cval(a if a.tag == "const" else b)
                delta = c if step_expr.tag == "add" else -c
                new = []
                for k in range(n):
                    val = init + k * delta
                    for b_ in body:
                        cp = copy.deepcopy(b_)
                        subs += substitute(cp, var, val)
                        new.append(cp)
                    new.append(copy.deepcopy(incr))
                parent.remove(w)
                for j, e in enumerate(new):
                    parent.insert(idx + j, e)
                total += 1
                break
            if found:
                break
        if not found:
            # Counters that are only assigned inside a branch would be unconditionally "unknown" (latch-like) for the all-states
            # known-bit certificate.  After the substitution nothing reads them, so a leading `var = 0` changes no other signal.
            for var, (top, z) in sorted(inits.items()):
                top.insert(0, z)
            return total, subs, sorted(inits)


def is_const(n):
    return n.tag == "const"


def cval(n):
    return NF._cval(n)


def fold(root, tr):
    """Bottom-up folding of constant index arithmetic. Returns the number of folded nodes."""
    count = 0
    changed = True
    while changed:
        changed = False
        for parent in list(root.iter()):
            for i, c in enumerate(list(parent)):
                kids = list(c)
                if c.tag in {"mul", "muls", "add", "sub"} and len(kids) == 2 and all(is_const(k) for k in kids):
                    a, b = cval(kids[0]), cval(kids[1])
                    v = {"mul": a * b, "muls": a * b, "add": a + b, "sub": a - b}[c.tag]
                elif c.tag == "sel" and len(kids) == 3 and all(is_const(k) for k in kids):
                    v = (cval(kids[0]) >> cval(kids[1])) & ((1 << cval(kids[2])) - 1)
                else:
                    continue
                w = tr.width(c)
                parent[i] = const_node(c, w, v, signed=False)
                count += 1
                changed = True
    return count


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--xml", type=Path, required=True)
    p.add_argument("--top", required=True)
    p.add_argument("--module", required=True)
    p.add_argument("--prefix", required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    pinned = json.loads((args.xml.parent / "report.json").read_text())
    xml_hash = hashlib.sha256(args.xml.read_bytes()).hexdigest()
    if pinned.get("xml_sha256") != xml_hash:
        raise ValueError("XML is not pinned by its original elaboration report")
    for item in pinned.get("source_hashes", []):
        if hashlib.sha256(Path(item["path"]).read_bytes()).hexdigest() != item["sha256"]:
            raise ValueError("source changed since elaboration; regenerate XML")
    root = ET.parse(args.xml).getroot()
    xcount = NF.zero_x_constants(root)
    loops, subs, inits = unroll_literal(root)
    tr = NF.NervTranslator(root, args.top)
    folded = fold(root, tr)
    tr = NF.NervTranslator(root, args.top)       # fresh translator over the folded tree
    sources = []
    for f in tr.root.findall("./files/file"):
        name = Path(f.get("filename", ""))
        if name.is_file():
            sources.append((str(name.resolve()), hashlib.sha256(name.read_bytes()).hexdigest()))
    source_digest = hashlib.sha256(json.dumps(sorted(sources)).encode()).hexdigest()
    report = {"source_xml_sha256": xml_hash, "translation_equivalence": "not_mechanized_from_original_rtl",
              "x_constants_rewritten_to_zero": xcount, "loops_unrolled": loops, "counter_reads_replaced_by_literals": subs,
              "constant_nodes_folded": folded, "counter_inits_added": inits}
    try:
        tr.translate()
        write_coq(args.output / (args.module + ".v"), tr, source_digest, xml_hash, {}, args.module, args.prefix)
        report.update(status="runtime_ast_generated_not_refinement", signals=len(tr.signals),
                      processes=len(tr.processes), features=dict(tr.runtime_tags), source_hashes=sources,
                      signal_table=[vars(s) for s in tr.signals], process_table=tr.process_meta,
                      comb_candidate=tr.comb_graph_metrics, lfp_fuel=tr.lfp_fuel)
    except (ValueError, KeyError, NotImplementedError) as err:
        report.update(status="unsupported", diagnostic=str(err))
    (args.output / "report.json").write_text(json.dumps(report, indent=2))
    print(json.dumps({k: v for k, v in report.items() if k in {
        "status", "diagnostic", "signals", "processes", "lfp_fuel", "x_constants_rewritten_to_zero", "loops_unrolled",
        "counter_reads_replaced_by_literals", "constant_nodes_folded"}}, indent=1))
    return 0 if report["status"] == "runtime_ast_generated_not_refinement" else 1


if __name__ == "__main__":
    raise SystemExit(main())
