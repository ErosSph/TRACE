#!/usr/bin/env python3
"""NERV import front end: cpu_array_frontend.ArrayTranslator plus ONE additive pre-pass.

The trusted frontends are not modified.  nerv.sv drives 'don't care' values with x literals
(`dmem_addr`, `dmem_wdata`, `mem_wr_*`, `mem_rd_*`, `csr_rdval` default to 32'hx / 5'hx / 4'hx).  Verilator prints
them as binary constants with x bits (`32'bxxxx...`), which `parse_const` (hex only) rejects.  The pre-pass rewrites
every constant that contains x/z bits to the hex constant with those bits set to 0 (the AST semantics is two-valued).
This is a concrete choice of the don't-care value; it is sound for the observed behaviour only because every x
use is dominated by a guard (valid / enable / csr_ack / sel) -- the guard is checked empirically by the
differential test against a Verilator C++ model built with --x-assign 0, 1 and unique (tools/nerv_cosim.py).
Constants without x/z bits are not touched, so the output for designs without x literals is unchanged.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
import xml.etree.ElementTree as ET

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cpu_array_frontend import ArrayTranslator
from cv32e40p_extended_frontend import write_coq, EXPR_TAGS

XCONST = re.compile(r"(\d+)'(s?)b([01xXzZ_]+)")


def wildcard_key(name):
    """For a casez item constant containing z bits: (width, care_mask, value).  x bits are not wildcards in
    casez and are rejected; constants without z return None."""
    m = XCONST.fullmatch(name)
    if not m or not re.search(r"[zZ]", m.group(3)):
        return None
    width, _, digits = m.groups()
    digits = digits.replace("_", "")
    if re.search(r"[xX]", digits):
        raise ValueError(f"casez item mixes x and z: {name}")
    digits = digits.rjust(int(width), "0")   # Verilator prints the constant without its leading zeros
    if len(digits) != int(width):
        raise ValueError(f"casez item width mismatch: {name}")
    mask = int(re.sub(r"[zZ]", "0", re.sub(r"[01]", "1", digits)), 2)
    return int(width), mask, int(re.sub(r"[zZ]", "0", digits), 2)


class NervTranslator(ArrayTranslator):
    """casez: a case whose item constants contain z bits is lowered to a priority if-chain
    `(scrutinee & care_mask) == value` (first match wins; the default arm goes last).  Other cases are untouched."""

    def stmt(self, node, env):
        if node.tag == "case":
            children = [c for c in node if c.tag not in {"sentree", "var"}]
            items = children[1:]
            keyed = [k for it in items if it.tag == "caseitem" for k in list(it)[:-1]
                     if k.tag == "const" and wildcard_key(k.get("name"))]
            if keyed:
                return self.casez(children[0], items, env)
        return super().stmt(node, env)

    def casez(self, scrut_node, items, env):
        self.runtime_tags["casez_lowered"] += 1
        ws = self.width(scrut_node)
        scrut = self.expr(scrut_node, env)
        branches, default = [], "SSkip"
        for item in items:
            ich = list(item)
            if not ich:
                continue
            if ich[-1].tag in EXPR_TAGS:      # keys with an empty body
                keys, body = ich, "SSkip"
            else:
                keys, body = ich[:-1], self.stmt(ich[-1], env)
            if not keys:
                default = body
                continue
            conds = []
            for k in keys:
                w = wildcard_key(k.get("name")) if k.tag == "const" else None
                if w:
                    _, mask, val = w
                    conds.append(f"EBinary 1 BEq (EBinary {ws} BAnd ({scrut}) (EConst {ws} {mask})) (EConst {ws} {val})")
                else:
                    conds.append(f"EBinary 1 BEq ({scrut}) ({self.expr(k, env)})")
            cond = conds[0]
            for c in conds[1:]:
                cond = f"ECond 1 ({cond}) (EConst 1 1) ({c})"
            branches.append((cond, body))
        out = default
        for cond, body in reversed(branches):
            out = f"SIf ({cond}) ({body}) ({out})"
        return out


def zero_x_constants(root):
    """Rewrite binary constants containing x/z bits to hex with those bits 0.  Returns the number rewritten."""
    count = 0
    for node in root.iter("const"):
        m = XCONST.fullmatch(node.get("name", ""))
        if not m:
            continue
        width, signed, digits = m.groups()
        digits = digits.replace("_", "")
        if not re.search(r"[xX]", digits) or re.search(r"[zZ]", digits):
            continue            # no x bits, or a casez wildcard (handled by NervTranslator.casez)
        value = int(re.sub(r"[xXzZ]", "0", digits), 2)
        if len(digits) != int(width):
            raise ValueError(f"x constant width mismatch: {node.get('name')}")
        node.set("name", f"{width}'{signed}h{value:x}")
        count += 1
    return count


def _cval(node):
    m = re.fullmatch(r"(\d+)'(s?)h([0-9a-fA-F]+)", node.get("name", "")) if node.tag == "const" else None
    if not m:
        raise ValueError(f"loop bound is not a constant at {node.get('loc')}")
    w, sg, d = int(m.group(1)), m.group(2), int(m.group(3), 16)
    return d - (1 << w) if sg and d >> (w - 1) else d


def _loop_trip(init, cond, incr, var):
    """Concrete iteration count of `for (var = init; cond; var = var +/- c)`; every operand is constant."""
    ops = {"gts": lambda a, b: a > b, "lts": lambda a, b: a < b, "gtes": lambda a, b: a >= b,
           "ltes": lambda a, b: a <= b, "gt": lambda a, b: a > b, "lt": lambda a, b: a < b,
           "gte": lambda a, b: a >= b, "lte": lambda a, b: a <= b, "neq": lambda a, b: a != b}
    if cond.tag not in ops:
        raise ValueError(f"unsupported loop condition {cond.tag} at {cond.get('loc')}")
    step_expr = list(incr)[0]
    if step_expr.tag not in {"add", "sub"}:
        raise ValueError(f"unsupported loop increment at {incr.get('loc')}")
    a, b = list(step_expr)
    if a.tag == "const" and b.tag == "varref" and b.get("name") == var:
        c = _cval(a)
        delta = c if step_expr.tag == "add" else None      # c - var is not a counter step
    elif b.tag == "const" and a.tag == "varref" and a.get("name") == var:
        c = _cval(b)
        delta = c if step_expr.tag == "add" else -c
    else:
        delta = None
    if not delta:
        raise ValueError(f"unsupported loop step at {incr.get('loc')}")
    lhs, rhs = list(cond)
    f = lambda n, v: v if (n.tag == "varref" and n.get("name") == var) else _cval(n)
    v, n = init, 0
    while ops[cond.tag](f(lhs, v), f(rhs, v)):
        v += delta
        n += 1
        if n > 4096:
            raise ValueError(f"loop does not terminate statically at {cond.get('loc')}")
    return n


def unroll_loops(root):
    """Unroll `while` loops with a static trip count: init; (body; step) x N.  The init assignment stays, the loop
    variable is still assigned at every step, so the statement sequence is exactly the loop's execution
    (what Verilator's own unroll pass does; --xml-only stops before it).  Returns the number of loops unrolled."""
    import copy
    total = 0
    while True:
        found = False
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
                n = _loop_trip(_cval(prev[0]), cond, incr, var)
                new = []
                for _ in range(n):
                    new += [copy.deepcopy(b) for b in body] + [copy.deepcopy(incr)]
                if not n:
                    new = []
                parent.remove(w)
                for j, e in enumerate(new):
                    parent.insert(idx + j, e)
                total += 1
                break               # restart: the child list changed
            if found:
                break
        if not found:
            return total


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
    if not pinned.get("source_hashes"):
        raise ValueError("source hashes are missing; regenerate elaboration report")
    root = ET.parse(args.xml).getroot()
    xcount = zero_x_constants(root)
    loops = unroll_loops(root)
    tr = NervTranslator(root, args.top)
    sources = []
    for f in tr.root.findall("./files/file"):
        name = Path(f.get("filename", ""))
        if name.is_file():
            sources.append((str(name.resolve()), hashlib.sha256(name.read_bytes()).hexdigest()))
    source_digest = hashlib.sha256(json.dumps(sorted(sources)).encode()).hexdigest()
    report = {"source_xml_sha256": xml_hash, "translation_equivalence": "not_mechanized_from_original_rtl",
              "x_constants_rewritten_to_zero": xcount, "loops_unrolled": loops}
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
        "status", "diagnostic", "signals", "processes", "lfp_fuel", "x_constants_rewritten_to_zero", "loops_unrolled"}}, indent=1))
    return 0 if report["status"] == "runtime_ast_generated_not_refinement" else 1


if __name__ == "__main__":
    raise SystemExit(main())
