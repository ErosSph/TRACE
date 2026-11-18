#!/usr/bin/env python3
"""Generate semantic adapter proofs from the imported RTL syntax.

The parser accepts only the frontend's constructor language.  Python proposes
plans; Coq checks their equality to compile_nb over the actual imported body.
No CPU-specific process IDs, architectural roles, or proof names occur here.
Global invariant synthesis is a separate obligation, never inferred from local
success.  A new imported design can use --ast/--ast-module/--program directly.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_framework as framework
from cpu_certificate_acceptance import run_stage

ROOT = framework.ROOT
SYMBOL = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*")
ARITIES = {
    "EConst": 2, "EVar": 2, "ESel": 3, "EConcat": 3, "EReplicate": 3,
    "EExtend": 3, "EUnary": 3, "EBinary": 4, "ECond": 4,
    "LVar": 2, "LSel": 3, "SSkip": 0, "SAssign": 3, "SSeq": 1,
    "SIf": 3, "SCase": 2, "Some": 1, "None": 0,
}
ATOMS = {"true", "false", "UNot", "UNegate", "URedOr", "BAnd", "BOr", "BXor",
         "BAdd", "BSub", "BMul", "BEq", "BNeq", "BLtU", "BGtU", "BGtS",
         "BShiftL", "BShiftR", "BShiftRS"}


@dataclass(frozen=True)
class Term:
    name: str
    args: tuple = ()


class Parser:
    """A closed grammar, not evaluation of source text or arbitrary Coq."""
    def __init__(self, text: str):
        self.tokens = re.findall(r"[A-Za-z_][A-Za-z0-9_]*|-?[0-9]+|[()[\];,]", text)
        if re.sub(r"\s+", "", text) != "".join(self.tokens):
            raise ValueError("unsupported characters in frontend constructor term")
        self.pos = 0

    def take(self, expected=None):
        if self.pos >= len(self.tokens):
            raise ValueError("incomplete constructor term")
        token = self.tokens[self.pos]
        self.pos += 1
        if expected is not None and token != expected:
            raise ValueError(f"expected {expected}, got {token}")
        return token

    def parse(self):
        token = self.take()
        if token == "(":
            node = self.parse()
            if self.tokens[self.pos] == ",":
                self.take(",")
                node = Term("pair", (node, self.parse()))
            self.take(")")
            return node
        if token == "[":
            nodes = []
            while self.tokens[self.pos] != "]":
                nodes.append(self.parse())
                if self.tokens[self.pos] != "]":
                    self.take(";")
            self.take("]")
            return Term("list", tuple(nodes))
        if token in ARITIES:
            return Term(token, tuple(self.parse() for _ in range(ARITIES[token])))
        if token in ATOMS or re.fullmatch(r"-?[0-9]+", token):
            return Term(token)
        raise ValueError(f"unsupported constructor {token}")

    def complete(self):
        node = self.parse()
        if self.pos != len(self.tokens):
            raise ValueError("trailing constructor tokens")
        return node


def render(t: Term) -> str:
    if t.name == "list":
        return "[" + "; ".join(map(render, t.args)) + "]"
    if t.name == "pair":
        return "(" + ", ".join(map(render, t.args)) + ")"
    if not t.args:
        return t.name if not t.name.startswith("-") else "(" + t.name + ")"
    return "(" + t.name + " " + " ".join(map(render, t.args)) + ")"


def walk(t):
    yield t
    for child in t.args:
        yield from walk(child)


def plan_of(st: Term) -> Term:
    if st.name == "SSkip":
        return Term("NEmpty")
    if st.name == "SAssign":
        nba, rhs, lhs = st.args
        if nba.name != "true":
            raise ValueError("blocking assignment requires a different template")
        return Term("NAssign", (rhs, lhs))
    if st.name == "SSeq":
        return Term("NSeq", (Term("list", tuple(plan_of(s) for s in st.args[0].args)),))
    if st.name == "SIf":
        g, y, n = st.args
        return Term("NIf", (g, plan_of(y), plan_of(n)))
    if st.name == "SCase":
        e, arms = st.args
        return Term("NCase", (e, Term("list", tuple(
            Term("pair", (arm.args[0], plan_of(arm.args[1]))) for arm in arms.args))))
    raise ValueError(f"unsupported statement {st.name}")


def root_of(lhs):
    if lhs.name == "LVar":
        return int(lhs.args[1].name)
    if lhs.name == "LSel":
        return root_of(lhs.args[1])
    raise ValueError("invalid assignment lvalue")


def effect_of(st: Term) -> Term:
    if st.name == "SSkip":
        return Term("FEmpty")
    if st.name == "SAssign":
        return Term("FAssign", st.args)
    if st.name == "SSeq":
        return Term("FSeq", (Term("list", tuple(effect_of(s) for s in st.args[0].args)),))
    if st.name == "SIf":
        g, y, n = st.args
        return Term("FIf", (g, effect_of(y), effect_of(n)))
    if st.name == "SCase":
        e, arms = st.args
        return Term("FCase", (e, Term("list", tuple(
            Term("pair", (arm.args[0], effect_of(arm.args[1]))) for arm in arms.args))))
    raise ValueError(f"unsupported statement {st.name}")


def load_ast(path: Path) -> dict:
    source = path.read_text()
    module = re.search(r"^Module ([A-Za-z_][A-Za-z0-9_]*)\.", source, re.M)
    if not module:
        raise ValueError("missing generated AST module")
    processes = []
    pattern = re.compile(r"^Definition (process_[0-9]+) : Process := \{\| "
        r"process_kind := (Initial|Sequential|Combinational); process_events := (.*?); "
        r"process_body := (.*); process_source_line := ([0-9]+) \|\}\.$", re.M)
    for match in pattern.finditer(source):
        name, kind, events, body, line = match.groups()
        term = Parser(body).complete()
        assignments = [n for n in walk(term) if n.name == "SAssign"]
        readers = sorted({int(n.args[1].name) for n in walk(term) if n.name == "EVar"})
        writers = sorted({root_of(n.args[2]) for n in assignments})
        indexed = [n for n in assignments if n.args[2].name == "LSel"]
        processes.append({"name": name, "kind": kind, "body": term,
            "events": events, "line": int(line), "readers": readers, "writers": writers,
            "assignments": len(assignments), "indexed_writes": len(indexed)})
    declared = len(re.findall(r"^Definition process_[0-9]+ : Process", source, re.M))
    if declared != len(processes) or not processes:
        raise ValueError("not all declared processes were parsed; refusing partial analysis")
    signal_count = re.search(r"signal_count := ([0-9]+)", source)
    fuel = re.search(r"statement_fuel := ([0-9]+)", source)
    if not signal_count or not fuel:
        raise ValueError("missing actual Program fields")
    return {"module": module.group(1), "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
            "signal_count": int(signal_count.group(1)), "statement_fuel": int(fuel.group(1)),
            "processes": processes}


def analyze(ast: dict) -> dict:
    """No role names needed: compile every supported actual sequential body."""
    plans, effects, residual = [], [], []
    for proc in ast["processes"]:
        if proc["kind"] != "Sequential":
            continue
        try:
            plans.append((proc, plan_of(proc["body"])))
        except ValueError as exc:
            try:
                effects.append((proc, effect_of(proc["body"])))
            except ValueError as fallback:
                residual.append({"process": proc["name"], "reason": str(fallback)})
    comb_writes = {r for p in ast["processes"] if p["kind"] == "Combinational" for r in p["writers"]}
    seq_writes = {r for p in ast["processes"] if p["kind"] == "Sequential" for r in p["writers"]}
    # Pure state roots permit the existing all-state phase projection theorem.
    roots = sorted(seq_writes - comb_writes)
    compiled = {p["name"] for p, _ in plans}
    plan_roots = [root for root in roots if all(p["name"] in compiled
        for p in ast["processes"] if p["kind"] == "Sequential" and root in p["writers"])]
    return {"plans": plans, "effects": effects, "residual": residual, "roots": roots, "plan_roots": plan_roots}


def render_adapter(ast_module: str, program: str, ast: dict, analysis: dict, program_imports=()) -> str:
    if not all(SYMBOL.fullmatch(x) for x in (ast_module, program, *program_imports)):
        raise ValueError("invalid AST module or program symbol")
    mod = ast["module"]
    lines = ["(** Generated semantic adapter: independently proposed plans are checked against actual AST. *)",
        "From Coq Require Import List ZArith Arith.",
        "Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice",
        f" Lang.ExtendedSVStaticRootCertificate Lang.ExtendedSVAutoAdapterPlan Lang.ExtendedSVAutoAdapterPhase",
        f" Lang.ExtendedSVAutoAdapterEffects {ast_module} {' '.join(program_imports)}.",
        "Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice",
        f" ExtendedSVStaticRootCertificate ExtendedSVAutoAdapterPlan ExtendedSVAutoAdapterPhase ExtendedSVAutoAdapterEffects {mod}."]
    for proc, plan in analysis["plans"]:
        name = proc["name"]
        lines += [f"Definition {name}_plan : NbPlan := {render(plan)}.",
            f"Lemma {name}_plan_checked : compile_nb (statement_fuel {program})",
            f" (process_body {mod}.{name}) = Some {name}_plan.",
            "Proof. vm_compute. reflexivity. Qed.",
            f"Definition {name}_actual_updates := checked_process_plan {program} {mod}.{name}",
            f" {name}_plan {name}_plan_checked.",
            f"Definition {name}_actual_run := checked_run_plan {program} {mod}.{name}",
            f" {name}_plan {name}_plan_checked.",
            f"Definition {name}_actual_projection := checked_plan_projection {program} {mod}.{name}",
            f" {name}_plan {name}_plan_checked."]
    for proc, effect in analysis["effects"]:
        name = proc["name"]
        lines += [f"Definition {name}_effect : EffectPlan := {render(effect)}.",
            f"Lemma {name}_effect_checked : compile_effect (statement_fuel {program})",
            f" (process_body {mod}.{name}) = Some {name}_effect.",
            "Proof. vm_compute. reflexivity. Qed.",
            f"Definition {name}_actual_updates := checked_effect_updates {program} {mod}.{name}",
            f" {name}_effect {name}_effect_checked.",
            f"Definition {name}_actual_run := checked_effect_run {program} {mod}.{name}",
            f" {name}_effect {name}_effect_checked."]
    # Kernel-check the exact ordered writer lists; no name-based architectural claim.
    for root in analysis["roots"]:
        writers = [f"{mod}.{p['name']}" for p in ast["processes"] if root in p["writers"]]
        writer_list = "[" + "; ".join(writers) + "]"
        lines += [f"Lemma root_{root}_bound : ({root} < signal_count {program})%nat.",
            "Proof. apply Nat.ltb_lt. vm_compute. reflexivity. Qed.",
            f"Lemma root_{root}_comb_frame : comb_root_unwrittenb {program} {root}%nat = true.",
            "Proof. vm_compute. reflexivity. Qed.",
            f"Lemma root_{root}_writers : filter (writes_rootb {root}%nat) (processes {program}) = {writer_list}.",
            "Proof. vm_compute. reflexivity. Qed.",
            f"Definition root_{root}_certificate : RootCertificate {program} {root}%nat {writer_list} :=",
            f" Build_RootCertificate _ _ _ root_{root}_bound root_{root}_comb_frame root_{root}_writers.",
            f"Definition root_{root}_actual_phase := certified_phase_root _ _ _ root_{root}_certificate."]
    for root in analysis["plan_roots"]:
        procs = [p for p in ast["processes"] if p["kind"] == "Sequential" and root in p["writers"]]
        entries = "[" + "; ".join(f"({mod}.{p['name']}, {p['name']}_plan)" for p in procs) + "]"
        seqs = "[" + "; ".join(f"{mod}.{p['name']}" for p in procs) + "]"
        lines += [f"Definition root_{root}_plan_entries : list (Process * NbPlan) := {entries}.",
            f"Lemma root_{root}_sequential_writers : filter is_sequential",
            f" (filter (writes_rootb {root}%nat) (processes {program})) = map fst root_{root}_plan_entries.",
            f"Proof. rewrite root_{root}_writers. reflexivity. Qed.",
            f"Lemma root_{root}_plans_checked : Forall (fun entry =>",
            f" compile_nb (statement_fuel {program}) (process_body (fst entry)) = Some (snd entry)) root_{root}_plan_entries.",
            "Proof. unfold root_" + str(root) + "_plan_entries."]
        for proc in procs:
            lines += [f" constructor; [exact {proc['name']}_plan_checked|]."]
        lines += [" constructor. Qed.",
            f"Definition root_{root}_plan_certificate : PlanRootCertificate {program} {root}%nat root_{root}_plan_entries :=",
            f" Build_PlanRootCertificate _ _ _ root_{root}_bound root_{root}_comb_frame",
            f" root_{root}_sequential_writers root_{root}_plans_checked.",
            f"Definition root_{root}_compiled_phase := planned_phase_root _ _ _ root_{root}_plan_certificate."]
    # Audit every generated semantic consequence, not just the last closed one.
    n = 0
    for proc, _ in analysis["plans"]:
        for suffix in ("actual_updates", "actual_run", "actual_projection"):
            lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{n}". exact I. Qed.',
                      f"Print Assumptions {proc['name']}_{suffix}."]
            n += 1
    for root in analysis["roots"]:
        lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{n}". exact I. Qed.',
                  f"Print Assumptions root_{root}_actual_phase."]
        n += 1
    for proc, _ in analysis["effects"]:
        for suffix in ("actual_updates", "actual_run"):
            lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{n}". exact I. Qed.',
                      f"Print Assumptions {proc['name']}_{suffix}."]
            n += 1
    for root in analysis["plan_roots"]:
        lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{n}". exact I. Qed.',
                  f"Print Assumptions root_{root}_compiled_phase."]
        n += 1
    return "\n".join(lines) + "\n"


def check_profile(profile: dict, output: Path, timeout: float = 1200) -> dict:
    if isinstance(profile.get("ast"), dict):
        binding = profile["ast"]
        profile = {"design": profile.get("design", "custom"), "ast": binding["file"],
                   "ast_module": binding["module"], "program": binding["program"],
                   "program_imports": binding.get("program_imports", []),
                   "coq_load_paths": profile.get("coq_load_paths", [])}
    if output.exists():
        raise ValueError("output must be fresh; preserve earlier attempts")
    output.mkdir(parents=True)
    ast_path = ROOT / profile["ast"]
    ast = load_ast(ast_path)
    analysis = analyze(ast)
    source = render_adapter(profile["ast_module"], profile["program"], ast, analysis,
                            profile.get("program_imports", []))
    source_path = output / "AutoAdapter.v"
    source_path.write_text(source)
    proc_table = [{k:v for k,v in p.items() if k != "body"} for p in ast["processes"]]
    report = {"schema_version": 1, "design": profile.get("design", "custom"),
        "ast": profile["ast"], "ast_sha256": ast["source_sha256"],
        "actual_program": profile["program"],
        "generated_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "signal_count": ast["signal_count"], "process_count": len(proc_table),
        "sequential_processes": sum(p["kind"] == "Sequential" for p in proc_table),
        "generated_sequential_plans": len(analysis["plans"]),
        "generated_state_threaded_effect_plans": len(analysis["effects"]),
        "generated_phase_root_certificates": len(analysis["roots"]),
        "generated_compiled_phase_projections": len(analysis["plan_roots"]),
        "generated_semantic_consequences": 3*len(analysis["plans"])+2*len(analysis["effects"])+len(analysis["roots"])+len(analysis["plan_roots"]),
        "residual_processes": analysis["residual"], "process_table": proc_table,
        "llm_calls": 0, "local_semantics_accepted": False,
        "global_invariant_synthesized": False, "new_cpu_infinite_refinement": False,
        "translation_equivalence": "external RTL to AST remains unmechanized"}
    flags = list(framework.FLAGS)
    for binding in profile.get("coq_load_paths", []):
        flags += ["-R", binding["directory"], binding["namespace"]]
    # Generated AST namespaces are explicit inputs, not CPU-name dispatch.
    namespace = profile["ast_module"].rsplit(".", 1)[0]
    if not namespace.startswith("Ex."):
        pair = ["-R", str(ast_path.parent), namespace]
        if not any(flags[i:i+3] == pair for i in range(len(flags)-2)):
            flags += pair
    flags += ["-R", str(output.resolve()), "CPUAuto"]
    start = time.monotonic()
    compiled, timed = run_stage([str(ROOT / "_opam/bin/coqc"), "-q", "-time", *flags,
                               str(source_path.resolve())], output / "coqc.log", timeout)
    report.update(coqc_exit=compiled.returncode, coqc_seconds=time.monotonic()-start,
                  coqc_timed_out=timed)
    if compiled.returncode == 0:
        marker_count = report["generated_semantic_consequences"]
        chunks = re.split(r"^AUTO_ADAPTER_ASSUMPTIONS_[0-9]+\s*$", compiled.stdout, flags=re.M)[1:]
        audits = len(chunks) == marker_count and marker_count > 0
        for chunk in chunks:
            # Local semantic adapter theorems should be closed, not merely within FE allowance.
            audits = audits and "Closed under the global context" in chunk and "Axioms:" not in chunk
        report["assumption_audits_closed"] = audits
        start = time.monotonic()
        kernel, timed = run_stage([str(ROOT / "_opam/bin/coqchk"), "-silent", *flags,
                                  "-norec", "CPUAuto.AutoAdapter"], output / "coqchk.log", timeout)
        report.update(coqchk_exit=kernel.returncode, coqchk_seconds=time.monotonic()-start,
                      coqchk_timed_out=timed)
        report["local_semantics_accepted"] = audits and kernel.returncode == 0
    (output / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--profile", type=Path)
    ap.add_argument("--ast", type=Path)
    ap.add_argument("--ast-module")
    ap.add_argument("--program")
    ap.add_argument("--load-path", action="append", default=[], metavar="DIRECTORY=NAMESPACE")
    ap.add_argument("--output", required=True, type=Path)
    ap.add_argument("--timeout", type=float, default=1200)
    args = ap.parse_args()
    if args.profile:
        profile = json.loads(args.profile.read_text())
    else:
        if not all((args.ast, args.ast_module, args.program)):
            ap.error("provide --profile or --ast/--ast-module/--program")
        profile = {"ast": str(args.ast), "ast_module": args.ast_module, "program": args.program,
                   "coq_load_paths": [{"directory": x.split("=",1)[0], "namespace": x.split("=",1)[1]}
                                      for x in args.load_path]}
    report = check_profile(profile, args.output, args.timeout)
    print(json.dumps({k:v for k,v in report.items() if k != "process_table"}, indent=2))
    return 0 if report["local_semantics_accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
