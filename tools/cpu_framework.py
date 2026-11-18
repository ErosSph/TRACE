#!/usr/bin/env python3
"""Design manifests, LLM obligation prompts, and conservative proof audits.

coqdep supplies actual local Require edges. Unreachable does not mean useless:
other designs, historical LLM runs and baselines are explicit preserved roots.
This tool never deletes files and never labels source discovery ISA refinement.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
FLAGS = ["-R", "src", "Pfv", "-R", "dep/coqutil/src/coqutil", "coqutil",
         "-R", "dep/riscv-coq/src/riscv", "riscv"]
OBLIGATIONS = {
    "startup": "actual reset scheduler is equivalent to the actual boot scheduler",
    "initial": "the actual boot state and initial ISA state satisfy the same joint relation",
    "cycle": "every actual cycle preserves the joint, matching real ISA steps at commits",
    "progress": "the concrete waiting rank strictly decreases on silent cycles",
}
RETIRED_DRAFTS = {
    "CV32E40PFull38HistoryOverlappedJalTwoOwnerCycle":
        "superseded uncompiled helper; whole OverlappedFinalCycle is checked",
    "CV32E40PFull38HeldJalTargetToken":
        "timed-out transport replaced by checked HeldJalTargetTokenReuse",
    "CV32E40PRetainedJalResponseFrontend":
        "timed-out transport replaced by existing EmptyIDReadyFrontend interface",
    "CV32E40PRetainedIndependentJalrResponseFrontend":
        "timed-out transport replaced by existing EmptyIDReadyFrontend interface",
    "CV32E40PFull38HistoryGlobalSafetyDispatch":
        "inactive task-record wrapper archived; final safety uses checked concrete exits",
    "CV32E40PFull38HistoryGlobalReducedSafety":
        "inactive five-family conditional wrapper archived; checked HistoryFinalSafety replaces this route",
}


def load_manifest(path: Path) -> dict:
    manifest = json.loads(path.read_text())
    required = {"schema_version", "design", "backend", "proof_roots", "preserve_roots",
                "verification_scope", "translation_equivalence", "bindings", "proof_providers"}
    missing = required - manifest.keys()
    if missing or manifest["schema_version"] != 1:
        raise ValueError(f"invalid manifest {path}: missing {sorted(missing)} or unsupported schema")
    for source in manifest["proof_roots"] + manifest["preserve_roots"]:
        path_source = Path(source)
        if path_source.is_absolute() or ".." in path_source.parts or not source.endswith(".v"):
            raise ValueError(f"invalid local proof root: {source}")
        if not (ROOT / source).is_file():
            raise ValueError(f"missing proof root: {source}")
    for binding in manifest.get("coq_load_paths", []):
        if set(binding) != {"directory", "namespace"}:
            raise ValueError("coq_load_paths requires directory and namespace")
        directory = Path(binding["directory"])
        if directory.is_absolute() or ".." in directory.parts or not (ROOT / directory).is_dir():
            raise ValueError(f"invalid local Coq directory: {directory}")
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*",
                            binding["namespace"]):
            raise ValueError("invalid Coq namespace")
    return manifest


def parse_dependencies(output: str, source_roots: tuple[str, ...] = ("src",)) -> dict[str, list[str]]:
    graph = {}
    for line in output.replace("\\\n", " ").splitlines():
        if ":" not in line:
            continue
        left, right = line.split(":", 1)
        outputs = left.split()
        obj = next((name for name in outputs if name.endswith(".vo")), None)
        if obj is None:
            continue
        graph[obj[:-1]] = sorted({name[:-1] for name in right.split()
                                 if any(name.startswith(root.rstrip("/") + "/")
                                        for root in source_roots) and name.endswith(".vo")})
    return graph


def closure(graph: dict[str, list[str]], roots: list[str]) -> set[str]:
    seen = set()
    pending = list(roots)
    while pending:
        node = pending.pop()
        if node in seen:
            continue
        if node not in graph:
            raise ValueError(f"coqdep did not report local source {node}")
        seen.add(node)
        pending.extend(graph[node])
    return seen


def dependency_order(graph: dict[str, list[str]], roots: list[str]) -> list[str]:
    ordered, active, seen = [], set(), set()

    def visit(node: str) -> None:
        if node in active:
            raise ValueError(f"dependency cycle at {node}")
        if node in seen:
            return
        if node not in graph:
            raise ValueError(f"missing coqdep node {node}")
        active.add(node)
        for child in graph[node]:
            visit(child)
        active.remove(node)
        seen.add(node)
        ordered.append(node)

    for root in roots:
        visit(root)
    return ordered


def get_graph(manifests: list[dict] | None = None) -> tuple[dict[str, list[str]], str]:
    # Generated ASTs are real dependencies, not opaque external packages. Include
    # their configured namespaces so an audit cannot silently omit the DUT model.
    flags = list(FLAGS)
    roots = {"src"}
    namespaces = {flags[i + 1]: flags[i + 2] for i in range(0, len(flags), 3)}
    for manifest in manifests or []:
        for binding in manifest.get("coq_load_paths", []):
            directory, namespace = binding["directory"], binding["namespace"]
            if directory in namespaces and namespaces[directory] != namespace:
                raise ValueError(f"conflicting namespaces for {directory}")
            if namespace in namespaces.values() and namespaces.get(directory) != namespace:
                raise ValueError(f"conflicting directories for namespace {namespace}")
            if directory not in namespaces:
                namespaces[directory] = namespace
                flags.extend(["-R", directory, namespace])
            roots.add(directory)
    sources = sorted({path.relative_to(ROOT).as_posix() for directory in roots
                      for path in (ROOT / directory).rglob("*.v")})
    result = subprocess.run([str(ROOT / "_opam/bin/coqdep"), *flags, *sources],
                            cwd=ROOT, capture_output=True, text=True, timeout=180)
    if result.returncode:
        raise RuntimeError(f"coqdep failed: {result.stderr[-4000:]}")
    return parse_dependencies(result.stdout, tuple(sorted(roots))), result.stderr


def runtime_references(stem: str, own_source: str) -> list[str]:
    pattern = re.compile(r"(?<![A-Za-z0-9_])" + re.escape(stem) + r"(?![A-Za-z0-9_])")
    refs = []
    for directory in ("src", "tools", "experiments", "framework"):
        for path in (ROOT / directory).rglob("*"):
            if path.suffix not in {".v", ".py", ".sh", ".js", ".json"}:
                continue
            source = path.relative_to(ROOT).as_posix()
            # This catalogue documents retirement; it is not an executable consumer.
            if source in {own_source, "tools/cpu_framework.py"}:
                continue
            if pattern.search(path.read_text(errors="replace")):
                refs.append(source)
    return sorted(refs)


def audit(manifest: dict) -> dict:
    manifests = [load_manifest(path) for path in sorted((ROOT / "framework/designs").glob("*.json"))]
    graph, warnings = get_graph(manifests)
    active = closure(graph, manifest["proof_roots"])
    all_roots = sorted({root for item in manifests
                        for root in item["proof_roots"] + item["preserve_roots"]})
    retained = closure(graph, all_roots)
    drafts = []
    for stem, reason in RETIRED_DRAFTS.items():
        source = f"src/Ex/External/{stem}.v"
        if not (ROOT / source).is_file():
            continue
        dependents = sorted(node for node, deps in graph.items() if source in deps)
        refs = runtime_references(stem, source)
        drafts.append({"source": source, "reason": reason,
                       "sha256": hashlib.sha256((ROOT / source).read_bytes()).hexdigest(),
                       "in_preserved_closure": source in retained,
                       "coq_dependents": dependents, "runtime_references": refs,
                       "safe_retired_leaf": source not in retained and not dependents and not refs})
    return {
        "design": manifest["design"], "dependency_engine": "coqdep (not a regex proof parser)",
        "total_local_sources": len(graph), "active_closure_count": len(active),
        "active_dependency_order": dependency_order(graph, manifest["proof_roots"]),
        "all_preserved_roots": all_roots, "preserved_closure_count": len(retained),
        "outside_active_closure": sorted(set(graph) - active),
        "outside_preserved_closure": sorted(set(graph) - retained),
        "retired_drafts": drafts, "coqdep_warnings": warnings,
        "claim": "dependency inventory only; source presence/coqdep success is not proof acceptance",
        "policy": "outside a closure is inventory only, not permission to delete",
    }


def render_prompt(manifest: dict) -> str:
    target = manifest.get("pinned_target")
    acceptance = (f"Submit Ex.External.CPUDesignTarget.Certificate ({target})."
                  if target else
                  "No pinned Coq target is registered yet. Produce source/transition connection "
                  "tasks only; an arbitrary DesignContract or invented Target is NOT accepted.")
    return "\n".join([
        f"Design: {manifest['design']}", f"Backend: {manifest['backend']}",
        f"Scope: {manifest['verification_scope']}",
        f"Source-to-model equivalence status: {manifest['translation_equivalence']}",
        "Target interface: Ex.External.CPUDesignTarget.Certificate actual_target",
        acceptance,
        "Only the framework fixes actual_target, including its architecture relation. "
        "The candidate may provide Joint, rank and proofs, not change the target.",
        "The following bindings are pinned to the actual design. Do not replace its step or observer.",
        json.dumps(manifest["bindings"], indent=2),
        "Fill the four proof fields using checked existing results where available:",
        json.dumps(OBLIGATIONS, indent=2),
        "Existing providers (candidates to reuse, not trusted natural-language evidence):",
        json.dumps(manifest["proof_providers"], indent=2),
        "If missing, produce a proof task about the actual transition, including its precise context.",
        "Do not weaken the goal, hide future correctness in the invariant, modify semantics,",
        "or introduce Axiom/Admitted/Parameter/Abort. Signal discovery alone is not a semantic proof.",
        "Submit complete Rocq code; acceptance requires the exact pinned Certificate type, "
        "coqc, assumptions audit, and kernel checks. Manifest text is not proof acceptance.",
        "No LLM request is made by this prompt generator.", "",
    ])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("audit", "prompt", "show"))
    parser.add_argument("--design", default="cv32e40p")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not re.fullmatch(r"[a-zA-Z0-9_-]+", args.design):
        parser.error("design must be a manifest name, not a path")
    manifest = load_manifest(ROOT / "framework/designs" / f"{args.design}.json")
    if args.action == "prompt":
        output = render_prompt(manifest)
    else:
        report = audit(manifest) if args.action == "audit" else manifest
        output = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
        if args.action == "audit":
            print(json.dumps({key: report[key] for key in
                             ("design", "total_local_sources", "active_closure_count",
                              "preserved_closure_count", "retired_drafts")}, indent=2))
    else:
        print(output, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
