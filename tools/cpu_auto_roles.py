#!/usr/bin/env python3
"""Bounded, unproved architectural-role proposals from actual constructor ASTs.

Nothing in this module generates or accepts proof code. A source-role proposal
is not a semantic certificate and must not be used as architectural evidence.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import time
import urllib.error
import urllib.request

import cpu_auto_adapter as adapter

MODEL = "qwen3.8-flash"
ENDPOINT = "https://dashscope.aliyuncs.com/compatible-mode/v1/chat/completions"
PROXY = "http://127.0.0.1:10808"
ROLES = ("register_file", "program_counter")
MAX_CANDIDATES = 256
MAX_RESPONSE_BYTES = 65536
NOTE = adapter.ROOT.parent / "codex_2.md"


def derive_candidates(ast: dict) -> dict:
    """Width/root/indexing facts only; never consult hand-selected profile roots."""
    facts = {}
    for proc in ast["processes"]:
        if proc["kind"] != "Sequential":
            continue
        for node in adapter.walk(proc["body"]):
            if node.name != "SAssign" or node.args[0].name != "true":
                continue
            _, rhs, lhs = node.args
            root = adapter.root_of(lhs)
            if not 0 <= root < ast["signal_count"]:
                raise ValueError("AST writer root out of bounds")
            fact = facts.setdefault(root, {"id": f"root_{root}", "root": root,
                "sequential_writers": set(), "direct_32_writes": 0,
                "indexed_32_writes": 0, "self_add_constant": False,
                "root_width": None, "rhs_summaries": []})
            root_lhs = lhs
            while root_lhs.name == "LSel":
                root_lhs = root_lhs.args[1]
            fact["root_width"] = int(root_lhs.args[0].name)
            summary = adapter.render(rhs)[:500]
            if summary not in fact["rhs_summaries"] and len(fact["rhs_summaries"]) < 2:
                fact["rhs_summaries"].append(summary)
            fact["sequential_writers"].add(proc["name"])
            if lhs.name == "LSel" and lhs.args[0].name == "32":
                fact["indexed_32_writes"] += 1
            if lhs.name == "LVar" and lhs.args[0].name == "32":
                fact["direct_32_writes"] += 1
                for expression in adapter.walk(rhs):
                    if expression.name == "EBinary" and expression.args[1].name == "BAdd":
                        a, b = expression.args[2:]
                        fact["self_add_constant"] |= any(
                            v.name == "EVar" and int(v.args[1].name) == root and c.name == "EConst"
                            for v, c in ((a, b), (b, a)))
    candidates = {role: [] for role in ROLES}
    for root, fact in sorted(facts.items()):
        fact["sequential_writers"] = sorted(fact["sequential_writers"])
        # RV32I has 32 architectural lanes; implementations may omit physical x0.
        # A 3-word token buffer or 64-word counter bank is not the same template.
        if fact["indexed_32_writes"] and fact["root_width"] in {31*32, 32*32}:
            candidates["register_file"].append(fact)
        if fact["direct_32_writes"]:
            candidates["program_counter"].append(fact)
    if sum(map(len, candidates.values())) > MAX_CANDIDATES:
        raise ValueError("candidate budget exceeded; no truncated role analysis")
    return candidates


def attach_metadata_hints(candidates, binding):
    """Names are untrusted hints, checked only for ID/width agreement with AST."""
    if not isinstance(binding, dict) or not binding.get("metadata"):
        return "unavailable"
    try:
        document = json.loads((adapter.ROOT / binding["metadata"]).read_text())
        table = document.get("signal_table", [])
        if not isinstance(table, list):
            return "invalid_signal_table"
        entries = {}
        duplicates = set()
        for entry in table:
            if not isinstance(entry, dict) or type(entry.get("id")) is not int:
                continue
            if entry["id"] in entries:
                duplicates.add(entry["id"])
            entries[entry["id"]] = entry
        for group in candidates.values():
            for candidate in group:
                entry = entries.get(candidate["root"], {})
                hint = entry.get("path")
                if candidate["root"] not in duplicates and type(entry.get("width")) is int \
                        and entry["width"] == candidate["root_width"] and isinstance(hint, str):
                    candidate["untrusted_name_hint"] = hint[:200]
        return "untrusted_id_width_checked_hints"
    except (OSError, ValueError, TypeError):
        return "metadata_unavailable_or_invalid"


def validate_bindings(value, candidates: dict, allowed_roles=None) -> dict:
    """Reject unknown roles/IDs, extra fields, types, and proof-like payloads."""
    allowed = set(ROLES if allowed_roles is None else allowed_roles)
    if not isinstance(value, dict) or set(value) != {"bindings"}:
        raise ValueError("expected only bindings object")
    bindings = value["bindings"]
    if not isinstance(bindings, dict) or not set(bindings) <= allowed:
        raise ValueError("unsupported role")
    result = {}
    for role, candidate_id in bindings.items():
        if role not in ROLES or type(candidate_id) is not str:
            raise ValueError("invalid role binding")
        whitelist = {c["id"] for c in candidates[role]}
        if candidate_id not in whitelist:
            raise ValueError("candidate outside structural whitelist")
        result[role] = candidate_id
    return result


def key_from_note(path: Path = NOTE) -> str:
    """Read the explicit Note credential privately, only after CLI opt-in."""
    source = path.read_text()
    notes = [line for line in source.splitlines() if "**Note**" in line]
    matches = [m.group(0) for line in notes for m in re.finditer(r"sk-[A-Za-z0-9_.-]+", line)]
    if len(matches) != 1:
        raise ValueError("Note must contain exactly one credential")
    return matches[0].rstrip(".")


def _usage(value):
    if not isinstance(value, dict):
        return {}
    return {k: v for k, v in value.items()
            if k in ("prompt_tokens", "completion_tokens", "total_tokens")
            and type(v) is int and v >= 0}


def call_llm(candidates: dict, roles: list, key: str) -> dict:
    """One request, no retries, forced explicit local proxy; no source or secrets logged."""
    payload = {"task": "Choose plausible architectural role candidates, or abstain by omitting a role.",
               "roles": {r: candidates[r] for r in roles},
               "output_schema": {"bindings": {"role": "whitelisted root_N ID"}},
               "status": "UNPROVED"}
    request_body = {"model": MODEL, "temperature": 0, "max_tokens": 256,
        "response_format": {"type": "json_object"},
        "messages": [{"role": "system", "content":
            "Return only JSON with one bindings object. Use supplied role and candidate IDs only. "
            "These structural facts do not prove architectural roles. Never output code or proofs."},
            {"role": "user", "content": json.dumps(payload, separators=(",", ":"))}]}
    data = json.dumps(request_body).encode()
    request = urllib.request.Request(ENDPOINT, data=data, method="POST",
        headers={"Authorization": "Bearer " + key, "Content-Type": "application/json"})
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({"http": PROXY, "https": PROXY}))
    started = time.monotonic()
    audit = {"model": MODEL, "attempts": 1, "status": "failed", "usage": {},
             "proxy": PROXY, "request_bytes": len(data)}
    try:
        if urllib.request.proxy_bypass("dashscope.aliyuncs.com"):
            raise RuntimeError("proxy bypass configuration forbidden")
        with opener.open(request, timeout=60) as response:
            raw = response.read(MAX_RESPONSE_BYTES + 1)
            audit["http_status"] = response.status
        if len(raw) > MAX_RESPONSE_BYTES:
            raise ValueError("response byte budget exceeded")
        document = json.loads(raw)
        audit["usage"] = _usage(document.get("usage"))
        choices = document["choices"]
        if len(choices) != 1 or choices[0].get("finish_reason") != "stop":
            raise ValueError("incomplete model response")
        content = json.loads(choices[0]["message"]["content"])
        audit["bindings"] = validate_bindings(content, candidates, roles)
        audit["status"] = "accepted_unproved"
    except urllib.error.HTTPError as exc:
        audit["http_status"] = exc.code
        audit["error"] = "http_error"
    except Exception as exc:
        # Never serialize exception text: providers/transport may echo credentials.
        audit["error"] = type(exc).__name__
    audit["elapsed_seconds"] = round(time.monotonic() - started, 6)
    return audit


def suggest_roles(profile: dict, output: Path, use_llm=False, key=None) -> dict:
    binding = profile["ast"]
    path = binding["file"] if isinstance(binding, dict) else binding
    ast = adapter.load_ast(adapter.ROOT / path)
    candidates = derive_candidates(ast)
    metadata_status = attach_metadata_hints(candidates, binding)
    report = {"schema_version": 1, "status": "UNPROVED", "ast_sha256": ast["source_sha256"],
              "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "metadata_status": metadata_status,
              "candidates": candidates, "bindings": {}, "unresolved": [],
              "local_semantics_certificates": "separate; no architectural role proved here",
              "llm": {"attempts": 0, "status": "disabled", "usage": {}}}
    for role in ROLES:
        if len(candidates[role]) == 1:
            report["bindings"][role] = {"candidate_id": candidates[role][0]["id"],
                "origin": "unique_structural_candidate", "status": "UNPROVED"}
        else:
            report["unresolved"].append(role)
    ambiguous = [r for r in report["unresolved"] if len(candidates[r]) > 1]
    if use_llm:
        if not ambiguous:
            report["llm"]["status"] = "not_needed"
        elif not key:
            report["llm"]["status"] = "missing_credential"
        else:
            report["llm"] = call_llm(candidates, ambiguous, key)
            for role, candidate_id in report["llm"].pop("bindings", {}).items():
                report["bindings"][role] = {"candidate_id": candidate_id,
                    "origin": "llm_structural_suggestion", "status": "UNPROVED"}
                report["unresolved"].remove(role)
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    (output / "roles.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--use-llm", action="store_true")
    parser.add_argument("--key-from-note", action="store_true")
    args = parser.parse_args()
    key = os.environ.get("DASHSCOPE_API_KEY") if args.use_llm else None
    if args.key_from_note:
        if not args.use_llm:
            parser.error("--key-from-note requires --use-llm")
        key = key_from_note()
    report = suggest_roles(json.loads(args.profile.read_text()), args.output, args.use_llm, key)
    print(json.dumps({"status": report["status"], "llm": report["llm"]}))


if __name__ == "__main__":
    main()
