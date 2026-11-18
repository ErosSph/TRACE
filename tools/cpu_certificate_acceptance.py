#!/usr/bin/env python3
"""Type/kernel acceptance of a provider for a framework-pinned CPU target.

The proposal is a qualified symbol, not executable Coq text or a replacement
Target. This is a proof acceptance gate, not an LLM API or RTL compiler proof.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import signal
import threading
import time
import cpu_framework as framework

SYMBOL = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*")
ALLOWED_AXIOMS = {"FunctionalExtensionality.functional_extensionality_dep"}


def render_proof_argument(node: dict, binders: list[str], depth: int = 0) -> str:
    """Small applicative proof term from versioned framework data, never Coq text.

    This only assembles checked names. Coq must still prove the resulting term
    inhabits the exact pinned certificate, and both assumption audits still run.
    """
    if depth > 12 or not isinstance(node, dict):
        raise ValueError("invalid structured proof argument")
    if set(node) == {"nat"}:
        value = node["nat"]
        if type(value) is not int or not 0 <= value <= 1024:
            raise ValueError("invalid bounded natural proof argument")
        return str(value) + "%nat"
    if set(node) == {"binder"}:
        name = node["binder"]
        if not isinstance(name, str) or name not in binders:
            raise ValueError("unknown proof argument binder")
        return name
    if not {"symbol"} <= set(node) <= {"symbol", "arguments"}:
        raise ValueError("invalid structured proof argument keys")
    symbol = node["symbol"]
    if not isinstance(symbol, str) or not SYMBOL.fullmatch(symbol):
        raise ValueError("invalid proof argument symbol")
    arguments = node.get("arguments", [])
    if not isinstance(arguments, list) or len(arguments) > 8:
        raise ValueError("invalid proof argument applications")
    rendered = [render_proof_argument(arg, binders, depth + 1) for arg in arguments]
    return "(" + " ".join([symbol, *rendered]) + ")" if rendered else symbol


def render_harness(manifest: dict, provider: str) -> str:
    if not SYMBOL.fullmatch(provider):
        raise ValueError("provider must be a qualified Coq symbol, not code")
    harness = manifest.get("certificate_harness")
    if not manifest.get("pinned_target") or not harness:
        raise ValueError("no framework-pinned certificate harness for this design")
    # These declarations belong to the versioned framework, never the proposal.
    imports = harness["imports"]
    opens = harness.get("open_modules", ["CPUDesignTarget"])
    if not all(SYMBOL.fullmatch(name) for name in imports + opens):
        raise ValueError("invalid framework import")
    args = harness["arguments"]
    if not all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name) for name in args):
        raise ValueError("invalid framework argument")
    # Opt-in typed composition: provider-specific arguments differ from the
    # target binders. Keep the latter for replaying acceptance_certificate.
    applications = harness.get("provider_applications", {})
    if not isinstance(applications, dict) or len(applications) > 16:
        raise ValueError("invalid framework proof applications")
    rendered_applications = {}
    for name, nodes in applications.items():
        if not isinstance(name, str) or not SYMBOL.fullmatch(name):
            raise ValueError("invalid framework proof compiler")
        if not isinstance(nodes, list) or len(nodes) > 8:
            raise ValueError("invalid framework proof arguments")
        rendered_applications[name] = [render_proof_argument(node, args) for node in nodes]
    provider_args = rendered_applications.get(provider, args)
    application_imports = harness.get("provider_application_imports", {})
    if not isinstance(application_imports, dict) or not set(application_imports) <= set(applications):
        raise ValueError("imports require a registered proof application")
    for names in application_imports.values():
        if (not isinstance(names, list) or not names or
                not all(isinstance(name, str) and SYMBOL.fullmatch(name) for name in names)):
            raise ValueError("invalid proof application imports")
    imports = application_imports.get(provider, imports)
    # The versioned framework selects a checked interface, never the proposal.
    # Both interfaces consume the same CPUDesignTarget.Target, including its
    # independently pinned architectural relation.
    interface = harness.get("certificate_interface", "cycle")
    if interface == "cycle":
        certificate_type = "Certificate"
        refinement_rule = "CPUDesignTarget.pinned_target_infinite_refinement"
    elif interface == "boundary":
        certificate_type = "CPUCommitBoundaryTarget.Certificate"
        refinement_rule = "CPUCommitBoundaryTarget.pinned_target_infinite_refinement"
    else:
        raise ValueError("unknown framework certificate interface")
    return ("(** Generated fixed-target acceptance; proposal supplies a symbol only. *)\n"
            + "Require Import " + " ".join(imports) + ".\n"
            + "Import " + " ".join(opens) + ".\n"
            + "Definition acceptance_certificate " + harness["binders"]
            + " : " + certificate_type + " (" + manifest["pinned_target"] + ") :=\n "
            + provider + (" " + " ".join(provider_args) if provider_args else "") + ".\n"
            + 'Goal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\n'
            + "Print Assumptions acceptance_certificate.\n"
            + "Definition acceptance_infinite_refinement " + harness["binders"]
            + " :=\n " + refinement_rule + " ("
            + manifest["pinned_target"] + ") (acceptance_certificate"
            + (" " + " ".join(args) if args else "") + ").\n"
            + 'Goal True. idtac "REFINEMENT_ASSUMPTIONS". exact I. Qed.\n'
            + "Print Assumptions acceptance_infinite_refinement.\n")


def parse_assumptions(output: str, marker: str = "ACCEPTANCE_ASSUMPTIONS") -> set[str]:
    if marker not in output:
        raise ValueError("missing final assumption audit")
    audit = output.rsplit(marker, 1)[1]
    # Audit each artifact independently: a closed later theorem must never hide
    # assumptions of an earlier certificate (or vice versa).
    audit = re.split(r"(?:ACCEPTANCE|REFINEMENT)_ASSUMPTIONS", audit, maxsplit=1)[0]
    if "Closed under the global context" in audit:
        return set()
    if "Axioms:" not in audit:
        raise ValueError("unrecognized assumption audit")
    names = set(re.findall(r"^([A-Za-z_][A-Za-z0-9_.]*)\s*:", audit, re.M))
    names.discard("Axioms")
    if not names:
        raise ValueError("empty/unrecognized axiom list")
    return names


def run_stage(command: list[str], log: Path, timeout: float) -> tuple[subprocess.CompletedProcess, bool]:
    """Stream diagnostics live, preserving separate audit stdout/stderr.

    Coq commands and deadlines are unchanged. A partial live log is diagnostic
    evidence, never a successful terminal result. Readers drain both pipes so
    a large error message cannot block the prover on a full stderr pipe.
    """
    stdout, stderr = [], []
    lock = threading.Lock()
    with log.open('wb') as output:
        process = subprocess.Popen(command, cwd=framework.ROOT,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   start_new_session=True)
        def capture(stream, chunks):
            with stream:
                for line in iter(stream.readline, b''):
                    chunks.append(line)
                    with lock:
                        output.write(line)
                        output.flush()
        readers = [threading.Thread(target=capture,args=(stream,chunks))
                   for stream,chunks in [(process.stdout,stdout),(process.stderr,stderr)]]
        for reader in readers:reader.start()
        timed_out = False
        deadline = time.monotonic()+timeout
        try:
            process.wait(timeout=max(0,deadline-time.monotonic()))
            for reader in readers:reader.join(timeout=max(0,deadline-time.monotonic()))
            if any(reader.is_alive() for reader in readers):
                raise subprocess.TimeoutExpired(command,timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            try:os.killpg(process.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            process.wait()
        for reader in readers:reader.join()
    errors = 'replace' if timed_out else 'strict'
    def text(chunks):
        # Match the previous text=True universal-newline API for audit parsers.
        return b''.join(chunks).decode(errors=errors).replace('\r\n','\n').replace('\r','\n')
    result = subprocess.CompletedProcess(command,124 if timed_out else process.returncode,
        text(stdout),text(stderr))
    return result, timed_out


def check(manifest: dict, provider: str, output: Path, stage_timeout: float = 1200) -> dict:
    if stage_timeout <= 0:
        raise ValueError("stage timeout must be positive")
    source = render_harness(manifest, provider)
    output.mkdir(parents=True, exist_ok=True)
    source_path = output / "AcceptedCPU.v"
    if source_path.exists() or (output / "AcceptedCPU.vo").exists():
        raise ValueError("use a fresh output directory; preserve earlier attempts and artifacts")
    source_path.write_text(source)
    flags = list(framework.FLAGS)
    for binding in manifest.get("coq_load_paths", []):
        flags += ["-R", binding["directory"], binding["namespace"]]
    flags += ["-R", str(output.resolve()), "CPUAcceptance"]
    report = {"design": manifest["design"], "provider": provider,
              "pinned_target": manifest["pinned_target"],
              "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
              "framework_manifest_sha256": hashlib.sha256(
                  json.dumps(manifest, sort_keys=True).encode()).hexdigest(),
              "structured_provider_arguments": manifest["certificate_harness"].get(
                  "provider_applications", {}).get(provider),
              "accepted": False, "scope": manifest["verification_scope"],
              "stage_timeout_seconds": stage_timeout,
              "kernel_scope": "own generated binding; imports must be previously checked providers",
              "claim": "exact pinned certificate and derived infinite ITree theorem; not RTL translation proof",
              "refinement_artifact": "CPUAcceptance.AcceptedCPU.acceptance_infinite_refinement"}
    start = time.monotonic()
    compiled, timed_out = run_stage([str(framework.ROOT / "_opam/bin/coqc"), "-q", *flags,
                                    str(source_path.resolve())], output / "coqc.log", stage_timeout)
    report["coqc_exit"] = compiled.returncode
    report["coqc_timed_out"] = timed_out
    report["coqc_seconds"] = time.monotonic() - start
    if compiled.returncode == 0:
        try:
            certificate_assumptions = parse_assumptions(compiled.stdout)
            refinement_assumptions = parse_assumptions(compiled.stdout, "REFINEMENT_ASSUMPTIONS")
            assumptions = certificate_assumptions | refinement_assumptions
            report["assumptions"] = sorted(assumptions)
            report["certificate_assumptions"] = sorted(certificate_assumptions)
            report["refinement_assumptions"] = sorted(refinement_assumptions)
            if assumptions - ALLOWED_AXIOMS:
                raise ValueError("new/unapproved proof assumptions")
            start = time.monotonic()
            checked, timed_out = run_stage([str(framework.ROOT / "_opam/bin/coqchk"), "-silent",
                                           *flags, "-norec", "CPUAcceptance.AcceptedCPU"],
                                          output / "coqchk.log", stage_timeout)
            report["coqchk_exit"] = checked.returncode
            report["coqchk_timed_out"] = timed_out
            report["coqchk_seconds"] = time.monotonic() - start
            report["accepted"] = checked.returncode == 0
        except ValueError as exc:
            report["audit_error"] = str(exc)
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--design", required=True)
    parser.add_argument("--provider", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--stage-timeout", type=float, default=1200,
                        help="seconds per coqc/coqchk stage; no automatic retry (default: 1200)")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9_-]+", args.design):
        parser.error("invalid design name")
    manifest = framework.load_manifest(framework.ROOT / "framework/designs" / (args.design + ".json"))
    report = check(manifest, args.provider, args.output, args.stage_timeout)
    print(json.dumps(report, indent=2))
    return 0 if report["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
