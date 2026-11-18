#!/usr/bin/env python3
"""[incr-compile experiment copy of tools/cpu_chain_replay.py: reuse from a substituted baseline, affected = changed files
+ dependents.] Replay a whole Coq proof chain from scratch in a sandbox, with profiling.

Given a target module (the final theorem file) and its loadpaths, the tool
  1. computes the transitive dependency closure with ``coqdep`` over ALL
     loadpaths (``src``/Pfv included); only files under ``_opam`` and ``dep``
     (coqutil, riscv-coq) are treated as external, never-changing libraries;
  2. copies the closure's ``.v`` sources into ``OUT/sandbox`` (one directory
     per loadpath entry), optionally replacing a module by a mutant file;
  3. generates a Makefile from ``coqdep`` run on the sandbox and builds it with
     ``make -jN``; every file is compiled by ``coqc -time`` through this script
     (``--compile-one``), which records wall time, user/sys CPU and peak RSS;
  4. runs ``coqchk -silent -norec`` on the target and ``Print Assumptions`` on
     the given export names (only functional_extensionality_dep is accepted);
  5. writes ``OUT/report.json`` and deletes ``.vo``/``.glob`` unless
     ``--keep-objects``.

``--stop-on-first-error`` kills the build at the first coqc failure and records
the failing file and the error text.  Nothing outside OUT is written.

``--design-root MODULE`` (repeatable) marks the design-dependent subset: the
closure files that transitively import one of the given design AST modules.
Files, lines, CPU sum and critical path are reported for that subset and for
the rest.  ``--analyze-subset RUN_DIR`` recomputes this from an existing run
(its Makefile and report.json) without rebuilding.

``--reuse-from BASELINE_DIR`` (a run built with --keep-objects and no
substitution) copies the objects of every closure file that does not
transitively import a substituted module, after checking that its source is
byte-identical to the baseline's; only the affected files are compiled.  The
dependency list of a substituted file is re-read from the mutant; it may only
use modules that are already in the closure.

Usage:
  cpu_chain_replay.py --target Pfv.Ex.External.DarkSkeletonFill \\
      --providers providers.json --out-dir results/r-chain-replay-X-aN \\
      [-R DIR NS ...] [--substitute Dark38.DarkRISCV38DerivedAST=mutant.v] \\
      [--assumptions DarkSkeletonFill.filled ...] [-j 32] [--stop-on-first-error]
"""
import argparse
import collections
import hashlib
import json
import os
import pathlib
import re
import resource
import shlex
import shutil
import signal
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"FunctionalExtensionality.functional_extensionality_dep"}
DEFAULT_ASSUMPTIONS_FILE_NAME = "Assumptions"
SELF = pathlib.Path(__file__).resolve()


def sha256_file(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def count_lines(path):
    with open(path, "rb") as f:
        return sum(1 for _ in f)


# ---------------------------------------------------------------- processes

def run_timed(cmd, log_path, cwd=None, env=None, timeout=None, unlimited_stack=False):
    """Run cmd, write stdout+stderr to log_path, return timing and exit info.

    Peak RSS and CPU come from wait4(), the same kernel source as
    ``/usr/bin/time -v`` (which is not installed everywhere)."""
    start = time.time()
    with open(log_path, "wb") as log:
        preexec = None
        if unlimited_stack:
            def preexec():
                _, hard = resource.getrlimit(resource.RLIMIT_STACK)
                resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))
        proc = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=log,
                                stderr=subprocess.STDOUT, preexec_fn=preexec)
        timed_out = False
        while True:
            pid, status, usage = os.wait4(proc.pid, os.WNOHANG)
            if pid:
                break
            if timeout is not None and time.time() - start > timeout:
                timed_out = True
                proc.kill()
                pid, status, usage = os.wait4(proc.pid, 0)
                break
            time.sleep(0.05)
        proc.returncode = os.waitstatus_to_exitcode(status)
    return dict(exit=proc.returncode, timed_out=timed_out,
                wall_s=round(time.time() - start, 3),
                user_s=round(usage.ru_utime, 3), sys_s=round(usage.ru_stime, 3),
                max_rss_kb=usage.ru_maxrss,
                started=start, ended=time.time())


def compile_one(argv):
    """Worker used by the generated Makefile: --compile-one META LOG FLAG FILE COQC -- ARGS."""
    meta, log, flag, source, coqc = argv[:5]
    flags = argv[6:] if len(argv) > 5 and argv[5] == "--" else argv[5:]
    result = run_timed([coqc, "-time"] + flags + [source], log)
    result["file"] = source
    pathlib.Path(meta).write_text(json.dumps(result))
    if result["exit"] != 0:
        try:
            fd = os.open(flag, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            os.write(fd, source.encode())
            os.close(fd)
        except FileExistsError:
            pass
    return result["exit"]


# ----------------------------------------------------------------- loadpaths

def remap_directory(directory):
    """providers.json files record the original build path; map it to this tree."""
    path = pathlib.Path(directory)
    if not path.is_absolute():
        path = ROOT / path
    if path.exists():
        return path.resolve()
    text = str(directory)
    for marker, base in ((ROOT.name + "/", ROOT),):
        if marker in text:
            candidate = base / text.split(marker, 1)[1]
            if candidate.exists():
                return candidate.resolve()
    return path


def load_loadpaths(providers, extra, base=True):
    """Return list of (directory Path, namespace).  Base loadpaths come first."""
    entries = []
    if base:
        entries += [(ROOT / "src", "Pfv"),
                    (ROOT / "dep/coqutil/src/coqutil", "coqutil"),
                    (ROOT / "dep/riscv-coq/src/riscv", "riscv")]
    for provider in providers or []:
        data = json.loads(pathlib.Path(provider).read_text())
        for item in data:
            entries.append((remap_directory(item["directory"]), item["namespace"]))
    for directory, namespace in extra or []:
        entries.append((remap_directory(directory), namespace))
    seen, result = set(), []
    for directory, namespace in entries:
        directory = pathlib.Path(directory).resolve()
        key = (str(directory), namespace)
        if key not in seen:
            seen.add(key)
            result.append((directory, namespace))
    return result


def is_under(path, parent):
    try:
        pathlib.Path(path).resolve().relative_to(pathlib.Path(parent).resolve())
        return True
    except ValueError:
        return False


def logical_name(path, loadpaths):
    """Logical module name of a .v file, using the longest matching loadpath."""
    best = None
    for directory, namespace in loadpaths:
        if is_under(path, directory):
            if best is None or len(str(directory)) > len(str(best[0])):
                best = (directory, namespace)
    if best is None:
        return None
    rel = pathlib.Path(path).resolve().relative_to(best[0]).with_suffix("")
    return ".".join([best[1]] + list(rel.parts))


def resolve_module(spec, loadpaths):
    """Accept a file path or a logical module name; return the .v path."""
    candidate = pathlib.Path(spec)
    if spec.endswith(".v"):
        candidate = candidate if candidate.is_absolute() else pathlib.Path.cwd() / candidate
        if candidate.exists():
            return candidate.resolve()
        candidate = ROOT / spec
        if candidate.exists():
            return candidate.resolve()
        raise SystemExit(f"cannot find file {spec}")
    for directory, namespace in loadpaths:
        if spec == namespace or spec.startswith(namespace + "."):
            rel = spec[len(namespace):].lstrip(".").replace(".", "/")
            found = directory / (rel + ".v")
            if found.exists():
                return found.resolve()
    raise SystemExit(f"cannot resolve module {spec} in the given loadpaths")


# -------------------------------------------------------------------- coqdep

def coqdep_args(loadpaths):
    args = []
    for directory, namespace in loadpaths:
        args += ["-R", str(directory), namespace]
    return args


def parse_coqdep(text, cwd):
    """Parse coqdep output; return {v_file: [dep .v files]} for .vo rules only."""
    text = text.replace("\\\n", " ")
    result = {}
    for line in text.splitlines():
        if ":" not in line:
            continue
        targets, deps = line.split(":", 1)
        first = targets.split()[0] if targets.split() else ""
        if not first.endswith(".vo"):
            continue
        tokens = deps.split()
        if not tokens or not tokens[0].endswith(".v"):
            continue
        base = pathlib.Path(cwd)
        source = (base / tokens[0]).resolve()
        result[source] = [(base / t).resolve().with_suffix(".v")
                          for t in tokens[1:] if t.endswith(".vo")]
    return result


def run_coqdep(files, loadpaths, coqdep, cwd):
    proc = subprocess.run([str(coqdep)] + coqdep_args(loadpaths) + [str(f) for f in files],
                          cwd=cwd, capture_output=True, text=True)
    if proc.returncode:
        raise SystemExit(f"coqdep failed: {proc.stderr[-2000:]}")
    return parse_coqdep(proc.stdout, cwd)


def closure(target, loadpaths, coqdep, externals, extra_requires=None):
    """Transitive closure over non-external files.  Returns {file: [deps]}.

    extra_requires maps a file to library files that its original build loaded
    with ``coqc -require`` (invisible to coqdep); they count as dependencies."""
    extra_requires = extra_requires or {}
    graph, external_deps = {}, set()
    frontier = [target]
    while frontier:
        batch = [f for f in frontier if f not in graph]
        frontier = []
        if not batch:
            break
        deps = run_coqdep(batch, loadpaths, coqdep, ROOT)
        for source in batch:
            if source not in deps:
                raise SystemExit(f"coqdep gave no rule for {source}")
            mine = []
            for dep in deps[source]:
                if any(is_under(dep, e) for e in externals):
                    external_deps.add(dep)
                    continue
                mine.append(dep)
                frontier.append(dep)
            for lib in extra_requires.get(source, []):
                if lib not in mine:
                    mine.append(lib)
                    frontier.append(lib)
            graph[source] = mine
    return graph, sorted(external_deps)


# ------------------------------------------------------------------- sandbox

def build_sandbox(graph, loadpaths, out_dir, externals, substitutions):
    """Copy the closure into out_dir/sandbox; return (mapping, sandbox loadpaths)."""
    sandbox = out_dir / "sandbox"
    internal = [(d, n) for d, n in loadpaths if not any(is_under(d, e) for e in externals)]
    roots = {}
    for index, (directory, namespace) in enumerate(internal):
        roots[(directory, namespace)] = sandbox / f"{index:02d}_{namespace}"
    mapping = {}
    for source in sorted(graph):
        best = None
        for (directory, namespace), target_dir in roots.items():
            if is_under(source, directory):
                if best is None or len(str(directory)) > len(str(best[0])):
                    best = (directory, target_dir)
        if best is None:
            raise SystemExit(f"{source} is not under any internal loadpath")
        destination = best[1] / source.resolve().relative_to(best[0])
        destination.parent.mkdir(parents=True, exist_ok=True)
        replacement = substitutions.get(source)
        shutil.copyfile(replacement if replacement else source, destination)
        mapping[source] = destination
    used = {d for d in mapping.values()}
    sandbox_loadpaths = [(target_dir, namespace) for (directory, namespace), target_dir
                         in roots.items() if target_dir.exists()]
    externals_lp = [(d, n) for d, n in loadpaths if any(is_under(d, e) for e in externals)]
    return mapping, sandbox_loadpaths, externals_lp, used


def critical_path(order_deps, wall):
    """Longest path (seconds) through the dependency DAG; returns (seconds, [files])."""
    best = {}

    def visit(node, stack=()):
        if node in best:
            return best[node]
        value = (wall.get(node, 0.0), [node])
        for dep in order_deps.get(node, []):
            if dep in stack:
                continue
            sub = visit(dep, stack + (node,))
            if sub[0] + wall.get(node, 0.0) > value[0]:
                value = (sub[0] + wall.get(node, 0.0), sub[1] + [node])
        best[node] = value
        return value

    sys.setrecursionlimit(max(10000, len(order_deps) * 4))
    top = max((visit(n) for n in order_deps), default=(0.0, []))
    return round(top[0], 3), top[1]


# ---------------------------------------------------------------- assumptions

def parse_assumptions(text):
    """Parse the output of Print Assumptions; return {name: [axioms] | 'closed'}."""
    result, current = {}, None
    lines = text.splitlines()
    index = 0
    while index < len(lines):
        line = lines[index]
        if line.startswith("Closed under the global context"):
            result.setdefault(len(result), [])
        elif line.startswith("Axioms:"):
            axioms = []
            index += 1
            while (index < len(lines) and lines[index].strip()
                   and not lines[index].startswith(("Axioms:", "Closed under"))):
                if not lines[index].startswith((" ", "\t")):
                    axioms.append(lines[index].split(" : ", 1)[0].strip())
                index += 1
            result[len(result)] = axioms
            continue
        index += 1
    return [result[k] for k in sorted(result)]


def error_text(log_path, limit=60):
    try:
        lines = pathlib.Path(log_path).read_text(errors="replace").splitlines()
    except OSError:
        return ""
    start = 0
    for index, line in enumerate(lines):
        if line.startswith("Error") or "Error:" in line:
            start = max(0, index - 3)
            break
    else:
        start = max(0, len(lines) - limit)
    return "\n".join(lines[start:start + limit])


# ----------------------------------------------------- subsets and reuse

def reverse_reach(roots, deps):
    """Roots plus every node that transitively depends on a root."""
    users = collections.defaultdict(set)
    for node, node_deps in deps.items():
        for dep in node_deps:
            users[dep].add(node)
    seen, stack = set(), [r for r in roots if r in deps]
    while stack:
        node = stack.pop()
        if node not in seen:
            seen.add(node)
            stack.extend(users[node])
    return seen


def subset_stats(nodes, deps, wall, cpu, lines, name=str):
    """Size, CPU sum and critical path (inside the subset) of a set of files."""
    nodes = set(nodes)
    inner = {n: [d for d in deps.get(n, []) if d in nodes] for n in nodes}
    seconds, path = critical_path(inner, wall)
    return dict(files=len(nodes), lines=sum(lines.get(n, 0) for n in nodes),
                cpu_sum_s=round(sum(cpu.get(n, 0.0) for n in nodes), 3),
                critical_path_s=seconds, critical_path=[name(n) for n in path])


def analyze_subset(run_dir, roots):
    """Recompute the design-dependent subset of an existing run from its files."""
    run_dir = pathlib.Path(run_dir).resolve()
    report = json.loads((run_dir / "report.json").read_text())
    sandbox = run_dir / "sandbox"
    entries = {e["file"]: e for e in report["per_file"]}
    deps = {rel: [] for rel in entries}
    for line in (run_dir / "Makefile").read_text().splitlines():
        match = re.match(r"^(\S+)\.vo: (\S+\.v)\s*(.*)$", line)
        if match:
            rel = str(pathlib.Path(match.group(2)).relative_to(sandbox))
            deps[rel] = [str(pathlib.Path(t).relative_to(sandbox).with_suffix(".v"))
                         for t in match.group(3).split() if t.endswith(".vo")]
    by_module = {e["module"]: rel for rel, e in entries.items()}
    root_files = []
    for root in roots:
        if root not in by_module:
            raise SystemExit(f"design root {root} is not in the closure of {run_dir}")
        root_files.append(by_module[root])
    design = reverse_reach(root_files, deps)
    rest = set(entries) - design
    wall = {rel: e.get("wall_s", 0.0) for rel, e in entries.items()}
    cpu = {rel: e.get("user_s", 0.0) + e.get("sys_s", 0.0) for rel, e in entries.items()}
    lines = {rel: e["lines"] for rel, e in entries.items()}
    return dict(design_roots=list(roots),
                design_dependent=subset_stats(design, deps, wall, cpu, lines),
                rest=subset_stats(rest, deps, wall, cpu, lines),
                design_dependent_files=sorted(design))


def reuse_objects(base_dir, out_dir, files, affected, deps):
    """Copy baseline objects for unaffected files; refuse unless sources are identical."""
    base_dir = pathlib.Path(base_dir).resolve()
    base_report = json.loads((base_dir / "report.json").read_text())
    # incr copy: a substituted baseline is allowed (the previous design version); every reused file must still be
    # byte-identical to the baseline's source (checked below), and 'affected' covers every file that differs.
    if not base_report.get("build_ok"):
        raise SystemExit("--reuse-from needs a successful baseline run")
    sandbox, reused, saved = out_dir / "sandbox", {}, 0.0
    order, seen = [], set()

    def visit(node):
        if node not in seen:
            seen.add(node)
            for dep in deps[node]:
                visit(dep)
            order.append(node)

    sys.setrecursionlimit(max(10000, len(files) * 4))
    for node in files:
        visit(node)
    stamp = time.time_ns()
    for index, node in enumerate(order):
        if node in affected:
            continue
        rel = node.relative_to(sandbox)
        old = base_dir / "sandbox" / rel
        if not old.is_file() or sha256_file(old) != sha256_file(node):
            raise SystemExit(f"refusing reuse: {rel} differs from the baseline source")
        if not old.with_suffix(".vo").is_file():
            raise SystemExit(f"baseline has no object for {rel} (built without --keep-objects?)")
        for suffix in (".vo", ".vos", ".vok", ".glob"):
            if old.with_suffix(suffix).is_file():
                shutil.copyfile(old.with_suffix(suffix), node.with_suffix(suffix))
        os.utime(node.with_suffix(".vo"), ns=(stamp + index * 1000, stamp + index * 1000))
        key = str(rel).replace("/", "__")
        meta = base_dir / "meta" / (key + ".json")
        baseline_wall = json.loads(meta.read_text())["wall_s"] if meta.exists() else 0.0
        reused[node] = baseline_wall
    return reused


# --------------------------------------------------------------------- main

# Two-phase build phases: name -> (object suffix made, suffix of dependencies read, extra coqc flags).
# vos: statements only (opaque proofs skipped), a sequential chain.
# vok: every proof checked against the .vos of the dependencies; no ordering among files.
# vio: statements only, proofs suspended in the .vio (input of -schedule-vio2vo).
PHASES = {
    "vos": (".vos", ".vos", ["-vos", "-no-glob"]),
    "vok": (".vok", ".vos", ["-vok", "-no-glob"]),
    "vio": (".vio", ".vio", ["-vio", "-no-glob"]),
}


def phase_key(rel, phase):
    return str(rel).replace("/", "__") + ("." + phase if phase else "")


def write_makefile(path, order, deps_sandbox, flags, coqc, out_dir, file_flags=None, phase=None):
    """Makefile with one rule per file; phase None is the normal one-phase .vo build."""
    file_flags = file_flags or {}
    suffix, dep_suffix, extra = PHASES[phase] if phase else (".vo", ".vo", [])
    meta_dir, log_dir = out_dir / "meta", out_dir / "logs"
    flag = out_dir / "failed.flag"
    lines = [".SUFFIXES:", "COQFLAGS := " + " ".join(shlex.quote(f) for f in flags + extra), ""]
    lines.append("all: " + " ".join(str(f.with_suffix(suffix)) for f in order))
    lines.append("")
    for f in order:
        key = phase_key(f.relative_to(out_dir / "sandbox"), phase)
        deps = " ".join(str(d.with_suffix(dep_suffix)) for d in deps_sandbox[f])
        lines.append(f"{f.with_suffix(suffix)}: {f} {deps}")
        lines.append(f"\t@{shlex.quote(sys.executable)} {shlex.quote(str(SELF))} --compile-one "
                     f"{meta_dir / (key + '.json')} {log_dir / (key + '.log')} {flag} "
                     f"{f} {shlex.quote(str(coqc))} -- $(COQFLAGS)"
                     + "".join(" " + shlex.quote(x) for x in file_flags.get(f, [])))
    path.write_text("\n".join(lines) + "\n")


def run_make(makefile, out_dir, jobs, stop_on_first_error):
    """Run make; return (wall_s, make returncode).  The failed.flag file stops the build early."""
    flag = out_dir / "failed.flag"
    cmd = ["make", "-f", str(makefile), f"-j{jobs}"] + ([] if stop_on_first_error else ["-k"])
    start = time.time()
    killed = False
    with open(str(makefile) + ".log", "wb") as log:
        make = subprocess.Popen(cmd, cwd=out_dir, stdout=log, stderr=subprocess.STDOUT,
                                start_new_session=True)
        while make.poll() is None:
            if stop_on_first_error and flag.exists() and not killed:
                killed = True
                os.killpg(make.pid, signal.SIGTERM)
                time.sleep(1.0)
                try:
                    os.killpg(make.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            time.sleep(0.1)
    if killed:
        try:
            os.killpg(make.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    return round(time.time() - start, 3), make.returncode


def peak_concurrent_rss_kb(entries):
    """Upper bound of the summed max RSS of simultaneously running files (needs started/ended)."""
    events = []
    for e in entries:
        if "started" in e and "ended" in e:
            events.append((e["started"], 1, e["max_rss_kb"]))
            events.append((e["ended"], 0, -e["max_rss_kb"]))
    events.sort()
    cur = best = 0
    for _, _, delta in events:
        cur += delta
        best = max(best, cur)
    return best


def collect_phase(out_dir, sandbox_files, sandbox_lp, phase, reused):
    """Per-file result of one make phase from meta/*.json; returns (entries by file, wall by file)."""
    per_file, wall = {}, {}
    for dest in sandbox_files:
        rel = dest.relative_to(out_dir / "sandbox")
        key = phase_key(rel, phase)
        meta = out_dir / "meta" / (key + ".json")
        entry = dict(file=str(rel), module=logical_name(dest, sandbox_lp), lines=count_lines(dest),
                     log=f"logs/{key}.log")
        entry["source_sha256"] = sha256_file(dest)
        if dest in reused:
            entry.update(exit=0, wall_s=0.0, user_s=0.0, sys_s=0.0, max_rss_kb=0, reused=True,
                         baseline_wall_s=reused[dest])
            wall[dest] = 0.0
        elif meta.exists():
            data = json.loads(meta.read_text())
            entry.update({k: data[k] for k in ("exit", "wall_s", "user_s", "sys_s", "max_rss_kb")})
            entry["started"], entry["ended"] = data["started"], data["ended"]
            wall[dest] = data["wall_s"]
        else:
            entry["exit"] = None
        per_file[str(dest)] = entry
    return per_file, wall


def merge_phases(phase_data, sandbox_files, out_dir):
    """One entry per file over all phases: exit is the first nonzero phase exit, None if a phase is missing."""
    merged, wall = {}, {}
    order = list(phase_data)
    for dest in sandbox_files:
        parts = {n: phase_data[n]["per_file"][str(dest)] for n in order}
        ran = {n: e for n, e in parts.items() if e["exit"] is not None}
        base = dict(next(iter(parts.values())))
        failed = [n for n, e in ran.items() if e["exit"] != 0]
        entry = {k: base[k] for k in ("file", "module", "lines", "source_sha256")}
        if failed:
            entry["exit"], entry["failed_phase"] = ran[failed[0]]["exit"], failed[0]
            entry["log"] = ran[failed[0]]["log"]
        else:
            entry["exit"] = 0 if len(ran) == len(order) else None
            entry["log"] = (ran[order[-1]] if ran else base)["log"]
        for k in ("wall_s", "user_s", "sys_s"):
            entry[k] = round(sum(e.get(k, 0.0) for e in ran.values()), 3)
        entry["max_rss_kb"] = max([e.get("max_rss_kb", 0) for e in ran.values()] or [0])
        if ran:
            entry["started"] = min(e["started"] for e in ran.values())
            entry["ended"] = max(e["ended"] for e in ran.values())
        entry["phases"] = {n: {k: e[k] for k in ("exit", "wall_s", "user_s", "sys_s", "max_rss_kb") if k in e}
                           for n, e in parts.items()}
        merged[str(dest)] = entry
        wall[dest] = phase_data[order[0]]["wall"].get(dest, 0.0)   # the sequential chain is phase 1
    return merged, wall


GUARANTEES = {
    "vos": dict(
        proofs_checked_by="coqc -vok (the Coq kernel at every Qed, inside coqc) against the .vos of the dependencies",
        real_vo_files=False, coqchk=False, print_assumptions=False,
        equivalent_to_one_phase_double_zero=False,
        notes=["Admitted / axioms are NOT detected (as with plain coqc); Print Assumptions needs real .vo",
               "no .vo is produced and nothing is independently re-checked by coqchk",
               "a dependency is seen only through its .vos: universe constraints of its opaque proofs and "
               "any other effect of a skipped proof body are not part of what dependents are checked against",
               "to accept a result use --two-phase vio or the one-phase build"]),
    "vio": dict(
        proofs_checked_by="coqc -schedule-vio2vo runs every suspended proof task and writes the real .vo",
        real_vo_files=True, coqchk=True, print_assumptions=True,
        equivalent_to_one_phase_double_zero="yes for the target when coqchk exit 0 and Print Assumptions only allow "
                                            "functional_extensionality_dep (coqchk -norec on the target, as in "
                                            "the one-phase build); use --coqchk-recursive for the whole closure",
        notes=["the .vo files come from vio2vo, not from plain coqc; coqchk is the independent check"]),
}


def summarize_two_phase(mode, phase_data, vio2vo, deps_sandbox, build_wall):
    phases, lower = {}, 0.0
    peak = 0
    for name, data in phase_data.items():
        entries = list(data["per_file"].values())
        wall = data["wall"]
        if name in ("vos", "vio"):
            cp, _ = critical_path(deps_sandbox, wall)
        else:
            cp = max(wall.values(), default=0.0)
        lower += cp
        peak = max(peak, peak_concurrent_rss_kb(entries))
        phases[name] = dict(wall_s=data["wall_s"], cpu_sum_s=round(sum(e.get("user_s", 0) + e.get("sys_s", 0) for e in entries), 3),
                            critical_path_s=cp, files_ok=sum(1 for e in entries if e["exit"] == 0),
                            files_failed=sum(1 for e in entries if e["exit"] not in (None, 0)),
                            files_not_built=sum(1 for e in entries if e["exit"] is None),
                            max_rss_kb=max((e.get("max_rss_kb", 0) for e in entries), default=0),
                            peak_concurrent_rss_kb_bound=peak_concurrent_rss_kb(entries))
    if vio2vo is not None:
        phases["vio2vo"] = {k: vio2vo[k] for k in ("exit", "wall_s", "user_s", "sys_s", "max_rss_kb")}
        phases["vio2vo"]["vo_missing"] = len(vio2vo["vo_missing"])
        lower += vio2vo["wall_s"]
    return dict(mode=mode, phases=phases, build_wall_s=build_wall, critical_path_lower_bound_s=round(lower, 3),
                peak_concurrent_rss_kb_bound=peak, guarantees=GUARANTEES[mode])


def parse_args(argv):
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--target", help="logical module or .v file")
    p.add_argument("--providers", action="append", default=[], help="providers.json (list of directory/namespace)")
    p.add_argument("-R", dest="extra", nargs=2, action="append", default=[], metavar=("DIR", "NS"))
    p.add_argument("--no-base-loadpaths", action="store_true", help="do not add Pfv/coqutil/riscv")
    p.add_argument("--substitute", action="append", default=[], metavar="MODULE_OR_FILE=MUTANT.v")
    p.add_argument("--require-lib", action="append", default=[], metavar="MODULE=LIBMODULE",
                   help="MODULE was originally compiled with coqc -require LIBMODULE (not visible to "
                        "coqdep): add LIBMODULE to the closure as its dependency and pass -require")
    p.add_argument("--out-dir")
    p.add_argument("--design-root", action="append", default=[], metavar="MODULE",
                   help="design AST module; report the subset of files importing it")
    p.add_argument("--reuse-from", metavar="BASELINE_DIR",
                   help="copy objects of unaffected files from a --keep-objects baseline")
    p.add_argument("--analyze-subset", metavar="RUN_DIR",
                   help="recompute the design subset of an existing run (needs --design-root)")
    p.add_argument("-j", "--jobs", type=int, default=32)
    p.add_argument("--assumptions", nargs="*", default=[], help="names for Print Assumptions (after Require Import TARGET)")
    p.add_argument("--stop-on-first-error", action="store_true")
    p.add_argument("--keep-objects", action="store_true")
    p.add_argument("--two-phase", choices=["vos", "vio"],
                   help="vos: phase 1 coqc -vos in dependency order, phase 2 coqc -vok on all files in "
                        "parallel; a fast 'all proofs check' result with NO .vo, NO coqchk, NO Print "
                        "Assumptions.  vio: phase 1 coqc -vio in dependency order, phase 2 "
                        "coqc -schedule-vio2vo turns every .vio into a real .vo (proofs run in parallel), "
                        "then coqchk and Print Assumptions run on the real .vo exactly as in the "
                        "one-phase build")
    p.add_argument("--vio2vo-stack", choices=["soft", "hard"], default="hard",
                   help="stack limit of the vio2vo step: 'hard' raises the soft limit to the hard limit "
                        "(vio2vo proof workers overflow the default 8 MB stack on deep proofs that the "
                        "one-phase coqc compiles; seen on CV32E40PAddiDecoder.v); 'soft' keeps ulimit -s")
    p.add_argument("--coqchk-recursive", action="store_true",
                   help="run coqchk without -norec (checks the whole closure, not only the target)")
    p.add_argument("--skip-coqchk", action="store_true")
    p.add_argument("--prepare-only", action="store_true", help="closure, sandbox and Makefile only")
    p.add_argument("--coq-bin", default=str(ROOT / "_opam/bin"))
    p.add_argument("--external-dir", action="append", default=[], help="extra never-changing library dirs")
    return p.parse_args(argv)


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if argv and argv[0] == "--compile-one":
        return compile_one(argv[1:])
    args = parse_args(argv)
    if args.analyze_subset:
        if not args.design_root:
            raise SystemExit("--analyze-subset needs --design-root")
        result = analyze_subset(args.analyze_subset, args.design_root)
        (pathlib.Path(args.analyze_subset) / "design_subset.json").write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps({k: v for k, v in result.items() if k != "design_dependent_files"}, indent=2))
        return 0
    if not args.target or not args.out_dir:
        raise SystemExit("--target and --out-dir are required")
    out_dir = pathlib.Path(args.out_dir).resolve()
    if out_dir.exists():
        raise SystemExit(f"output dir {out_dir} already exists; never reuse a result dir")
    if " " in str(out_dir):
        raise SystemExit("output dir path must not contain spaces")
    coq_bin = pathlib.Path(args.coq_bin)
    coqc, coqdep, coqchk = coq_bin / "coqc", coq_bin / "coqdep", coq_bin / "coqchk"
    externals = [ROOT / "_opam", ROOT / "dep"] + [pathlib.Path(e).resolve() for e in args.external_dir]
    loadpaths = load_loadpaths(args.providers, args.extra, not args.no_base_loadpaths)
    started = time.time()

    target = resolve_module(args.target, loadpaths)
    target_logical = logical_name(target, loadpaths)
    extra_requires, require_names = {}, {}
    for spec in args.require_lib:
        user_spec, _, lib_spec = spec.partition("=")
        if not lib_spec:
            raise SystemExit(f"--require-lib needs MODULE=LIBMODULE, got {spec}")
        user_file, lib_file = resolve_module(user_spec, loadpaths), resolve_module(lib_spec, loadpaths)
        extra_requires.setdefault(user_file, []).append(lib_file)
        require_names.setdefault(user_file, []).append(logical_name(lib_file, loadpaths))
    graph, external_deps = closure(target, loadpaths, coqdep, externals, extra_requires)

    substitutions, substitution_info = {}, []
    for spec in args.substitute:
        original_spec, _, mutant = spec.partition("=")
        original = resolve_module(original_spec, loadpaths)
        if original not in graph:
            raise SystemExit(f"{original_spec} is not in the closure of {args.target}")
        mutant_path = pathlib.Path(mutant).resolve()
        if not mutant_path.is_file():
            raise SystemExit(f"mutant file {mutant} not found")
        substitutions[original] = mutant_path
        substitution_info.append(dict(module=logical_name(original, loadpaths),
                                      original=str(original), mutant=str(mutant_path),
                                      original_sha256=sha256_file(original),
                                      mutant_sha256=sha256_file(mutant_path)))
    substitution_hash = None
    if substitution_info:
        text = "\n".join(f"{i['module']}:{i['mutant_sha256']}" for i in sorted(substitution_info, key=lambda i: i["module"]))
        substitution_hash = hashlib.sha256(text.encode()).hexdigest()

    out_dir.mkdir(parents=True)
    for sub in ("logs", "meta"):
        (out_dir / sub).mkdir()
    mapping, sandbox_lp, external_lp, _ = build_sandbox(graph, loadpaths, out_dir, externals, substitutions)
    sandbox_files = sorted(mapping.values())
    reverse = {v: k for k, v in mapping.items()}

    # dependency graph of the sandbox, again from coqdep; mutants may not add files
    sb_deps = run_coqdep(sandbox_files, sandbox_lp + external_lp, coqdep, out_dir)
    for dest in sandbox_files:
        found = {d for d in sb_deps[dest] if not any(is_under(d, e) for e in externals)}
        known = set(mapping.values())
        found |= {mapping[l] for l in extra_requires.get(reverse[dest], [])}
        if not found <= known:
            raise SystemExit(f"{dest}: depends on modules outside the closure: {sorted(map(str, found - known))}")
        if reverse[dest] not in substitutions:
            expected = {mapping[d] for d in graph[reverse[dest]]}
            if found != expected:
                raise SystemExit(f"{dest}: sandbox dependencies differ from the original ones")
    deps_sandbox = {f: sorted(({d for d in sb_deps[f] if d in set(mapping.values())}
                               | {mapping[l] for l in extra_requires.get(reverse[f], [])}))
                    for f in sandbox_files}
    file_flags = {mapping[u]: [x for n in names for x in ("-require", n)]
                  for u, names in require_names.items()}

    design_nodes = None
    if args.design_root:
        roots = []
        for spec in args.design_root:
            root = resolve_module(spec, loadpaths)
            if root not in graph:
                raise SystemExit(f"design root {spec} is not in the closure of {args.target}")
            roots.append(mapping[root])
        design_nodes = reverse_reach(roots, deps_sandbox)
    affected = reverse_reach([mapping[o] for o in substitutions], deps_sandbox)
    reused = {}
    if args.reuse_from:
        if not substitutions:
            raise SystemExit("--reuse-from makes sense only together with --substitute")
        # incr copy: affected = files whose source differs from the baseline sandbox, plus their dependents
        base_sb = pathlib.Path(args.reuse_from).resolve() / "sandbox"
        changed = [n for n in sandbox_files
                   if not (base_sb / n.relative_to(out_dir / "sandbox")).is_file()
                   or sha256_file(base_sb / n.relative_to(out_dir / "sandbox")) != sha256_file(n)]
        affected = reverse_reach(changed, deps_sandbox)
        reused = reuse_objects(args.reuse_from, out_dir, sandbox_files, affected, deps_sandbox)

    flags = []
    for directory, namespace in sandbox_lp + external_lp:
        flags += ["-R", str(directory), namespace]
    makefile = out_dir / "Makefile"
    write_makefile(makefile, sandbox_files, deps_sandbox, flags, coqc, out_dir, file_flags)

    report = dict(target=args.target, target_module=target_logical, target_file=str(target),
                  out_dir=str(out_dir), jobs=args.jobs, stop_on_first_error=args.stop_on_first_error,
                  closure_files=len(graph), closure_lines=sum(count_lines(f) for f in graph),
                  external_dependencies=[str(p) for p in external_deps],
                  loadpaths=[[str(d), n] for d, n in loadpaths],
                  ast_substitutions=substitution_info, ast_substitution_hash=substitution_hash,
                  design_roots=args.design_root, require_libs=args.require_lib,
                  reuse=dict(baseline=args.reuse_from, reused_files=len(reused),
                             affected_files=len(affected)) if args.reuse_from else None)
    if args.prepare_only:
        report["prepared_only"] = True
        (out_dir / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        return 0

    # ---- build
    if args.two_phase and args.reuse_from:
        raise SystemExit("--two-phase cannot be combined with --reuse-from")
    phase_plan = {None: [None], "vos": ["vos", "vok"], "vio": ["vio"]}[args.two_phase]
    flag = out_dir / "failed.flag"
    build_start = time.time()
    phase_data = {}   # name -> dict(per_file, wall, make_rc, wall_s)
    for phase in phase_plan:
        if phase == "vok" and phase_data["vos"]["failed"] and args.stop_on_first_error:
            break
        mk = out_dir / ("Makefile" if phase is None else f"Makefile.{phase}")
        write_makefile(mk, sandbox_files, deps_sandbox, flags, coqc, out_dir, file_flags, phase)
        make_wall, make_rc = run_make(mk, out_dir, args.jobs, args.stop_on_first_error)
        entries, walls = collect_phase(out_dir, sandbox_files, sandbox_lp, phase, reused)
        phase_data[phase or "vo"] = dict(per_file=entries, wall=walls, make_rc=make_rc, wall_s=make_wall,
                                         failed=any(e["exit"] not in (None, 0) for e in entries.values()))
    vio2vo = None
    if args.two_phase == "vio" and not phase_data["vio"]["failed"] and phase_data["vio"]["make_rc"] == 0 \
            and all(e["exit"] == 0 for e in phase_data["vio"]["per_file"].values()):
        vio2vo = run_timed([str(coqc)] + flags + ["-schedule-vio2vo", str(args.jobs)]
                           + [str(f.with_suffix(".vio")) for f in sandbox_files],
                           out_dir / "vio2vo.log", cwd=out_dir,
                           unlimited_stack=args.vio2vo_stack == "hard")
        vio2vo["stack"] = args.vio2vo_stack
        vio2vo["error"] = error_text(out_dir / "vio2vo.log") if vio2vo["exit"] else None
        vio2vo["vo_missing"] = sorted(str(f.relative_to(out_dir / "sandbox")) for f in sandbox_files
                                      if not f.with_suffix(".vo").is_file())
    build_wall = round(time.time() - build_start, 3)
    make_ok = all(d["make_rc"] == 0 for d in phase_data.values())

    if args.two_phase is None:
        per_file, wall = phase_data["vo"]["per_file"], phase_data["vo"]["wall"]
    else:
        per_file, wall = merge_phases(phase_data, sandbox_files, out_dir)
    failures = sorted((e for e in per_file.values() if e["exit"] not in (None, 0)), key=lambda e: e["ended"])
    first_failure = None
    if failures:
        first = failures[0]
        first_failure = dict(file=first["file"], module=first["module"], original_file=str(reverse[sandbox_root_path(out_dir, first)]),
                             seconds_from_build_start=round(first["ended"] - build_start, 3),
                             error=error_text(out_dir / first["log"]))
        if first.get("failed_phase"):
            first_failure["phase"] = first["failed_phase"]
    elif vio2vo is not None and (vio2vo["exit"] or vio2vo["vo_missing"]):
        first_failure = dict(file=None, phase="vio2vo", error=vio2vo["error"], vo_missing=vio2vo["vo_missing"][:20])
    unbuilt = [e["file"] for e in per_file.values() if e["exit"] is None]
    if args.two_phase == "vio" and vio2vo is None:
        unbuilt = unbuilt or [e["file"] for e in per_file.values()]
    cp_seconds, cp_files = critical_path(deps_sandbox, wall)
    two_phase_info = None
    if args.two_phase:
        two_phase_info = summarize_two_phase(args.two_phase, phase_data, vio2vo, deps_sandbox, build_wall)
        cp_seconds = two_phase_info["critical_path_lower_bound_s"]
    build_ok = (not failures and not unbuilt and make_ok
                and (vio2vo is None or (vio2vo["exit"] == 0 and not vio2vo["vo_missing"])))

    # ---- coqchk and assumptions (only meaningful with real .vo files: not after --two-phase vos)
    chk = None
    assumptions = None
    if build_ok and args.two_phase != "vos":
        if not args.skip_coqchk:
            chk = run_timed([str(coqchk), "-silent"] + flags + ([] if args.coqchk_recursive else ["-norec"])
                            + [target_logical], out_dir / "coqchk.log", cwd=out_dir)
        if args.assumptions:
            driver = out_dir / f"{DEFAULT_ASSUMPTIONS_FILE_NAME}.v"
            body = f"Require Import {target_logical}.\n" + "".join(f"Print Assumptions {n}.\n" for n in args.assumptions)
            driver.write_text(body)
            run = run_timed([str(coqc)] + flags + [str(driver)], out_dir / "assumptions.log", cwd=out_dir)
            axioms = parse_assumptions((out_dir / "assumptions.log").read_text())
            flat = sorted({a for group in axioms for a in group})
            assumptions = dict(exit=run["exit"], names=args.assumptions, per_name=axioms,
                               axioms=flat, only_allowed=(run["exit"] == 0 and len(axioms) == len(args.assumptions)
                                                          and set(flat) <= ALLOWED_AXIOMS))
    cpu_sum = round(sum(e.get("user_s", 0) + e.get("sys_s", 0) for e in per_file.values())
                    + (vio2vo["user_s"] + vio2vo["sys_s"] if vio2vo else 0.0), 3)
    by_dest = {pathlib.Path(k): e for k, e in per_file.items()}
    subsets = {}
    if design_nodes is not None:
        cpu = {d: e.get("user_s", 0.0) + e.get("sys_s", 0.0) for d, e in by_dest.items()}
        lines = {d: e["lines"] for d, e in by_dest.items()}
        rel_name = lambda n: str(pathlib.Path(n).relative_to(out_dir / "sandbox"))
        subsets = dict(
            design_dependent=subset_stats(design_nodes, deps_sandbox, wall, cpu, lines, rel_name),
            rest=subset_stats(set(sandbox_files) - design_nodes, deps_sandbox, wall, cpu, lines, rel_name))
    reuse_info = None
    if args.reuse_from:
        reuse_info = dict(baseline=str(args.reuse_from),
                          reused=sorted(per_file[str(d)]["file"] for d in reused),
                          compiled=sorted(e["file"] for e in per_file.values() if not e.get("reused")),
                          baseline_wall_of_reused_s=round(sum(reused.values()), 3))
    slowest = sorted((e for e in per_file.values() if "wall_s" in e), key=lambda e: -e["wall_s"])[:20]
    report.update(
        build_ok=build_ok, build_wall_s=build_wall, total_wall_s=round(time.time() - started, 3),
        cpu_sum_s=cpu_sum, critical_path_s=cp_seconds,
        critical_path=[str(pathlib.Path(f).relative_to(out_dir / "sandbox")) for f in cp_files],
        files_built=sum(1 for e in per_file.values() if e["exit"] == 0 and not e.get("reused")),
        files_reused=len(reused), files_failed=len(failures),
        design_subset=subsets or None, reuse=reuse_info,
        files_not_built=len(unbuilt), first_failure=first_failure,
        coqchk=chk, assumptions=assumptions, two_phase=two_phase_info,
        coqchk_recursive=bool(args.coqchk_recursive),
        peak_concurrent_rss_kb_bound=(two_phase_info["peak_concurrent_rss_kb_bound"] if two_phase_info
                                      else peak_concurrent_rss_kb(per_file.values())),
        files_over_15_min=[e["file"] for e in per_file.values() if e.get("wall_s", 0) > 900],
        slowest_20=[dict(file=e["file"], wall_s=e["wall_s"], max_rss_kb=e["max_rss_kb"]) for e in slowest],
        per_file=sorted(per_file.values(), key=lambda e: e["file"]))
    for entry in report["per_file"]:
        entry.pop("started", None)
        entry.pop("ended", None)
    (out_dir / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    if not args.keep_objects:
        for pattern in ("*.vo", "*.vos", "*.vok", "*.vio", "*.glob", "*.aux"):
            for f in (out_dir).rglob(pattern):
                f.unlink()
    summary = dict(build_ok=build_ok, files=report["closure_files"], lines=report["closure_lines"],
                   wall_s=report["total_wall_s"], first_failure=(first_failure or {}).get("file"),
                   mode=args.two_phase or "one-phase",
                   coqchk_exit=None if chk is None else chk["exit"],
                   acceptance=("NOT coqchk-equivalent: proofs checked by coqc -vok only"
                               if args.two_phase == "vos" else None),
                   assumptions_ok=None if assumptions is None else assumptions["only_allowed"])
    print(json.dumps(summary))
    ok = build_ok and (chk is None or chk["exit"] == 0) and (assumptions is None or assumptions["only_allowed"])
    return 0 if ok else 1


def sandbox_root_path(out_dir, entry):
    return out_dir / "sandbox" / entry["file"]


if __name__ == "__main__":
    raise SystemExit(main())
