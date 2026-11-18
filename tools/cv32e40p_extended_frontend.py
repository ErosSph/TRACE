#!/usr/bin/env python3
"""Elaborate CV32E40P and emit the complete executable ExtendedSV NIR.

The Python/Verilator stage is deliberately treated as a translation-validation
boundary, not as a proof.  The emitted Rocq term contains every runtime
expression and statement.  Rocq checks the term against Lang.ExtendedSV and
all semantic/equivalence theorems are proved over that kernel-checked term.
The JSON sidecar records source/XML digests, coverage and provenance.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import tempfile
import xml.etree.ElementTree as ET
from collections import Counter
import heapq
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FLIST = ROOT / "experiments/cv32e40p/rv32i_noext.flist"
EXPR_TAGS = {
    "const", "varref", "sel", "and", "or", "xor", "add", "sub",
    "muls", "eq", "neq", "lt", "gt", "gts", "shiftl", "shiftr",
    "shiftrs", "not", "negate", "redor", "cond", "concat",
    "replicate", "extend", "extends",
}
STMT_TAGS = {"begin", "assign", "assigndly", "if", "case"}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_const(text: str) -> tuple[int, int, bool]:
    match = re.fullmatch(r"(\d+)'(s?)h([0-9a-fA-F]+)", text)
    if not match:
        raise ValueError(f"unsupported Verilator constant: {text}")
    width, signed, digits = match.groups()
    return int(width), int(digits, 16), bool(signed)


def loc_line(node: ET.Element) -> int:
    loc = node.get("loc", "")
    fields = loc.split(",")
    return int(fields[1]) if len(fields) > 1 and fields[1].isdigit() else 0


def source_port_order(source: str, module_name: str) -> list[str]:
    """Read simple ANSI/non-ANSI port headers, rejecting ambiguous syntax.

    Verilator 4 XML lists variables in declaration order, which is NOT port
    order for non-ANSI modules. Never resolve __pinNumberN using that list.
    This parsing is part of the existing trusted RTL elaboration boundary.
    """
    source = re.sub(r'"(?:\\.|[^"\\])*"|/\*.*?\*/|//[^\n]*',
                    lambda m: m[0] if m[0].startswith('"') else
                    re.sub(r'[^\n]', ' ', m[0]), source, flags=re.S)
    matches = list(re.finditer(r'\bmodule\s+' + re.escape(module_name) + r'\b', source))
    if len(matches) != 1:
        raise ValueError(f"ambiguous/missing source header for {module_name}")
    tail = source[matches[0].end():].lstrip()

    def group(text):
        if not text.startswith('('):
            raise ValueError(f"unsupported module header for {module_name}")
        depth = 0
        quoted = escaped = False
        for i, char in enumerate(text):
            if quoted:
                if escaped:
                    escaped = False
                elif char == '\\':
                    escaped = True
                elif char == '"':
                    quoted = False
            elif char == '"':
                quoted = True
            elif char == '(':
                depth += 1
            elif char == ')':
                depth -= 1
                if depth == 0:
                    return text[1:i], text[i+1:].lstrip()
        raise ValueError(f"unclosed module header for {module_name}")

    if tail.startswith('#'):
        _, tail = group(tail[1:].lstrip())
    header, tail = group(tail)
    if not tail.startswith(';') or re.search(r'`(?:if|else|endif|include|define)', header):
        raise ValueError(f"conditional/unsupported port header for {module_name}")
    # Supported dimensions contain no comma; complex array/default/interface
    # declarations fail below instead of guessing a port binding.
    ports = []
    for field in header.split(','):
        plain = re.sub(r'\[[^\[\],]*\]', ' ', field).strip()
        if re.search(r'[^\w\s`$]', plain):
            raise ValueError(f"unsupported positional port declaration: {field}")
        words = plain.split()
        if not words or not re.fullmatch(r'[A-Za-z_][\w$]*', words[-1]):
            raise ValueError(f"unsupported positional port declaration: {field}")
        ports.append(words[-1])
    if len(ports) != len(set(ports)):
        raise ValueError(f"duplicate port in {module_name}")
    return ports


@dataclass
class SignalInfo:
    id: int
    width: int
    path: str
    source_line: int
    direction: str


class Translator:
    def __init__(self, root: ET.Element, top: str = "cv32e40p_top"):
        self.top = top
        self.root = root
        self.netlist = root.find("netlist")
        if self.netlist is None:
            raise ValueError("Verilator XML has no netlist")
        self.modules = {m.get("name"): m for m in self.netlist.findall("module")}
        typetable = self.netlist.find("typetable")
        if typetable is None:
            raise ValueError("Verilator XML has no typetable")
        self.dtypes = {d.get("id"): d for d in typetable}
        self.signals: list[SignalInfo] = []
        self.processes: list[str] = []
        self.process_meta: list[dict] = []
        self.instances: list[dict] = []
        self.runtime_tags = Counter()
        self.unsupported: list[str] = []
        self.top_env: dict[str, SignalInfo] = {}
        self.comb_graph_metrics: dict = {}
        self.lfp_fuel = 256

    def dtype_width(self, dtype_id: str, seen: set[str] | None = None) -> int:
        seen = set() if seen is None else seen
        if dtype_id in seen:
            raise ValueError(f"cyclic dtype {dtype_id}")
        seen.add(dtype_id)
        node = self.dtypes.get(dtype_id)
        if node is None:
            raise ValueError(f"missing dtype {dtype_id}")
        if node.tag == "basicdtype":
            if "left" in node.attrib:
                return abs(int(node.get("left")) - int(node.get("right", "0"))) + 1
            return 32 if node.get("name") in {"int", "integer"} else 1
        if node.tag in {"refdtype", "enumdtype", "memberdtype"}:
            return self.dtype_width(node.get("sub_dtype_id"), seen)
        if node.tag == "packarraydtype":
            range_node = node.find("range")
            if range_node is None or len(range_node) != 2:
                raise ValueError(f"bad packed range for dtype {dtype_id}")
            left = parse_const(range_node[0].get("name"))[1]
            right = parse_const(range_node[1].get("name"))[1]
            return (abs(left - right) + 1) * self.dtype_width(node.get("sub_dtype_id"), seen)
        if node.tag == "structdtype":
            return sum(self.dtype_width(m.get("sub_dtype_id"), set(seen))
                       for m in node.findall("memberdtype"))
        raise ValueError(f"unsupported dtype node {node.tag} id={dtype_id}")

    def width(self, node: ET.Element) -> int:
        return self.dtype_width(node.get("dtype_id"))

    def expr(self, node: ET.Element, env: dict[str, SignalInfo]) -> str:
        self.runtime_tags[node.tag] += 1
        if node.tag not in EXPR_TAGS:
            raise ValueError(f"unsupported expression tag {node.tag} at {node.get('loc')}")
        w = self.width(node)
        children = list(node)
        if node.tag == "const":
            cw, value, _ = parse_const(node.get("name"))
            if cw != w:
                # Verilator sometimes assigns a context dtype.  The context
                # width is the executable result width.
                cw = w
            return f"EConst {cw} {value}"
        if node.tag == "varref":
            name = node.get("name")
            if name not in env:
                raise ValueError(f"unknown varref {name} at {node.get('loc')}")
            return f"EVar {w} {env[name].id}"
        if node.tag == "sel":
            return f"ESel {w} ({self.expr(children[0], env)}) ({self.expr(children[1], env)})"
        if node.tag == "concat":
            return f"EConcat {w} ({self.expr(children[0], env)}) ({self.expr(children[1], env)})"
        if node.tag == "replicate":
            count = parse_const(children[1].get("name"))[1]
            return f"EReplicate {w} {count} ({self.expr(children[0], env)})"
        if node.tag in {"extend", "extends"}:
            signed = "true" if node.tag == "extends" else "false"
            return f"EExtend {w} {signed} ({self.expr(children[0], env)})"
        unary = {"not": "UNot", "negate": "UNegate", "redor": "URedOr"}
        if node.tag in unary:
            return f"EUnary {w} {unary[node.tag]} ({self.expr(children[0], env)})"
        binary = {
            "and": "BAnd", "or": "BOr", "xor": "BXor", "add": "BAdd",
            "sub": "BSub", "muls": "BMul", "eq": "BEq", "neq": "BNeq",
            "lt": "BLtU", "gt": "BGtU", "gts": "BGtS",
            "shiftl": "BShiftL", "shiftr": "BShiftR", "shiftrs": "BShiftRS",
        }
        if node.tag in binary:
            return (f"EBinary {w} {binary[node.tag]} "
                    f"({self.expr(children[0], env)}) ({self.expr(children[1], env)})")
        if node.tag == "cond":
            return (f"ECond {w} ({self.expr(children[0], env)}) "
                    f"({self.expr(children[1], env)}) ({self.expr(children[2], env)})")
        raise AssertionError(node.tag)

    def lvalue(self, node: ET.Element, env: dict[str, SignalInfo]) -> str:
        if node.tag == "varref":
            info = env[node.get("name")]
            return f"LVar {self.width(node)} {info.id}"
        if node.tag == "sel":
            children = list(node)
            return (f"LSel {self.width(node)} ({self.lvalue(children[0], env)}) "
                    f"({self.expr(children[1], env)})")
        raise ValueError(f"unsupported lvalue {node.tag} at {node.get('loc')}")

    def stmt(self, node: ET.Element, env: dict[str, SignalInfo]) -> str:
        self.runtime_tags[node.tag] += 1
        if node.tag not in STMT_TAGS:
            raise ValueError(f"unsupported statement tag {node.tag} at {node.get('loc')}")
        children = [c for c in node if c.tag not in {"sentree", "var"}]
        if node.tag == "begin":
            return "SSeq [" + "; ".join(self.stmt(c, env) for c in children) + "]"
        if node.tag in {"assign", "assigndly"}:
            if len(children) != 2:
                raise ValueError(f"assignment arity at {node.get('loc')}")
            nba = "true" if node.tag == "assigndly" else "false"
            return (f"SAssign {nba} ({self.expr(children[0], env)}) "
                    f"({self.lvalue(children[1], env)})")
        if node.tag == "if":
            if len(children) not in {2, 3}:
                raise ValueError(f"if arity at {node.get('loc')}")
            no = self.stmt(children[2], env) if len(children) == 3 else "SSkip"
            return (f"SIf ({self.expr(children[0], env)}) "
                    f"({self.stmt(children[1], env)}) ({no})")
        if node.tag == "case":
            scrutinee = self.expr(children[0], env)
            arms = []
            for item in children[1:]:
                if item.tag != "caseitem":
                    raise ValueError(f"non-caseitem at {item.get('loc')}")
                ich = list(item)
                if len(ich) == 0:
                    arms.append("(None, SSkip)")
                elif len(ich) == 1:
                    if ich[0].tag in EXPR_TAGS:
                        arms.append(f"(Some ({self.expr(ich[0], env)}), SSkip)")
                    else:
                        arms.append(f"(None, {self.stmt(ich[0], env)})")
                elif len(ich) >= 2:
                    has_body = ich[-1].tag not in EXPR_TAGS
                    body = self.stmt(ich[-1], env) if has_body else "SSkip"
                    keys = ich[:-1] if has_body else ich
                    for key in keys:
                        arms.append(f"(Some ({self.expr(key, env)}), {body})")
            return f"SCase ({scrutinee}) [{'; '.join(arms)}]"
        raise AssertionError(node.tag)

    def add_process(self, kind: str, events: list[tuple[str, int]], body: str,
                    line: int, path: str, origin: str) -> None:
        evs = "; ".join(
            f"{{| event_edge := {edge}; event_signal := {signal} |}}"
            for edge, signal in events)
        term = (f"{{| process_kind := {kind}; process_events := [{evs}]; "
                f"process_body := {body}; process_source_line := {line} |}}")
        self.processes.append(term)
        readers = sorted({int(x) for x in re.findall(r"EVar\s+\d+\s+(\d+)", body)})
        writers = sorted({int(x) for x in re.findall(r"LVar\s+\d+\s+(\d+)", body)})
        self.process_meta.append({"index": len(self.processes) - 1, "kind": kind,
                                  "events": events, "line": line,
                                  "instance": path, "origin": origin,
                                  "readers": readers, "writers": writers})

    def reorder_combinational(self) -> None:
        """Topologically order the elaborated combinational dependency cone.

        This is not trusted for correctness: the complete reordered AST is
        still checked by Rocq and [lfp_checked] checks stability.  The order
        merely makes the executable LFP certificate small enough to check.
        """
        comb = [i for i, m in enumerate(self.process_meta) if m["kind"] == "Combinational"]
        writer_map: dict[int, list[int]] = {}
        for i in comb:
            for signal in self.process_meta[i]["writers"]:
                writer_map.setdefault(signal, []).append(i)
        edges = {i: set() for i in comb}
        indegree = {i: 0 for i in comb}
        for j in comb:
            for signal in self.process_meta[j]["readers"]:
                for i in writer_map.get(signal, []):
                    if i != j and j not in edges[i]:
                        edges[i].add(j)
                        indegree[j] += 1
        ready = [i for i in comb if indegree[i] == 0]
        heapq.heapify(ready)
        ordered = []
        while ready:
            i = heapq.heappop(ready)
            ordered.append(i)
            for j in sorted(edges[i]):
                indegree[j] -= 1
                if indegree[j] == 0:
                    heapq.heappush(ready, j)
        unresolved = [i for i in comb if indegree[i] != 0]
        ordered.extend(unresolved)
        noncomb = [i for i, m in enumerate(self.process_meta) if m["kind"] != "Combinational"]
        permutation = noncomb + ordered
        self.processes = [self.processes[i] for i in permutation]
        self.process_meta = [self.process_meta[i] for i in permutation]
        for i, meta in enumerate(self.process_meta):
            meta["index"] = i
        multiwriters = {str(signal): ids for signal, ids in writer_map.items() if len(ids) > 1}
        self.comb_graph_metrics = {
            "nodes": len(comb), "edges": sum(map(len, edges.values())),
            "acyclic_nodes": len(comb) - len(unresolved),
            "cyclic_or_unresolved_nodes": len(unresolved),
            "multiwriter_signal_count": len(multiwriters),
        }
        # One topologically ordered round is a candidate LFP for an acyclic
        # cone.  Cyclic cones retain a conservative bounded iteration.
        # The pinned CV32E40P cone reaches a checked fixed point from its
        # reset/zero acceptance seed after eight rounds.  This is not assumed:
        # CV32E40PReq38LFP.v recomputes the ninth round in the kernel.
        self.lfp_fuel = 1 if not unresolved else 8

    def module_items(self, node: ET.Element, env: dict[str, SignalInfo], path: str) -> None:
        for child in node:
            if child.tag in {"var", "instance"}:
                continue
            if child.tag == "contassign":
                body = self.stmt(ET.Element("assign", child.attrib), env) if False else None
                ch = list(child)
                if len(ch) != 2:
                    raise ValueError(f"continuous assignment arity at {child.get('loc')}")
                body = f"SAssign false ({self.expr(ch[0], env)}) ({self.lvalue(ch[1], env)})"
                self.add_process("Combinational", [], body, loc_line(child), path, "contassign")
            elif child.tag == "always":
                sentree = child.find("sentree")
                body_nodes = [c for c in child if c.tag != "sentree"]
                body = "SSeq [" + "; ".join(self.stmt(c, env) for c in body_nodes) + "]"
                if sentree is None:
                    self.add_process("Combinational", [], body, loc_line(child), path, "always_comb")
                else:
                    events = []
                    for sen in sentree.findall("senitem"):
                        edge = {"POS": "Posedge", "NEG": "Negedge",
                                "CHANGED": "AnyChange"}.get(sen.get("edgeType", "CHANGED"))
                        if edge is None or len(sen) != 1 or sen[0].tag != "varref":
                            raise ValueError(f"unsupported sensitivity at {sen.get('loc')}")
                        events.append((edge, env[sen[0].get("name")].id))
                    self.add_process("Sequential", events, body, loc_line(child), path, "always_event")
            elif child.tag == "initial":
                body = "SSeq [" + "; ".join(self.stmt(c, env) for c in child) + "]"
                self.add_process("Initial", [], body, loc_line(child), path, "initial")
            elif child.tag == "begin":
                self.module_items(child, env, path)
            elif child.tag in {"typedef", "enumitem"}:
                # Elaboration metadata: no runtime behavior remains.
                continue
            else:
                self.unsupported.append(f"module item {child.tag} at {child.get('loc')}")

    def instantiate(self, module_name: str, path: str) -> dict[str, SignalInfo]:
        module = self.modules[module_name]
        env: dict[str, SignalInfo] = {}
        def runtime_vars(node):
            # Function/task locals belong to their call, not hardware state.
            # Frontend extensions must lower the calls separately.
            if node.tag in {"func", "task"}:
                return
            if node.tag == "var":
                yield node
                return
            for child in node:
                yield from runtime_vars(child)
        # Verilator keeps variables declared in elaborated generate/procedural
        # blocks underneath <begin>. Ambiguous unqualified scoped names require
        # explicit lexical resolution; never silently overwrite a binding.
        for var in runtime_vars(module):
            name = var.get("name")
            if name in env:
                raise ValueError(f"ambiguous scoped variable {name} in {module_name}")
            info = SignalInfo(len(self.signals), self.width(var), f"{path}.{name}",
                              loc_line(var), var.get("dir", "internal"))
            self.signals.append(info)
            env[name] = info
        if path == self.top:
            self.top_env = env

        self.module_items(module, env, path)

        def scoped_instances(node, scope=()):
            for child in node:
                if child.tag == "instance":
                    yield scope, child
                elif child.tag == "begin":
                    name = child.get("name")
                    yield from scoped_instances(child, scope + ((name,) if name else ()))
        instances = list(scoped_instances(module))
        if {id(inst) for _, inst in instances} != {id(inst) for inst in module.iter("instance")}:
            raise ValueError(f"instance inside unsupported scope in {module_name}")
        child_paths = set()
        for scope, inst in instances:
            child_path = ".".join((path, *scope, inst.get("name")))
            if child_path in child_paths:
                raise ValueError(f"duplicate elaborated instance path {child_path}")
            child_paths.add(child_path)
            child_env = self.instantiate(inst.get("defName"), child_path)
            self.instances.append({"path": child_path, "module": inst.get("defName")})
            for port in inst.findall("port"):
                if len(port) == 0:
                    continue
                pname = port.get("name")
                if pname not in child_env and re.fullmatch(r'__pinNumber[1-9][0-9]*', pname or ''):
                    index = int(pname[len('__pinNumber'):])
                    if port.get('portIndex') != str(index):
                        raise ValueError('positional port name/index mismatch')
                    child_module = self.modules[inst.get('defName')]
                    file_id = child_module.get('loc', '').split(',')[0]
                    source_files = {f.get('id'): f.get('filename')
                                    for f in self.root.findall('./files/file')}
                    filename = source_files.get(file_id)
                    if not filename:
                        raise ValueError('positional port source location missing')
                    order = source_port_order(Path(filename).read_text(), child_module.get('origName', inst.get('defName')))
                    declared = {v.get('name'): v.get('dir') for v in child_module.findall('var')
                                if v.get('dir') in {'input', 'output', 'inout'}}
                    if set(order) != set(declared) or not 1 <= index <= len(order):
                        raise ValueError('source/XML positional port inventory mismatch')
                    pname = order[index - 1]
                    if {'input': 'in', 'output': 'out', 'inout': 'inout'}[declared[pname]] != port.get('direction'):
                        raise ValueError('source/XML positional port direction mismatch')
                    self.runtime_tags['source_header_positional_port_binding'] += 1
                if pname not in child_env:
                    raise ValueError(f"port {pname} absent in {inst.get('defName')}")
                child_signal = child_env[pname]
                direction = port.get("direction")
                if direction == "in":
                    rhs = self.expr(port[0], env)
                    lhs = f"LVar {child_signal.width} {child_signal.id}"
                elif direction == "out":
                    rhs = f"EVar {child_signal.width} {child_signal.id}"
                    lhs = self.lvalue(port[0], env)
                else:
                    raise ValueError(f"unsupported port direction {direction} at {port.get('loc')}")
                self.add_process("Combinational", [], f"SAssign false ({rhs}) ({lhs})",
                                 loc_line(port), path, f"port_{direction}")
        return env

    def translate(self) -> None:
        self.instantiate(self.top, self.top)
        if self.unsupported:
            raise ValueError("; ".join(self.unsupported[:20]))
        self.reorder_combinational()


def verilator_xml(xml: Path, flist: Path = FLIST, top: str = "cv32e40p_top",
                  parameters: dict[str, str] | None = None) -> list[str]:
    if parameters is None:
        parameters = {"COREV_PULP": "0", "COREV_CLUSTER": "0", "FPU": "0", "ZFINX": "0"}
    command = [
        "verilator", "--xml-only", "--xml-output", str(xml),
        "--Mdir", str(xml.parent), "--top-module", top,
        "-Wno-fatal", "-Wno-BLKANDNBLK", "-Wno-DECLFILENAME",
        "-Wno-PINCONNECTEMPTY",
        *[f"-G{name}={value}" for name, value in parameters.items()],
        "-f", str(flist.relative_to(ROOT)),
    ]
    subprocess.run(command, cwd=ROOT, check=True, stdout=subprocess.PIPE,
                   stderr=subprocess.STDOUT, text=True)
    return command


def write_coq(path: Path, tr: Translator, source_digest: str, xml_digest: str,
              feature_counts: dict[str, int], module_name: str = "CV32E40PExtendedAST",
              prefix: str = "cv32e40p") -> None:
    if not all(re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", value)
               for value in (module_name, prefix)):
        raise ValueError("Coq module/prefix must be identifiers")
    lines = [
        "(** Generated by tools/cv32e40p_extended_frontend.py; do not edit. *)",
        "From Coq Require Import ZArith List Strings.String.",
        "Require Import Lang.ExtendedSV Lang.ElaborationLowering.",
        "Import ListNotations.",
        "Import ExtendedSV.",
        "Import ElaborationLowering.",
        "Local Open Scope string_scope.",
        f"Module {module_name}.",
        f"Definition source_tree_sha256 : string := \"{source_digest}\".",
        f"Definition elaborated_xml_sha256 : string := \"{xml_digest}\".",
    ]
    for i, process in enumerate(tr.processes):
        lines.append(f"Definition process_{i} : Process := {process}.")
    plist = "; ".join(f"process_{i}" for i in range(len(tr.processes)))
    feature_map = {
        "typedef": "FeatureTypedef", "enum": "FeatureEnum",
        "package_import": "FeaturePackageImport", "parameter": "FeatureParameter",
        "localparam": "FeatureLocalparam", "for_generate": "FeatureForGenerate",
        "case_generate": "FeatureCaseGenerate", "packed_declaration": "FeaturePackedDeclaration",
        "interface": "FeatureInterface",
    }
    features = "; ".join(feature_map[name] for name, count in feature_counts.items() if count)
    lines += [
        f"Definition {prefix}_processes : list Process := [{plist}].",
        f"Definition {prefix}_program : Program :=",
        f"  {{| signal_count := {len(tr.signals)};",
        f"     processes := {prefix}_processes;",
        f"     statement_fuel := 512; lfp_fuel := {tr.lfp_fuel} |}}.",
        f"Definition {prefix}_mtrs : MTrs := phase_program_mtrs {prefix}_program.",
        f"Definition {prefix}_lfp := CombLFP {prefix}_program.",
        f"Definition {prefix}_elaborated_unit : CheckedElaboratedUnit :=",
        "  {| source_digest := source_tree_sha256;",
        "     elaborated_digest := elaborated_xml_sha256;",
        f"     features_seen := [{features}];",
        "     unsupported_elaboration_nodes := 0;",
        f"     lowered_runtime := {prefix}_program |}}.",
        f"Theorem {prefix}_lowering_checked : lowering_checked {prefix}_elaborated_unit = true.",
        "Proof. reflexivity. Qed.",
        f"Theorem {prefix}_lowering_semantics_preserving :",
        f"  StandardSemAfterElaboration {prefix}_elaborated_unit =",
        f"  LoweredSemantics {prefix}_elaborated_unit.",
        "Proof. apply checked_lowering_semantics_preserving; reflexivity. Qed.",
        f"Example checked_signal_count : signal_count {prefix}_program = {len(tr.signals)}%nat.",
        "Proof. reflexivity. Qed.",
        f"Example checked_process_count : List.length (processes {prefix}_program) = {len(tr.processes)}%nat.",
        "Proof. reflexivity. Qed.",
        f"End {module_name}.",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--coq-output", type=Path, required=True)
    parser.add_argument("--json-output", type=Path, required=True)
    parser.add_argument("--xml-output", type=Path)
    parser.add_argument("--top", default="cv32e40p_top")
    parser.add_argument("--flist", type=Path)
    parser.add_argument("--param", action="append", default=[], metavar="NAME=VALUE")
    parser.add_argument("--coq-module")
    parser.add_argument("--coq-prefix")
    args = parser.parse_args()
    if args.top != "cv32e40p_top" and args.flist is None:
        parser.error("a different top requires an explicit --flist")
    flist = args.flist or FLIST
    flist = flist if flist.is_absolute() else ROOT / flist
    parameters = ({"COREV_PULP": "0", "COREV_CLUSTER": "0", "FPU": "0", "ZFINX": "0"}
                  if args.top == "cv32e40p_top" else {})
    for item in args.param:
        name, separator, value = item.partition("=")
        if not separator or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name) or not value:
            parser.error("--param requires NAME=VALUE")
        parameters[name] = value
    module_name = args.coq_module or ("CV32E40PExtendedAST" if args.top == "cv32e40p_top"
                                      else args.top + "ExtendedAST")
    prefix = args.coq_prefix or ("cv32e40p" if args.top == "cv32e40p_top" else args.top)

    xml = args.xml_output or Path(tempfile.mkdtemp(prefix="cv32e40p-xml-")) / "cv32.xml"
    xml = xml if xml.is_absolute() else ROOT / xml
    xml.parent.mkdir(parents=True, exist_ok=True)
    command = verilator_xml(xml, flist, args.top, parameters)
    root = ET.parse(xml).getroot()
    translator = Translator(root, args.top)
    translator.translate()

    rtl_files = []
    for line in flist.read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("+"):
            rtl_files.append(ROOT / line)
    source_hash = hashlib.sha256()
    source_text = []
    for source in rtl_files:
        source_hash.update(source.relative_to(ROOT).as_posix().encode())
        source_hash.update(b"\0")
        source_hash.update(source.read_bytes())
        source_hash.update(b"\0")
        source_text.append(source.read_text())

    text = "\n".join(source_text)
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    text = re.sub(r"//.*", "", text)
    feature_counts = {
        "typedef": len(re.findall(r"\btypedef\b", text)),
        "enum": len(re.findall(r"\benum\b", text)),
        "package_import": len(re.findall(r"\b(?:package|import)\b", text)),
        "parameter": len(re.findall(r"\bparameter\b", text)),
        "localparam": len(re.findall(r"\blocalparam\b", text)),
        "for_generate": len(re.findall(r"\bgenerate\b[\s\S]{0,200}?\bfor\s*\(", text)),
        "case_generate": len(re.findall(r"\bgenerate\b[\s\S]{0,200}?\bcase\s*\(", text)),
        "packed_declaration": len(re.findall(r"\b(?:logic|wire|reg)\s+(?:signed\s+)?\[", text)),
        "interface": len(re.findall(r"\binterface\b", text)),
    }

    coq_output = args.coq_output if args.coq_output.is_absolute() else ROOT / args.coq_output
    json_output = args.json_output if args.json_output.is_absolute() else ROOT / args.json_output
    write_coq(coq_output, translator, source_hash.hexdigest(), sha256(xml), feature_counts,
              module_name, prefix)
    report = {
        "requirement": 38,
        "top": args.top,
        "configuration": {key: int(value) if value.isdecimal() else value
                          for key, value in parameters.items()},
        "coq_module": module_name,
        "coq_prefix": prefix,
        "verilator_command": command,
        "source_tree_sha256": source_hash.hexdigest(),
        "elaborated_xml_sha256": sha256(xml),
        "coq_ast_sha256": sha256(coq_output),
        "module_count": len(translator.modules),
        "instance_count": len(translator.instances),
        "signal_count": len(translator.signals),
        "process_count": len(translator.processes),
        "process_kinds": dict(Counter(p["kind"] for p in translator.process_meta)),
        "combinational_dependency_graph": translator.comb_graph_metrics,
        "lfp_fuel": translator.lfp_fuel,
        "runtime_node_coverage": dict(sorted(translator.runtime_tags.items())),
        "elaboration_feature_counts": feature_counts,
        "unsupported_runtime_nodes": translator.unsupported,
        "top_ports": {name: info.__dict__ for name, info in translator.top_env.items()
                      if info.direction in {"input", "output", "inout"}},
        "signals": [s.__dict__ for s in translator.signals],
        "processes": translator.process_meta,
        "trust_boundary": {
            "elaboration": "Verilator XML, translation validated by pinned digests and coverage",
            "runtime_semantics": "Rocq Lang.ExtendedSV",
            "claim": "Verilator is not used as a semantic-equivalence proof",
        },
    }
    json_output.parent.mkdir(parents=True, exist_ok=True)
    json_output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ["module_count", "instance_count",
          "signal_count", "process_count", "process_kinds", "unsupported_runtime_nodes"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
