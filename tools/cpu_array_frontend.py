#!/usr/bin/env python3
"""Opt-in bounded unpacked-bank lowering into existing bit-slice semantics.

Only zero-based, unsigned indexes whose entire dtype domain is inside the
bank are accepted. No X/OOB access is silently replaced with zero. This is
an executable lowering with a separate source-translation trust boundary,
not a proof of arbitrary SystemVerilog frontend equivalence.
"""
import argparse
import hashlib
import json
from pathlib import Path
import xml.etree.ElementTree as ET
from cv32e40p_extended_frontend import Translator, parse_const, write_coq

class ArrayTranslator(Translator):
    def bank_shape(self, dtype_id):
        d = self.dtypes[dtype_id]
        if d.tag != "unpackarraydtype":
            raise ValueError("array access does not reference an unpacked bank")
        rng = d.find("range")
        if rng is None or len(rng) != 2:
            raise ValueError("array range is not static")
        a, b = [parse_const(c.get("name"))[1] for c in rng]
        if min(a,b) != 0:
            raise ValueError("only zero-based bank indexes are supported")
        cells = max(a,b)+1
        sub = self.dtypes[d.get("sub_dtype_id")]
        if sub.tag == "unpackarraydtype":
            raise ValueError("nested unpacked banks require another certificate")
        return cells, self.dtype_width(d.get("sub_dtype_id"))

    def dtype_width(self, dtype_id, seen=None):
        d = self.dtypes.get(dtype_id)
        if d is not None and d.tag == "unpackarraydtype":
            cells, width = self.bank_shape(dtype_id)
            return cells * width
        return super().dtype_width(dtype_id, seen)

    def array_offset(self, node, env):
        base, index = list(node)
        cells, width = self.bank_shape(base.get("dtype_id"))
        dtype = self.dtypes[index.get("dtype_id")]
        iw = self.width(index)
        if dtype.tag != "basicdtype":
            raise ValueError("non-basic index type needs a signedness certificate")
        if dtype.get("signed") in {"true", "1"}:
            raise ValueError("signed array index lacks an in-range certificate")
        if 2**iw > cells:
            raise ValueError(f"array index domain {2**iw} exceeds {cells} cells")
        # No index*element-width overflow at this arithmetic width.
        ow = iw + width.bit_length() + 1
        return f"EBinary {ow} BMul ({self.expr(index,env)}) (EConst {ow} {width})"

    def expr(self, node, env):
        if node.tag == "streaml":
            # {<<{x}} reverses bits.  Lower to existing slice/concat
            # semantics, without adding an evaluator primitive.  Other
            # slice sizes need their own streaming-layout validation.
            children = list(node)
            if len(children) != 2 or children[1].tag != "const":
                raise ValueError("streaml requires a constant one-bit slice")
            if parse_const(children[1].get("name"))[1] != 1:
                raise ValueError("streaml currently supports only one-bit slices")
            width = self.width(children[0])
            if width < 1 or self.width(node) != width:
                raise ValueError("streaml result width must equal its operand width")
            self.runtime_tags[node.tag] += 1
            operand = self.expr(children[0], env)
            offset_width = max(1, (width - 1).bit_length())
            def bit(index):
                return f"ESel 1 ({operand}) (EConst {offset_width} {index})"
            result = bit(0)
            for index in range(1, width):
                result = f"EConcat {index + 1} ({result}) ({bit(index)})"
            return result
        if node.tag in {"gte", "lte", "gtes", "ltes"}:
            a,b = list(node)
            self.runtime_tags[node.tag] += 1
            w = self.width(node)
            if node.tag == "gte": op,l,r = "BLtU",a,b
            elif node.tag == "lte": op,l,r = "BGtU",a,b
            elif node.tag == "gtes": op,l,r = "BGtS",b,a
            else: op,l,r = "BGtS",a,b
            cond = f"EBinary 1 {op} ({self.expr(l,env)}) ({self.expr(r,env)})"
            return f"ECond {w} ({cond}) (EConst {w} 0) (EConst {w} 1)"
        if node.tag == "lts":
            a,b = list(node)
            self.runtime_tags[node.tag] += 1
            return f"EBinary {self.width(node)} BGtS ({self.expr(b,env)}) ({self.expr(a,env)})"
        if node.tag in {"logor", "logand"}:
            a,b = list(node)
            w = self.width(node)
            self.runtime_tags[node.tag] += 1
            truth_b = f"EUnary {w} URedOr ({self.expr(b,env)})"
            yes,no = ((f"EConst {w} 1", truth_b) if node.tag == "logor"
                      else (truth_b, f"EConst {w} 0"))
            return f"ECond {w} ({self.expr(a,env)}) ({yes}) ({no})"
        if node.tag == "lognot":
            a = list(node)[0]
            self.runtime_tags[node.tag] += 1
            return f"EBinary {self.width(node)} BEq ({self.expr(a,env)}) (EConst {self.width(a)} 0)"
        if node.tag == "arraysel":
            base, index = list(node)
            self.runtime_tags[node.tag] += 1
            return f"ESel {self.width(node)} ({self.expr(base,env)}) ({self.array_offset(node,env)})"
        if node.tag == "mul":
            a,b = list(node)
            self.runtime_tags[node.tag] += 1
            return f"EBinary {self.width(node)} BMul ({self.expr(a,env)}) ({self.expr(b,env)})"
        return super().expr(node,env)

    def lvalue(self, node, env):
        if node.tag == "arraysel":
            base, index = list(node)
            return f"LSel {self.width(node)} ({self.lvalue(base,env)}) ({self.array_offset(node,env)})"
        return super().lvalue(node,env)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--xml", type=Path, required=True)
    p.add_argument("--top", required=True)
    p.add_argument("--module", required=True)
    p.add_argument("--prefix", required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    pinned = json.loads((args.xml.parent/"report.json").read_text())
    actual_xml_hash = hashlib.sha256(args.xml.read_bytes()).hexdigest()
    if pinned.get("xml_sha256") != actual_xml_hash:
        raise ValueError("XML is not pinned by its original elaboration report")
    for item in pinned.get("source_hashes",[]):
        if hashlib.sha256(Path(item["path"]).read_bytes()).hexdigest() != item["sha256"]:
            raise ValueError("source changed since elaboration; regenerate XML")
    if not pinned.get("source_hashes"):
        raise ValueError("source hashes are missing; regenerate elaboration report")
    tr = ArrayTranslator(ET.parse(args.xml).getroot(),args.top)
    sources = []
    for f in tr.root.findall("./files/file"):
        name = Path(f.get("filename", ""))
        if name.is_file(): sources.append((str(name.resolve()),hashlib.sha256(name.read_bytes()).hexdigest()))
    source_digest = hashlib.sha256(json.dumps(sorted(sources)).encode()).hexdigest()
    report = {"source_xml_sha256":hashlib.sha256(args.xml.read_bytes()).hexdigest(),
              "translation_equivalence":"not_mechanized_from_original_rtl"}
    try:
        tr.translate()
        write_coq(args.output/(args.module+".v"),tr,source_digest,
                  report["source_xml_sha256"],{},args.module,args.prefix)
        report.update(status="runtime_ast_generated_not_refinement",signals=len(tr.signals),
                      processes=len(tr.processes),features=dict(tr.runtime_tags),source_hashes=sources,
                      top=args.top,instance_table=tr.instances,
                      signal_table=[vars(s) for s in tr.signals],process_table=tr.process_meta,
                      comb_candidate=tr.comb_graph_metrics,lfp_fuel=tr.lfp_fuel)
    except (ValueError,KeyError,NotImplementedError) as err:
        report.update(status="unsupported",diagnostic=str(err))
    (args.output/"report.json").write_text(json.dumps(report,indent=2))
    print(json.dumps(report,indent=2))
    return 0 if report["status"] == "runtime_ast_generated_not_refinement" else 1

if __name__ == "__main__":
    raise SystemExit(main())
