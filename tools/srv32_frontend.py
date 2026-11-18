#!/usr/bin/env python3
"""Additive frontend subclass for srv32: unpacked banks whose declared lower bound is positive.

srv32 declares `reg [31:0] regs [31:1]` (x0 is not stored).  Verilator already rewrites every access to a
zero-based element index `sel - 1` (5-bit wrap-around: sel = 0 gives 31, outside the 31 declared cells).  The
trusted ArrayTranslator rejects such banks (non-zero lower bound; index domain 32 > 31 cells).  This subclass
pads the bank to the next power of two cells (31 -> 32), so every index the Verilator index expression can
produce is inside the stored signal.  The padded cell (element index 31, i.e. register number 0) is dead
storage.  This differs from Verilog only for out-of-range accesses (write ignored; read X) and is sound
exactly under the recorded obligations:
  (R) every read at an index that can be out of range is guarded (srv32: `(sel == 0) ? 0 : regs[...]`);
  (W) a write to the dead cell is never observed (consumers read registers 1..31 only).
cpu_array_frontend.py is not modified; Dark/Bzeeno imports do not use this class.
proof_author='LLM-generated: Claude Code (claude-sonnet-5-5)'; external_llm_api_calls=0.
"""
from cpu_array_frontend import ArrayTranslator
from cv32e40p_extended_frontend import parse_const


class PaddedBankTranslator(ArrayTranslator):
    padded_banks = []

    def bank_shape(self, dtype_id):
        d = self.dtypes[dtype_id]
        if d.tag != "unpackarraydtype":
            raise ValueError("array access does not reference an unpacked bank")
        rng = d.find("range")
        if rng is None or len(rng) != 2:
            raise ValueError("array range is not static")
        a, b = [parse_const(c.get("name"))[1] for c in rng]
        lo = min(a, b)
        if lo < 0:
            raise ValueError("negative bank bound")
        declared = abs(a - b) + 1
        cells = 1
        while cells < declared:
            cells *= 2
        if lo != 0 or cells != declared:
            rec = dict(dtype_id=dtype_id, low=lo, declared_cells=declared, padded_cells=cells)
            if rec not in self.padded_banks:
                self.padded_banks.append(rec)
        sub = self.dtypes[d.get("sub_dtype_id")]
        if sub.tag == "unpackarraydtype":
            raise ValueError("nested unpacked banks require another certificate")
        return cells, self.dtype_width(d.get("sub_dtype_id"))

    # ---- bounded `while` (Verilog `for`) with a constant trip count -------------------------------
    unrolled_loops = []

    def _loop_unroll(self, init, loop, env):
        """Translate `i = C0; while (C > i) { body; i = i + S }` into nested guarded copies.

        Each copy is `SIf cond (SSeq [body; step; next]) SSkip`, with the real runtime loop variable, so the
        result equals the loop as long as the (statically derived) trip count is right.  The trip count is
        computed from the constants; the body must not assign the loop variable."""
        kids = list(loop)
        cond, body, step = kids[0], kids[1:-1], kids[-1]
        if init.tag != "assign" or loop.tag != "while" or len(kids) < 3:
            raise ValueError("unsupported loop shape")
        c0, var = list(init)
        if c0.tag != "const" or var.tag != "varref":
            raise ValueError("loop init is not a constant assignment")
        name = var.get("name")
        if cond.tag not in {"gts", "gt"} or [c.tag for c in cond] != ["const", "varref"] \
                or list(cond)[1].get("name") != name:
            raise ValueError("unsupported loop condition (expected CONST > var)")
        if step.tag != "assign":
            raise ValueError("unsupported loop step")
        add, tgt = list(step)
        if add.tag != "add" or tgt.get("name") != name or [c.tag for c in add] != ["const", "varref"] \
                or list(add)[1].get("name") != name:
            raise ValueError("unsupported loop step (expected var = CONST + var)")
        for b in body:
            for n in b.iter():
                if n.tag in {"assign", "assigndly"} and list(n)[1].get("name") == name:
                    raise ValueError("loop body assigns the loop variable")
        v, bound, inc = parse_const(c0.get("name"))[1], parse_const(list(cond)[0].get("name"))[1], \
            parse_const(list(add)[0].get("name"))[1]
        trips = 0
        while v < bound:
            v += inc
            trips += 1
            if inc <= 0 or trips > 64:
                raise ValueError("loop trip count not statically bounded by 64")
        self.unrolled_loops.append(dict(loop_var=name, trips=trips, loc=loop.get("loc")))
        cond_s = self.expr(cond, env)
        inner = "SSkip"
        for _ in range(trips):
            seq = [self.stmt(b, env) for b in body] + [self.stmt(step, env), inner]
            inner = f"SIf ({cond_s}) (SSeq [{'; '.join(seq)}]) SSkip"
        return f"SSeq [{self.stmt(init, env)}; {inner}]"

    def stmt(self, node, env):
        if node.tag == "begin":
            kids = [c for c in node if c.tag not in {"sentree", "var"}]
            if any(c.tag == "while" for c in kids):
                parts, k = [], 0
                while k < len(kids):
                    if k + 1 < len(kids) and kids[k + 1].tag == "while":
                        self.runtime_tags["begin"] += 1
                        parts.append(self._loop_unroll(kids[k], kids[k + 1], env))
                        k += 2
                    elif kids[k].tag == "while":
                        raise ValueError("while without a constant init")
                    else:
                        parts.append(self.stmt(kids[k], env))
                        k += 1
                return "SSeq [" + "; ".join(parts) + "]"
        return super().stmt(node, env)
