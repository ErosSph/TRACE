"""Python mirror of src/Lang/ExtendedSVSymExec.v (xeval / xexec), untrusted: Coq re-checks every result.

Expressions and statements are the tuples of cpu_ast_sim / cpu_tmpl_ast. `Stuck` carries the expression the
executor could not decide, so a generator can ask for the missing fact.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
"""


class Stuck(Exception):
    def __init__(self, expr, why):
        super().__init__(why)
        self.expr, self.why = expr, why


def norm(w, v):
    return v & ((1 << w) - 1)


def width(e):
    return e[1]


def inputs(e, acc=None):
    acc = [] if acc is None else acc
    k = e[0]
    if k == 'EVar':
        acc.append((e[1], e[2]))
    elif k != 'EConst':
        for c in e[1:]:
            if isinstance(c, tuple) and c and isinstance(c[0], str) and c[0].startswith('E'):
                inputs(c, acc)
    return acc


def signed(w, v):
    v = norm(w, v)
    if w == 0:
        return 0
    return v - (1 << w) if (v >> (w - 1)) & 1 else v


def replicate(count, bw, v):
    r = 0
    for _ in range(count):
        r = (r << bw) | norm(bw, v)
    return r


class Exec:
    def __init__(self, facts):
        self.facts = {e: z for e, z in facts}
        self.log = []   # chronological writes (root, width, value), as the Coq overlay (reversed)

    def unwritten(self, ov, e):
        return all(x not in ov for _, x in inputs(e))

    def ev(self, ov, e):
        if self.unwritten(ov, e) and e in self.facts:
            return self.facts[e]
        k = e[0]
        if k == 'EConst':
            return norm(e[1], e[2])
        if k == 'EVar':
            if e[2] in ov and ov[e[2]][0] == e[1]:
                return ov[e[2]][1]
            raise Stuck(e, 'variable without value')
        if k == 'ESel':
            return norm(e[1], self.ev(ov, e[2]) >> self.ev(ov, e[3]))
        if k == 'EConcat':
            return norm(e[1], (self.ev(ov, e[2]) << width(e[3])) | self.ev(ov, e[3]))
        if k == 'EReplicate':
            return norm(e[1], replicate(e[2], width(e[3]), self.ev(ov, e[3])))
        if k == 'EExtend':
            v = self.ev(ov, e[3])
            return norm(e[1], signed(width(e[3]), v) if e[2] else v)
        if k == 'EUnary':
            v = self.ev(ov, e[3])
            return norm(e[1], ~v if e[2] == 'UNot' else (-v if e[2] == 'UNegate' else int(v != 0)))
        if k == 'EBinary':
            a, b = self.ev(ov, e[3]), self.ev(ov, e[4])
            op = e[2]
            wl, wr = width(e[3]), width(e[4])
            r = {'BAnd': lambda: a & b, 'BOr': lambda: a | b, 'BXor': lambda: a ^ b, 'BAdd': lambda: a + b,
                 'BSub': lambda: a - b, 'BMul': lambda: a * b, 'BEq': lambda: int(a == b), 'BNeq': lambda: int(a != b),
                 'BLtU': lambda: int(a < b), 'BGtU': lambda: int(a > b),
                 'BGtS': lambda: int(signed(wl, a) > signed(wr, b)), 'BShiftL': lambda: a << b,
                 'BShiftR': lambda: a >> b, 'BShiftRS': lambda: signed(wl, a) >> b}[op]()
            return norm(e[1], r)
        if k == 'ECond':
            g = self.ev(ov, e[2])
            return norm(e[1], self.ev(ov, e[4] if g == 0 else e[3]))
        raise ValueError(k)

    def select(self, ov, v, arms, default):
        for key, body in arms:
            if key is None:
                default = body
            else:
                if v == self.ev(ov, key):
                    return body
        return default

    def run(self, st, ov, fuel):
        """ov: dict root -> (width, value); returns the new dict (Python mirror of xexec)."""
        if fuel == 0:
            return ov
        k = st[0]
        if k == 'SSkip':
            return ov
        if k == 'SAssign':
            if st[1] or st[3][0] != 'LVar':
                raise Stuck(None, 'non-blocking or partial write')
            w, r = st[3][1], st[3][2]
            z = self.ev(ov, st[2])
            ov = dict(ov)
            ov[r] = (w, norm(w, z))
            self.log.append((r, w, norm(w, z)))
            return ov
        if k == 'SSeq':
            for c in st[1]:
                ov = self.run(c, ov, fuel - 1)
            return ov
        if k == 'SIf':
            g = self.ev(ov, st[1])
            return self.run(st[3] if g == 0 else st[2], ov, fuel - 1)
        if k == 'SCase':
            v = self.ev(ov, st[1])
            return self.run(self.select(ov, v, st[2], ('SSkip',)), ov, fuel - 1)
        raise ValueError(k)


def close_facts(proc_body, word, base_facts, fuel, class_slices, max_iter=40):
    """Run the mirror, resolving stuck expressions: slices of `word` that lie inside the known bit ranges of
    the class facts are derived; any other stuck input variable becomes a BASE fact with value 0 and is reported.
    Returns (facts, base_fact_exprs, ov)."""
    facts = list(class_slices)
    base = []
    known = {}   # bit -> value
    for e, z in class_slices:
        l = e[3][2]
        for i in range(e[1]):
            known[l + i] = (z >> i) & 1
    for _ in range(max_iter):
        try:
            return facts, base, Exec(facts + base_facts).run(proc_body, {}, fuel)
        except Stuck as s:
            e = s.expr
            # find enclosing slice of the word: re-run with a tracing subclass is not needed; handle direct cases
            if e is not None and e[0] == 'ESel' and e[2] == word and e[3][0] == 'EConst':
                l, w = e[3][2], e[1]
                if all((l + i) in known for i in range(w)):
                    facts.append((e, sum(known[l + i] << i for i in range(w))))
                    continue
                raise
            if e is not None and e[0] not in ('EVar', 'ESel', 'EConst') and width(e) == 1:    # ctl v3 atom (only produced by _Atoms)
                base_facts = base_facts + [(e, 0)]
                base.append(e)
                continue
            if e is not None and e[0] == 'EVar' and e != word:
                base_facts = base_facts + [(e, 0)]
                base.append(e)
                continue
            if e == word:
                # the word is read as a slice: find which one by tracing
                raise
            raise


class _Tracing(Exec):
    def ev(self, ov, e):
        try:
            return super().ev(ov, e)
        except Stuck as s:
            if s.expr is not None and s.expr[0] == 'EVar' and e[0] == 'ESel' and e[2] == s.expr:
                s.expr = e     # report the slice instead of the bare word
            raise


class _Atoms(Exec):
    """Tracing executor for ctl v3: a stuck input is reported as the OUTERMOST sub-expression of width 1 whose inputs are all
    unwritten (an enumerable fact), instead of its 5-bit leaves, so scenarios never pin leaf signals to 0."""
    def ev(self, ov, e):
        try:
            return super().ev(ov, e)
        except Stuck as s:
            if s.expr is not None and s.expr[0] == 'EVar' and e[0] == 'ESel' and e[2] == s.expr:
                s.expr = e
            elif s.expr is not None and e[0] not in ('EConst', 'EVar', 'ESel') and width(e) == 1 and self.unwritten(ov, e):
                s.expr = e
            raise
