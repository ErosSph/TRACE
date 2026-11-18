"""Condition-directed reducer with algebraic rules (extends cpu_condition_reduction.Compiler).

Adds the rules proved in src/Lang/ExtendedSVConditionalReductionAlgebra.v
(`and_zero_*`, `or_zero_*`, `or_one_*`, `and_one_*`) for operators that have one
constant operand. Untrusted planner: every step is replayed by Coq.
"""
from cpu_condition_reduction import Compiler


class AlgebraCompiler(Compiler):
    def normalize(self, index):
        res = super().normalize(index)
        if res.node != index:
            more = self.normalize(res.node)
            return res if more.node == res.node else self.chain(index, res, more)
        rule = self.algebra(index)
        if rule is None:
            return res
        nxt = self.normalize(rule.node)
        return rule if nxt.node == rule.node else self.chain(index, rule, nxt)

    def const(self, i):
        n = self.dag.nodes[i]
        if n.name == 'EConst':
            return self.dag.integer(n.args[0]), self.dag.integer(n.args[1])
        return None

    def algebra(self, index):
        d = self.dag
        n = d.nodes[index]
        if n.name != 'EBinary':
            return None
        a = n.args
        op = d.nodes[a[1]].name
        w = d.integer(a[0])
        l, r = self.const(a[2]), self.const(a[3])
        if op == 'BAnd':
            for side, c, other in (('l', l, a[3]), ('r', r, a[2])):
                if c is None:
                    continue
                if c[1] % (1 << c[0]) == 0:
                    return self.emit(index, d.constant(w, 0),
                                     f'apply and_zero_{side};vm_compute;reflexivity.')
                if w == 1 and c[0] == 1 and c[1] % 2 == 1:
                    return self.emit(index, d.node('EExtend', (a[0], d.atom('false'), other)),
                                     f'apply and_one_{side};vm_compute;reflexivity.')
        if op == 'BOr':
            for side, c, other in (('l', l, a[3]), ('r', r, a[2])):
                if c is None:
                    continue
                if c[1] % (1 << c[0]) == 0:
                    return self.emit(index, d.node('EExtend', (a[0], d.atom('false'), other)),
                                     f'apply or_zero_{side};vm_compute;reflexivity.')
                if w == 1 and c[0] == 1 and c[1] % 2 == 1:
                    return self.emit(index, d.constant(1, 1),
                                     f'apply or_one_{side};[vm_compute;reflexivity|reflexivity].')
        return None
