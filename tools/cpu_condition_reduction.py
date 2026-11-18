"""Untrusted DAG reduction planner emitting small, Coq-checked proof steps.

Every (input node, fact context) is processed once. Unknown guards are retained;
equal reduced arms can remove a guard without assuming its value. Generated
certificates preserve expression widths and refer to one sampled State only.
"""
from dataclasses import dataclass
import re

from cpu_expression_dag import ARITY


@dataclass(frozen=True)
class Result:
    node: int
    proof: str


class Compiler:
    def __init__(self, dag, facts=(), *, prefix='reduction', externals=None):
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', prefix):
            raise ValueError('invalid proof prefix')
        self.dag, self.prefix = dag, prefix
        self.facts = tuple((int(w), int(x), int(v)) for w, x, v in facts)
        if any(w < 0 or x < 0 for w, x, _ in self.facts):
            raise ValueError('negative width or signal')
        if len({(w, x) for w, x, _ in self.facts}) != len(self.facts):
            raise ValueError('duplicate or conflicting fact key')
        self.fact_map = {(w, x): (i, v) for i, (w, x, v) in enumerate(self.facts)}
        self.lines = []
        self.memo = {}
        self.named = set()
        self.externals = dict(externals or {})
        self.serial = 0
        self.hits = 0
        entries = ';'.join(f'({w}%nat,{x}%nat,({v})%Z)' for w, x, v in self.facts)
        self.context = prefix + '_facts'
        self.lines.append(f'Definition {self.context}:list Fact:=[{entries}].')

    def ref(self, index):
        if index in self.externals:
            return self.externals[index]
        n = self.dag.nodes[index]
        if n.name not in ARITY:
            if n.args:
                raise ValueError('compound non-expression atom')
            if n.name.startswith('-'):
                return '(' + n.name + ')'
            return n.name
        name = f'{self.prefix}_e{index}'
        if index not in self.named:
            children = [self.ref(c) for c in n.args]
            self.lines.append(f'Definition {name}:Expr:=({n.name} ' + ' '.join(children) + ').')
            self.named.add(index)
        return name

    def emit(self, original, reduced, proof):
        left, right = self.ref(original), self.ref(reduced)
        name = f'{self.prefix}_p{self.serial}'
        self.serial += 1
        self.lines += [f'Lemma {name}:Reduction {self.context} {left} {right}.',
                       f'Proof. {proof} Qed.']
        return Result(reduced, name)

    def chain(self, original, first, second):
        return self.emit(original, second.node,
            f'exact(transitive {self.context} {self.ref(original)} {self.ref(first.node)} '
            f'{self.ref(second.node)} {first.proof} {second.proof}).')

    def normalize(self, index):
        d = self.dag
        n = d.nodes[index]
        # Every numerical proposal is replayed by the kernel on this small
        # closed node, even if the Python evaluator is wrong.
        value = d.eval_closed(index)
        if value is not None and not self.has_inputs(index):
            result = d.constant(d.width(index), value)
            if result != index:
                return self.emit(index, result,
                    f'eapply ground;[reflexivity|vm_compute;reflexivity].')
        if n.name == 'EExtend' and d.nodes[n.args[1]].name == 'false' and d.width(n.args[2]) == d.width(index):
            return self.emit(index, n.args[2], 'apply unsigned_same_width;reflexivity.')
        return Result(index, f'(identity {self.context} {self.ref(index)})')

    def has_inputs(self, index):
        return any(n.name == 'EVar' for _, n in self.dag.iter_nodes(index))

    def reduce(self, index):
        if index in self.memo:
            self.hits += 1
            return self.memo[index]
        d = self.dag
        n, a = d.nodes[index], d.nodes[index].args
        if n.name not in ARITY:
            raise ValueError('reduction root is not an Expr')
        if n.name == 'EVar' and (key := (d.integer(a[0]), d.integer(a[1]))) in self.fact_map:
            offset, value = self.fact_map[key]
            membership = 'or_introl eq_refl'
            for _ in range(offset):
                membership = 'or_intror (' + membership + ')'
            result = self.emit(index, d.constant(key[0], value),
                f'apply known;exact({membership}).')
        elif n.name in ('EConst', 'EVar'):
            result = Result(index, f'(identity {self.context} {self.ref(index)})')
        elif n.name == 'ECond':
            guard = self.reduce(a[1])
            gn = d.nodes[guard.node]
            if gn.name == 'EConst':
                value = d.eval_closed(guard.node)
                chosen = self.reduce(a[3] if value == 0 else a[2])
                mid = d.node('EExtend', (a[0], d.atom('false'), chosen.node))
                rule = 'conditional_false' if value == 0 else 'conditional_true'
                result = self.emit(index, mid,
                    f'eapply {rule};[exact {guard.proof}|vm_compute;'
                    + ('reflexivity' if value == 0 else 'discriminate')
                    + f'|exact {chosen.proof}].')
            else:
                yes, no = self.reduce(a[2]), self.reduce(a[3])
                if yes.node == no.node:
                    mid = d.node('EExtend', (a[0], d.atom('false'), yes.node))
                    result = self.emit(index, mid,
                        f'apply conditional_same;[exact {yes.proof}|exact {no.proof}].')
                else:
                    mid = d.node('ECond', (a[0], guard.node, yes.node, no.node))
                    result = self.emit(index, mid,
                        f'apply conditional;[exact {guard.proof}|exact {yes.proof}|exact {no.proof}].')
            final = self.normalize(result.node)
            if final.node != result.node:
                result = self.chain(index, result, final)
        else:
            positions = {'ESel': (1, 2), 'EConcat': (1, 2), 'EReplicate': (2,),
                         'EExtend': (2,), 'EUnary': (2,), 'EBinary': (2, 3)}[n.name]
            children = [self.reduce(a[p]) for p in positions]
            replaced = list(a)
            for p, child in zip(positions, children):
                replaced[p] = child.node
            mid = d.node(n.name, tuple(replaced))
            rule = {'ESel': 'select', 'EConcat': 'concatenate', 'EReplicate': 'replicate',
                    'EExtend': 'extend', 'EUnary': 'unary', 'EBinary': 'binary'}[n.name]
            if mid == index:
                result = Result(index, f'(identity {self.context} {self.ref(index)})')
            else:
                result = self.emit(index, mid,
                    f'apply {rule};' + '[' + '|'.join('exact ' + c.proof for c in children) + '].')
            final = self.normalize(result.node)
            if final.node != result.node:
                result = self.chain(index, result, final)
        self.memo[index] = result
        return result

    def render(self, index):
        result = self.reduce(index)
        return '\n'.join(self.lines) + '\n', result, dict(
            unique_inputs_processed=len(self.memo), proof_nodes=self.serial,
            cache_hits=self.hits, output=self.dag.stats(result.node),
            state_context=self.dag.context, candidate_only_until_Coq_checked=True)
