#!/usr/bin/env python3
"""Table-driven per-class controller facts (milestone 1 generator).

Input: a design AST + its role manifest (framework/auto-contract-profiles/<design>.json,
`pipeline_roles` and `template_roles`) + the ISA class table (cpu_isa_classes.py).
Output: one Coq module with, for every class, a theorem
  <Class>_controls: CombLFP P seed fixed -> prem_<Class> fixed -> (concl_1 /\ ... /\ concl_n)
about the actual controller expressions at the combinational fixed point.
Expected values come from the ISA class (writes rd, branch/jump kind, operation);
the RTL expressions are specialised by condition-directed reduction
(cpu_condition_reduction + cpu_tmpl_reduce algebra rules, Coq-checked) and by
the generic checked_assignment_binding equations. No RTL value is used as an expectation.
Untrusted generator: Coq checks everything.
"""
import argparse
import json
import re
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles
import cpu_isa_classes as isa
from cpu_expression_dag import ExpressionDAG
from cpu_tmpl_reduce import AlgebraCompiler


def show(dag, i):
    n = dag.nodes[i]
    if not n.args:
        return n.name
    return '(' + n.name + ' ' + ' '.join(show(dag, x) for x in n.args) + ')'


def tuple_of(dag, i):
    """Reduced DAG node back to the tuple form used by cpu_tmpl_ast."""
    n = dag.nodes[i]
    a = n.args
    N = dag.integer
    if n.name == 'EConst':
        return ('EConst', N(a[0]), N(a[1]))
    if n.name == 'EVar':
        return ('EVar', N(a[0]), N(a[1]))
    if n.name in ('ESel', 'EConcat'):
        return (n.name, N(a[0]), tuple_of(dag, a[1]), tuple_of(dag, a[2]))
    if n.name == 'EReplicate':
        return (n.name, N(a[0]), N(a[1]), tuple_of(dag, a[2]))
    if n.name == 'EExtend':
        return (n.name, N(a[0]), dag.nodes[a[1]].name == 'true', tuple_of(dag, a[2]))
    if n.name == 'EUnary':
        return (n.name, N(a[0]), dag.nodes[a[1]].name, tuple_of(dag, a[2]))
    if n.name == 'EBinary':
        return (n.name, N(a[0]), dag.nodes[a[1]].name, tuple_of(dag, a[2]), tuple_of(dag, a[3]))
    if n.name == 'ECond':
        return (n.name, N(a[0]), tuple_of(dag, a[1]), tuple_of(dag, a[2]), tuple_of(dag, a[3]))
    raise ValueError(n.name)


def sub(txt, a, b, pc, link):
    m = {'a': a, 'b': b, 'pc': pc, 'link': link}
    return re.sub(r'\b(a|b|pc|link)\b', lambda x: m[x.group(1)], txt)


class Gen:
    def __init__(self, design, prefix):
        self.design = design
        self.ast, self.pr, self.tr = roles.load_all(design)
        self.prefix = prefix
        self.dag = ExpressionDAG()
        self.prog = self.pr['ast']['program'].split('.')[-1]
        self.ast_module = self.pr['ast']['module']
        self.head = []      # shared Coq text (wire equations, target originals)
        self.wires = set()
        self.targets_def = {}
        c = self.pr['controller']
        self.id = dict(xres=self.tr['reset_reg']['id'], halt=self.pr['fetch_slot']['stall']['id'],
                       flush=c['flush']['id'], f3=c['funct3']['id'], f7=c['funct7']['id'], rd=c['rd']['id'],
                       a=c['operand_a']['id'], b=c['operand_b']['id'], imm=c['imm_signed']['id'],
                       pc=self.pr['pc']['register']['id'], link=self.pr['fetch_slot']['pc']['id'],
                       ifpc=self.pr['pc']['fetch_pc']['id'], jreq=self.pr['pc']['branch_request']['id'],
                       jval=self.pr['pc']['branch_target']['id'], bmux=c['branch_decision']['id'],
                       ddreq=self.tr['data_request']['id'], drd=self.pr['data_bus']['read']['id'],
                       dwr=self.pr['data_bus']['write']['id'])
        ports = {p['index']: p['id'] for p in self.tr['rf_read_ports']['ports']}
        self.id['dreg'] = ports[self.id['rd']]
        self.cut = {c[k]['id'] for k in ('opcode', 'funct3', 'funct7', 'rd', 'rs1', 'rs2', 'imm_signed', 'imm_upper',
                                         'operand_a', 'operand_b')} | set(ports.values())
        self.flagregs = sorted(self.tr['class_flags']['flags'], key=lambda f: f['reg']['id'])

    # ---------------------------------------------------------------- shared text
    def wire_eq(self, r):
        if r in self.wires:
            return
        self.wires.add(r)
        c = self.ast.comb[r]
        W = c['width']
        self.head += [
            f'Definition orig_w{r}:Expr:={T.coq(c["rhs"])}.',
            f'Theorem eq_w{r} seed fixed:CombLFP P seed fixed->norm {W}(read_signal fixed {r}%nat)=norm {W}(eval_expr fixed orig_w{r}).',
            f'Proof. intro HL. refine(checked_assignment_binding P _ {c["k"]}%nat {c["name"]} {"true" if c["nba"] else "false"} orig_w{r} {W}%nat {r}%nat seed fixed eq_refl _ _ _ _ HL).',
            ' all: first[vm_compute;reflexivity|(vm_compute;lia)]. Qed.']

    def target_orig(self, name):
        t = self.tr['targets'][name]
        _, st = self.ast.find_assign(int(t['process'].split('_')[1]), t['root'])
        rhs = st[2]
        if name not in self.targets_def:
            self.targets_def[name] = rhs
            path = '[' + ';'.join(map(str, t['path'])) + ']%nat'
            self.head += [f'Definition orig_t_{name}:Expr:={T.coq(rhs)}.',
                          f'Lemma orig_t_{name}_checked:rhs_of(stmt_at(process_body {t["process"]}){path})=orig_t_{name}.',
                          'Proof. vm_compute;reflexivity. Qed.']
        return rhs

    # ---------------------------------------------------------------- reduction
    def reduce(self, rhs, ext, prefix, facts, emit):
        """facts: ordered dict (w,x)->v. Returns (text, node, proof, compiler, relevant_facts)."""
        used = T.evars(rhs)
        rel = [(w, x, v) for (w, x), v in facts.items() if (w, x) in used]
        node = self.dag.parse(T.coq(rhs))
        comp = AlgebraCompiler(self.dag, rel, prefix=prefix, externals={node: ext})
        text, res, _ = comp.render(node)
        return text, res, comp, rel, node

    def probe(self, st, x):
        """Is comb wire x constant under the facts? Emits the F<x> line (and those of its dependencies) if so."""
        W = self.ast.comb[x]['width']
        if (W, x) in st['facts']:
            return True
        if x in st['probed']:
            return False
        c = self.ast.comb[x]
        st['probed'].add(x)
        self.explore(st, c['rhs'], f'orig_w{x}', f'{st["cls"]}_p{x}')
        _, res, _, _, _ = self.reduce(c['rhs'], f'orig_w{x}', f'{st["cls"]}_p{x}', st['facts'], False)
        if self.dag.nodes[res.node].name == 'EConst':
            self.derive(st, x)
            return True
        return False

    def explore(self, st, rhs, ext, prefix):
        """Find (and emit) every wire that `rhs` needs and that is constant under the facts."""
        for _ in range(16):
            _, res, _, _, _ = self.reduce(rhs, ext, prefix + '_dry', st['facts'], False)
            red = tuple_of(self.dag, res.node)
            before = len(st['facts'])
            for (w, x) in sorted(T.evars(red)):
                if (w, x) in st['facts'] or x in self.cut or x not in self.ast.comb:
                    continue
                self.probe(st, x)
            if len(st['facts']) == before:
                return

    def settle(self, st, rhs, ext, prefix):
        """Specialise `rhs` under the facts; derive (R lines) the non-constant wires left in it."""
        self.explore(st, rhs, ext, prefix)
        text, res, comp, rel, node = self.reduce(rhs, ext, prefix, st['facts'], True)
        red = tuple_of(self.dag, res.node)
        for (w, x) in sorted(T.evars(red)):
            if (w, x) in st['facts'] or x in self.cut or x not in self.ast.comb:
                continue
            self.derive(st, x)
        return dict(text=text, res=res, comp=comp, rel=rel, red=red, ext=ext, prefix=prefix, node=node,
                    ref=comp.ref(res.node))

    def holds_lemma(self, st, rec):
        rel = rec['rel']
        hyps = ' '.join(f'(H{i}:norm {w}(read_signal fixed {x}%nat)={v})' for i, (w, x, v) in enumerate(rel))
        names = ' '.join(f'H{i}' for i in range(len(rel)))
        cons = ''.join(f'(Forall_cons ({w}%nat,{x}%nat,({v})%Z) H{i} ' for i, (w, x, v) in enumerate(rel)) + '(Forall_nil _)' + ')' * len(rel)
        return [f'Lemma {rec["prefix"]}_holds fixed {hyps}:Holds {rec["comp"].context} fixed.',
                f'Proof. unfold Holds,{rec["comp"].context}. exact({cons}). Qed.']

    def holds_use(self, rec):
        return f'({rec["prefix"]}_holds fixed ' + ' '.join(f'F{x}' for (w, x, v) in rec['rel']) + ')'

    def emit_rec(self, st, rec):
        st['out'] += [rec['text']] + self.holds_lemma(st, rec)

    def derive(self, st, x):
        """Establish the value of comb wire x under the facts: constant F<x> or reduction R<x>."""
        if x in st['derived']:
            return
        st['derived'].add(x)
        self.wire_eq(x)
        c = self.ast.comb[x]
        W = c['width']
        rec = self.settle(st, c['rhs'], f'orig_w{x}', f'{st["cls"]}_w{x}')
        self.emit_rec(st, rec)
        node = self.dag.nodes[rec['res'].node]
        use = self.holds_use(rec)
        val = f'(checked_value {rec["comp"].context} orig_w{x} {rec["ref"]} fixed {rec["res"].proof} {use})'
        if node.name == 'EConst':
            v = self.dag.integer(node.args[1]) % (1 << W)
            st['facts'][(W, x)] = v
            st['script'].append(
                f'assert(F{x}:norm {W}(read_signal fixed {x}%nat)={v}).\n'
                f'{{ rewrite(eq_w{x} seed fixed HL). rewrite{val}. vm_compute;reflexivity. }}')
        else:
            st['red'][x] = rec['red']
            st['script'].append(
                f'assert(R{x}:norm {W}(read_signal fixed {x}%nat)=norm {W}(eval_expr fixed {T.coq(rec["red"])})).\n'
                f'{{ rewrite(eq_w{x} seed fixed HL). apply f_equal. exact{val}. }}')

    def rewrite_chain(self, st, red):
        """Names R<y> of the non-constant wires reachable from the reduced expression, outer first."""
        order, seen, todo = [], set(), [red]
        while todo:
            e = todo.pop(0)
            for (w, y) in sorted(T.evars(e)):
                if y in st['red'] and y not in seen:
                    seen.add(y)
                    order.append(y)
                    todo.append(st['red'][y])
        return order

    # ---------------------------------------------------------------- targets
    def reads(self, c):
        f = lambda k: f'(norm {self.ast.sig[self.id[k]]["width"]}(read_signal fixed {self.id[k]}%nat))'
        a = f('a')
        b = f('b') if c['operand_b'] == 'rs2' else f('imm')
        return a, b, f('pc'), f('link')

    def expected(self, c):
        """(name, kind, expr-or-root, width, expected text) for the class, derived from the ISA class."""
        i = self.id
        rd = f'(norm 5(read_signal fixed {i["rd"]}%nat))'
        a, b, pc, link = self.reads(c)
        ifpc = f'(norm 32(read_signal fixed {i["ifpc"]}%nat))'
        bm = f'(norm 1(read_signal fixed {i["bmux"]}%nat))'
        imm = f'(norm 32(read_signal fixed {i["imm"]}%nat))'
        out = []
        if c['writes_rd']:
            val = sub(c['value'], a, b, pc, link)
            out.append(('rf', 'stmt', 'rf_value', f'if Z.eqb 0 {rd} then 0 else norm 32({val})'))
        else:
            out.append(('rf', 'stmt', 'rf_value', f'if Z.eqb 0 {rd} then 0 else norm 32(read_signal fixed {i["dreg"]}%nat)'))
        target = f'norm 32({pc} + {imm})'
        jalr_t = f'Z.shiftl(Z.shiftr(norm 32({a} + {imm}))1)1'
        k = c['kind']
        if k == 'dataop':
            jreq, flush, fpc = '0', '0', f'norm 32({ifpc} + 4)'
        elif k == 'jal':
            jreq, flush, fpc = '1', '2', target
        elif k == 'jalr':
            jreq, flush, fpc = '1', '2', f'norm 32({jalr_t})'
        else:
            jreq, flush = bm, f'if Z.eqb {bm} 0 then 0 else 2'
            fpc = f'if Z.eqb {bm} 0 then norm 32({ifpc} + 4) else {target}'
        out.append(('flush', 'stmt', 'next_flush', flush))
        out.append(('fpc', 'stmt', 'next_fetch_pc', fpc))
        out.append(('jreq', 'wire', i['jreq'], jreq))
        if k == 'jal' or k == 'branch':
            out.append(('jval', 'wire', i['jval'], target))
        if k == 'jalr':
            out.append(('jval', 'wire', i['jval'], f'norm 32({jalr_t})'))
        if k == 'branch':
            out.append(('bmux', 'wire', i['bmux'], f'boolz({sub(c["cond"], a, b, pc, link)})'))
        for nm in ('ddreq', 'drd', 'dwr'):
            out.append((nm, 'wire', i[nm], '0'))
        return out

    def premises(self, c):
        i = self.id
        prem = [(1, i['xres'], 0), (1, i['halt'], 0), (2, i['flush'], 0)]
        for f in self.flagregs:
            prem.append((1, f['reg']['id'], 1 if f['opcode'] == c['opcode'] else 0))
        if c['funct3'] is not None:
            prem.append((3, i['f3'], c['funct3']))
        if c['funct7'] is not None:
            prem.append((7, i['f7'], c['funct7']))
        return prem

    def gen_class(self, c):
        name = c['name']
        prem = self.premises(c)
        st = dict(cls=name, facts={(w, x): v for w, x, v in prem}, derived=set(), probed=set(), red={}, out=[], script=[])
        pdef = ' /\\ '.join(f'norm {w}(read_signal f {x}%nat)={v}' for w, x, v in prem)
        bind = ''
        for k, (w, x, v) in enumerate(prem):
            bind = bind + f'F{x}' if k == 0 else bind
        pat = f'F{prem[-1][1]}'
        for (_w, _x, _v) in reversed(prem[:-1]):
            pat = f'[F{_x} {pat}]'
        concl, proofs = [], []
        for (tn, kind, ref, exp) in self.expected(c):
            if kind == 'stmt':
                rhs = self.target_orig(ref)
                ext, W = f'orig_t_{ref}', rhs[1]
                rec = self.settle(st, rhs, ext, f'{name}_t{tn}')
                self.emit_rec(st, rec)
                use = self.holds_use(rec)
                val = f'(checked_value {rec["comp"].context} {ext} {rec["ref"]} fixed {rec["res"].proof} {use})'
                stmt = f'norm {W}(eval_expr fixed {ext})={exp}'
                lit = T.coq(rec['red'])
                pre = f'assert(E0:eval_expr fixed {ext}=eval_expr fixed {lit})by exact{val}. rewrite(f_equal(norm {W})E0).'
                red = rec['red']
            else:
                W = self.ast.comb[ref]['width']
                self.derive(st, ref)
                stmt = f'norm {W}(read_signal fixed {ref}%nat)={exp}'
                if (W, ref) in st['facts']:
                    pre = f'rewrite F{ref}.'
                    red = None
                else:
                    pre = f'rewrite R{ref}.'
                    red = st['red'][ref]
            chain = self.rewrite_chain(st, red) if red else []
            rws = '|'.join(f'rewrite R{y}' for y in chain)
            body = pre + ' cbn[eval_expr].'
            if rws:
                body += f' repeat((first[{rws}]);cbn[eval_expr]).'
            body += ' tmpl_close.'
            concl.append((f'T{tn}', stmt))
            proofs.append(f'assert(T{tn}:{stmt}).\n{{ {body} }}')
        cstmt = ' /\\ '.join(f'({s})' for _, s in concl)
        conj = ''
        names = [n for n, _ in concl]
        conj = names[-1]
        for n in reversed(names[:-1]):
            conj = f'(conj {n} {conj})'
        text = [f'Definition prem_{name}(f:State):Prop:={pdef}.'] + st['out'] + [
            f'Theorem {name}_controls seed fixed:CombLFP P seed fixed->prem_{name} fixed->{cstmt}.',
            f'Proof. intros HL HP. destruct HP as {pat}.'] + st['script'] + proofs + [f'exact {conj}. Qed.']
        return '\n'.join(text) + '\n', [n for n, _ in concl]


PREAMBLE = r"""From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVCheckedAssignmentBinding Lang.ExtendedSVConditionalReduction
 Lang.ExtendedSVConditionalReductionAlgebra Lang.ExtendedSVWordInvariant Lang.ExtendedSVStallFlush Lang.ExtendedSVBankAlignment @AST@.
Import ListNotations ExtendedSV ExtendedSVCheckedAssignmentBinding ExtendedSVConditionalReduction
 ExtendedSVConditionalReductionAlgebra ExtendedSVWordInvariant ExtendedSVStallFlush @ASTNS@.
Local Open Scope Z_scope.
Definition P:=@PROG@.
Fixpoint stmt_at(s:Stmt)(path:list nat):Stmt:=match path with nil=>s|i::r=>match s with
 |SSeq l=>stmt_at(nth i l SSkip)r|SIf _ y n=>stmt_at(if Nat.eqb i 0 then y else n)r|_=>SSkip end end.
Definition rhs_of(s:Stmt):Expr:=match s with SAssign _ e _=>e|_=>EConst 0 0 end.
Lemma norm_0 w:norm w 0=0.
Proof. unfold norm. apply Z.land_0_l. Qed.
Lemma norm_1_boolz b:norm 1(boolz b)=boolz b.
Proof. destruct b;reflexivity. Qed.
Lemma norm_32_boolz b:norm 32(boolz b)=boolz b.
Proof. destruct b;reflexivity. Qed.
Lemma norm31_shiftr32 v:norm 31(Z.shiftr(norm 32 v)1)=Z.shiftr(norm 32 v)1.
Proof. pose proof(ExtendedSVBankAlignment.norm_bounds 32 v)as[H0 H1].
 rewrite(ExtendedSVBankAlignment.norm_mod 31(Z.shiftr(norm 32 v)1)).
 rewrite Z.shiftr_div_pow2 by lia. apply Z.mod_small. split.
 - apply Z.div_pos;[lia|apply Z.pow_pos_nonneg;lia].
 - apply Z.div_lt_upper_bound;[apply Z.pow_pos_nonneg;lia|]. cbn in *. lia. Qed.
Ltac norm_lits:=repeat match goal with
 |_:_|-context[norm ?w ?v]=>
  lazymatch v with context[read_signal _ _]=>fail|_=>idtac end;
  let r:=eval vm_compute in(norm w v)in change(norm w v)with r end.
Ltac tmpl_simp:=try cbn [expr_width]; repeat rewrite ?norm_0,?norm_idempotent,?Z.lor_0_l,?Z.lor_0_r,?norm_1_boolz,?norm_32_boolz,
 ?Z.gtb_ltb,?Z.shiftr_0_r,?norm31_shiftr32.
Ltac tmpl_close :=
 tmpl_simp; norm_lits;
 repeat match goal with
 |_:_|-context[norm 1(read_signal ?f ?r)]=>destruct(one_bit_cases f r)as[Hb|Hb];rewrite ?Hb
 |_:_|-context[Z.eqb 0(norm ?w(read_signal ?f ?r))]=>destruct(Z.eqb 0(norm w(read_signal f r)))eqn:?
 |_:_|-context[Z.eqb(norm ?w(read_signal ?f ?r))(norm ?w2(read_signal ?f2 ?r2))]=>destruct(Z.eqb(norm w(read_signal f r))(norm w2(read_signal f2 r2)))eqn:?
 |_:_|-context[Z.ltb ?x ?y]=>lazymatch x with context[read_signal _ _]=>destruct(Z.ltb x y)eqn:? end
 end;
 cbn -[Z.add Z.mul Z.sub Z.land Z.lor Z.lxor Z.shiftl Z.shiftr Z.lnot norm signed_value];
 tmpl_simp; norm_lits;
 cbn -[Z.add Z.mul Z.sub Z.land Z.lor Z.lxor Z.shiftl Z.shiftr Z.lnot norm signed_value];
 tmpl_simp;
 first[reflexivity|(f_equal;lia)|idtac].
"""


def build(design, names, module):
    g = Gen(design, module)
    cls = [c for c in isa.classes() if names == 'all' or c['name'] in names.split(',')]
    body, index = [], {}
    for c in cls:
        txt, tnames = g.gen_class(c)
        body.append(txt)
        index[c['name']] = tnames
    pre = PREAMBLE.replace('@AST@', g.ast_module).replace('@ASTNS@', g.ast_module.split('.')[-1]).replace('@PROG@', g.prog)
    hdr = (f'(** {design}: per-class controller facts from the ISA class table, generated by tools/cpu_tmpl_controls.py.\n'
           f'    proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. Generated; do not edit. *)\n')
    text = hdr + pre + f'Module {module}.\n' + '\n'.join(g.head) + '\n' + '\n'.join(body) + f'End {module}.\n'
    exports = [f'{module}.{c["name"]}_controls' for c in cls]
    text += ''.join(f'Print Assumptions {e}.\n' for e in exports)
    return text, exports, index


def run_accept(design, names, module, namespace, out):
    import cpu_tmpl_accept as acc
    text, exports, index = build(design, names, module)
    g = Gen(design, module)
    lp = [(d['directory'], d['namespace']) for d in json.loads(Path(f'framework/auto-contract-profiles/{design}.json').read_text())['coq_load_paths']
          if d['namespace'] == 'Dark38']
    r = acc.accept(out, namespace, module, text, exports, lp, extra=dict(
        generator='tools/cpu_tmpl_controls.py', classes=len(index), design=design,
        ast_sha256=acc.sha(g.ast.file), target_index=index))
    return r


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--design', default='darkriscv')
    ap.add_argument('--classes', default='all')
    ap.add_argument('--module', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--namespace')
    ap.add_argument('--accept', action='store_true', help='run the acceptance gate into --out (a new results dir)')
    a = ap.parse_args()
    if a.accept:
        r = run_accept(a.design, a.classes, a.module, a.namespace, a.out)
        print(json.dumps({k: r[k] for k in r if k != 'target_index'}, indent=1))
        sys.exit(0 if r['accepted'] else 1)
    text, exports, index = build(a.design, a.classes, a.module)
    Path(a.out).write_text(text)
    print(a.out, len(text.splitlines()), 'lines;', len(exports), 'exports')
