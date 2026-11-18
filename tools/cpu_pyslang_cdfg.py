"""Typed, ordered candidate dependency graph. Never a substitute for Coq semantics."""
import pyslang as slang


def refs(expr):
    result = set()
    def visit(node):
        if isinstance(node, slang.ast.NamedValueExpression):
            result.add(node.symbol.hierarchicalPath)
    expr.visit(visit)
    return sorted(result)


class Graph:
    def __init__(self, compilation, bindings):
        self.compilation = compilation
        self.symbols = {s['path']: s for s in bindings}
        self.processes = []
        self.edges = []
        self.obligations = []

    def location(self, node):
        loc = node.location if hasattr(node, 'location') else node.sourceRange.start
        sm = self.compilation.sourceManager
        return dict(file=str(sm.getFileName(loc)), line=sm.getLineNumber(loc))

    def expr(self, e):
        kind = type(e).__name__
        out = dict(kind=kind, width=e.type.bitWidth, signed=e.type.isSigned,
                   location=self.location(e), reads=refs(e))
        if kind == 'NamedValueExpression':
            out['symbol'] = e.symbol.hierarchicalPath
        elif kind in ('IntegerLiteral', 'UnbasedUnsizedIntegerLiteral'):
            out['value'] = str(e.value)
        elif kind in ('BinaryExpression', 'RangeSelectExpression'):
            out.update(left=self.expr(e.left), right=self.expr(e.right))
            if kind == 'BinaryExpression': out['op'] = str(e.op)
            else: out.update(value=self.expr(e.value), selection=str(e.selectionKind))
        elif kind in ('UnaryExpression', 'ConversionExpression'):
            out['operand'] = self.expr(e.operand)
            out['operation'] = str(e.op if kind == 'UnaryExpression' else e.conversionKind)
        elif kind == 'ElementSelectExpression':
            out.update(value=self.expr(e.value), selector=self.expr(e.selector))
        elif kind == 'ConcatenationExpression':
            out['operands'] = [self.expr(a) for a in e.operands]
        elif kind == 'ReplicationExpression':
            out.update(count=self.expr(e.count), concat=self.expr(e.concat))
        elif kind == 'ConditionalExpression':
            out.update(conditions=[self.expr(c.expr) for c in e.conditions],
                       left=self.expr(e.left), right=self.expr(e.right))
            if any(c.pattern is not None for c in e.conditions):
                self.obligations.append(dict(reason='pattern condition', **self.location(e)))
        elif kind == 'CallExpression' and e.isSystemCall and e.subroutineName in ('$signed', '$unsigned'):
            out.update(operation=e.subroutineName, arguments=[self.expr(a) for a in e.arguments])
        elif kind == 'EmptyArgumentExpression':
            out['role'] = 'output_port_placeholder'
        elif kind == 'AssignmentExpression':
            out.update(left=self.expr(e.left), right=self.expr(e.right), nonblocking=e.isNonBlocking)
        else:
            self.obligations.append(dict(reason='unsupported expression '+kind, **self.location(e)))
            out['unsupported'] = True
        return out

    def assign(self, lhs, rhs, process, guard, nba=False):
        left, right = self.expr(lhs), self.expr(rhs)
        base = lhs
        while type(base).__name__ in ('ElementSelectExpression', 'RangeSelectExpression'):
            base = base.value
        if not isinstance(base, slang.ast.NamedValueExpression):
            self.obligations.append(dict(reason='unsupported assignment destination', **self.location(lhs)))
            return dict(kind='unsupported_assignment', left=left, right=right)
        target = base.symbol.hierarchicalPath
        index = len(self.edges)
        self.edges.append(dict(id=index, process=process, target=target,
                               data=refs(rhs), address=[x for x in refs(lhs) if x != target],
                               guards=guard, assignment='nonblocking' if nba else 'blocking',
                               reads_version='procedural_current', writes_version='next' if nba else 'procedural_current',
                               left=left, right=right))
        return dict(kind='assignment', edge=index)

    def statement(self, st, process, guards):
        if st is None: return dict(kind='empty')
        kind = type(st).__name__
        if kind == 'BlockStatement':
            return dict(kind=kind, block_kind=str(st.blockKind), body=self.statement(st.body,process,guards))
        if kind == 'StatementList':
            return dict(kind=kind, ordered=[self.statement(a,process,guards) for a in st.list])
        if kind == 'ExpressionStatement' and isinstance(st.expr, slang.ast.AssignmentExpression):
            e=st.expr
            if e.isCompound or e.timingControl is not None:
                self.obligations.append(dict(reason='compound or timed assignment', **self.location(e)))
            return self.assign(e.left,e.right,process,guards,e.isNonBlocking)
        if kind == 'ConditionalStatement':
            cond=[self.expr(c.expr) for c in st.conditions]
            if any(c.pattern is not None for c in st.conditions):
                self.obligations.append(dict(reason='statement pattern', **self.location(st)))
            return dict(kind=kind, condition=cond,
                then=self.statement(st.ifTrue,process,guards+[dict(condition=cond,taken=True)]),
                otherwise=self.statement(st.ifFalse,process,guards+[dict(condition=cond,taken=False)]))
        if kind == 'CaseStatement':
            selector=self.expr(st.expr);prior=[];items=[]
            for item in st.items:
                values=[self.expr(v) for v in item.expressions]
                guard=dict(selector=selector, values=values, excluded=prior.copy(), condition=str(st.condition))
                items.append(dict(values=values, body=self.statement(item.stmt,process,guards+[guard])))
                prior.extend(values)
            return dict(kind=kind,selector=selector,items=items,
                default=self.statement(st.defaultCase,process,guards+[dict(selector=selector,excluded=prior,default=True)]))
        if kind == 'TimedStatement':
            return dict(kind=kind, timing=self.timing(st.timing), body=self.statement(st.stmt,process,guards))
        if kind == 'EmptyStatement': return dict(kind=kind)
        self.obligations.append(dict(reason='unsupported statement '+kind, **self.location(st)))
        return dict(kind=kind, unsupported=True)

    def timing(self,t):
        kind=type(t).__name__
        if kind == 'EventListControl': return dict(kind=kind,events=[self.timing(x) for x in t.events])
        if kind == 'SignalEventControl':
            return dict(kind=kind,edge=str(t.edge),expr=self.expr(t.expr),
                        iff=self.expr(t.iffCondition) if t.iffCondition is not None else None)
        if kind == 'ImplicitEventControl': return dict(kind=kind)
        self.obligations.append(dict(reason='unsupported timing '+kind))
        return dict(kind=kind,unsupported=True)

    def extract(self,root):
        def visit(node):
            if isinstance(node, slang.ast.ProceduralBlockSymbol):
                i=len(self.processes)
                self.processes.append(dict(id=i,instance=node.hierarchicalPath,kind=str(node.procedureKind),
                    location=self.location(node),body=self.statement(node.body,i,[])))
            elif isinstance(node, slang.ast.ContinuousAssignSymbol):
                i=len(self.processes);a=node.assignment
                self.processes.append(dict(id=i,instance=node.hierarchicalPath,kind='continuous',
                    location=self.location(node),body=self.assign(a.left,a.right,i,[])))
            elif isinstance(node, slang.ast.InstanceSymbol):
                for conn in node.portConnections:
                    port=conn.port
                    if conn.expression is None: continue
                    i=len(self.processes)
                    # Keep port objects explicitly; do not invent expression objects.
                    direction=str(port.direction)
                    if direction not in ('ArgumentDirection.In','ArgumentDirection.Out'):
                        self.obligations.append(dict(reason='unsupported port direction',port=port.hierarchicalPath));continue
                    self.processes.append(dict(id=i,kind='port',direction=direction,
                        port=port.hierarchicalPath,expression=self.expr(conn.expression),
                        location=self.location(port)))
                    expr=conn.expression
                    if direction == 'ArgumentDirection.In':
                        target=port.hierarchicalPath; reads=refs(expr)
                    elif isinstance(expr,slang.ast.AssignmentExpression) and isinstance(expr.left,slang.ast.NamedValueExpression):
                        target=expr.left.symbol.hierarchicalPath
                        reads=[port.hierarchicalPath]
                    else:
                        self.obligations.append(dict(reason='non-scalar output connection',port=port.hierarchicalPath));continue
                    self.edges.append(dict(id=len(self.edges),process=i,target=target,data=reads,
                        address=[],guards=[],assignment='port_connection',reads_version='current',
                        writes_version='current',expression=self.expr(expr)))
        root.visit(visit)
        return dict(symbols=list(self.symbols.values()),processes=self.processes,edges=self.edges,
                    obligations=self.obligations, translation_equivalence_proved=False,
                    execution_model='ordered syntax only; original Coq semantics remains authoritative')


def dependencies(edge):
    """Conservative dependencies, including all guards and destination selectors."""
    result=set(edge['data']) | set(edge['address'])
    def visit(x):
        if isinstance(x,dict):
            result.update(x.get('reads',[]))
            for value in x.values(): visit(value)
        elif isinstance(x,list):
            for value in x: visit(value)
    visit(edge['guards'])
    return result


def backward_slice(graph, target):
    """Stop at sequential writers; return their timing/control obligations intact."""
    symbols={s['path']:s for s in graph['symbols']}
    if target not in symbols: raise ValueError('unknown query target')
    writers={}
    for edge in graph['edges']: writers.setdefault(edge['target'],[]).append(edge)
    processes={p['id']:p for p in graph['processes']}
    nodes={};boundaries={};active=set()
    def walk(path):
        if path in nodes or path in boundaries:return
        if path in active:raise ValueError('combinational cycle in queried slice')
        edges=writers.get(path,[])
        if not edges:
            boundaries[path]='external_or_unresolved';return
        # Explicit timed statements are sequential; implicit @* is combinational.
        def clocked(x):
            if isinstance(x,dict):
                return x.get('kind')=='SignalEventControl' or any(clocked(v) for v in x.values())
            return isinstance(x,list) and any(clocked(v) for v in x)
        if any(clocked(processes[e['process']]) for e in edges):
            boundaries[path]='sequential';return
        if len({e['process'] for e in edges})!=1:raise ValueError('ambiguous writer')
        active.add(path)
        deps=sorted(set().union(*(dependencies(e) for e in edges)))
        for dep in deps:walk(dep)
        active.remove(path)
        nodes[path]=dict(symbol=symbols[path],dependencies=deps,edges=[e['id'] for e in edges])
    walk(target)
    return dict(target=target,nodes=list(nodes.values()),boundaries=boundaries,
                obligations=graph['obligations'],proof_status='candidate_not_proved')
