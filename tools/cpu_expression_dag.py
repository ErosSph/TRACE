"""Untrusted, width-preserving Expr DAG analysis; emits no proof claims.

No DUT, opcode, root, or phase is built in. A caller may attach opaque context
metadata; expressions never acquire facts from that metadata. Facts must be
supplied explicitly as (width, signal) bindings and checked by the Coq caller.
"""
from collections import Counter
from dataclasses import dataclass
import re


@dataclass(frozen=True)
class Node:
    name: str
    args: tuple[int, ...] = ()


ARITY={'EConst':2,'EVar':2,'ESel':3,'EConcat':3,'EReplicate':3,
       'EExtend':3,'EUnary':3,'EBinary':4,'ECond':4}


def strip_comments(source):
    result=[];depth=0;index=0
    while index<len(source):
        token=source[index:index+2]
        if token=='(*':depth+=1;index+=2;continue
        if token=='*)':
            if not depth:raise ValueError('unmatched comment end')
            depth-=1;index+=2;continue
        if not depth or source[index]=='\n':result.append(source[index])
        index+=1
    if depth:raise ValueError('unterminated comment')
    return ''.join(result)


def parse_term(text):
    """Parse the constructor/application fragment, rejecting trailing tokens."""
    tokens=re.findall(r'\(|\)|[^\s()]+',text);position=0
    def take():
        nonlocal position
        if position>=len(tokens):raise ValueError('incomplete term')
        token=tokens[position];position+=1
        if token==')':raise ValueError('unexpected closing parenthesis')
        if token!='(':return(token,())
        if position>=len(tokens):raise ValueError('missing application head')
        head=tokens[position];position+=1;args=[]
        while position<len(tokens)and tokens[position]!=')':args.append(take())
        if position>=len(tokens):raise ValueError('unclosed term')
        position+=1;return(head,tuple(args))
    result=take()
    if position!=len(tokens):raise ValueError('trailing term tokens')
    return result


class ExpressionDAG:
    def __init__(self, *, context=None):
        self.context=context
        self.nodes=[];self._intern={};self.definitions={};self._resolved={};self._active=set();self._inputs={}

    def node(self,name,args=()):
        item=Node(name,tuple(args))
        if item not in self._intern:
            self._intern[item]=len(self.nodes);self.nodes.append(item)
        return self._intern[item]

    def atom(self,value):return self.node(str(value))

    def integer(self,index):
        n=self.nodes[index]
        if n.args:raise ValueError('non-atomic integer')
        return int(re.sub(r'%(?:nat|Z|N)$','',n.name))

    @classmethod
    def from_coq(cls,source, *, namespace='',context=None):
        """Read Expr definitions/Module scopes; do not evaluate proof scripts.

        Unsupported Expr-producing applications are rejected when resolved.
        Module aliases are not copied or expanded.
        """
        dag=cls(context=context);scope=tuple(filter(None,namespace.split('.')))
        source=strip_comments(source)
        pattern=r'(?m)^\s*(?:Module\s+(\w+)\s*\.|End\s+(\w+)\s*\.|Definition\s+(\w+)\s*:\s*Expr\s*:=\s*(.*?)\.(?=\s|$))'
        for match in re.finditer(pattern,source,re.S):
            module,end,name,body=match.groups()
            if module:scope+= (module,)
            elif end:
                if scope and scope[-1]==end:scope=scope[:-1]
            else:
                key='.'.join((*scope,name))
                if key in dag.definitions:raise ValueError('duplicate Expr definition: '+key)
                dag.definitions[key]=(parse_term(body),scope)
        return dag

    def _lookup(self,name,scope):
        if name in self.definitions:return name
        for length in range(len(scope),-1,-1):
            key='.'.join((*scope[:length],name))
            if key in self.definitions:return key
        candidates=[key for key in self.definitions if key.endswith('.'+name)]
        if len(candidates)==1:return candidates[0]
        if candidates:raise ValueError('ambiguous Expr reference: '+name)
        return None

    def resolve(self,name,scope=()):
        key=self._lookup(name,tuple(scope))
        if key is None:raise ValueError('unresolved Expr reference: '+name)
        if key in self._resolved:return self._resolved[key]
        if key in self._active:raise ValueError('cyclic Expr reference: '+key)
        self._active.add(key)
        try:
            term,scope=self.definitions[key];result=self._lower(term,scope)
            if self.nodes[result].name not in ARITY:raise ValueError('not an Expr: '+key)
            self._resolved[key]=result;return result
        finally:self._active.remove(key)

    @classmethod
    def from_definitions(cls,definitions, *, context=None):
        """Load a caller-provided mapping of fully qualified Expr names."""
        dag=cls(context=context)
        for name,body in definitions.items():
            dag.definitions[name]=(parse_term(body),tuple(name.split('.')[:-1]))
        return dag

    def parse(self,text, *, scope=()):
        result=self._lower(parse_term(text),tuple(scope))
        if self.nodes[result].name not in ARITY:raise ValueError('root is not an Expr')
        return result

    def _lower(self,term,scope):
        name,args=term
        reference=self._lookup(name,scope)if not args else None
        if reference:return self.resolve(reference)
        if name=='substitute':
            if len(args)!=2 or args[0][0]!='assign_substitution' or len(args[0][1])!=3:
                raise ValueError('unsupported substitution; provide explicit caller bindings')
            w,x,rhs=args[0][1]
            return self.substitute(self._lower(args[1],scope),
                {(int(w[0]),int(x[0])):self._lower(rhs,scope)})
        if name=='fold_expression'and len(args)==1:return self.fold(self._lower(args[0],scope))
        if name in ARITY and len(args)!=ARITY[name]:raise ValueError('incorrect constructor arity: '+name)
        if args and name not in ARITY:raise ValueError('unsupported Expr application: '+name)
        return self.node(name,tuple(self._lower(a,scope)for a in args))

    def width(self,index):
        node=self.nodes[index]
        if node.name not in ARITY:raise ValueError('atom has no Expr width')
        return self.integer(node.args[0])

    def constant(self,width,value):return self.node('EConst',(self.atom(width),self.atom(value)))

    def inputs(self,root):
        if root not in self._inputs:
            node=self.nodes[root]
            self._inputs[root]=(frozenset({(self.integer(node.args[0]),self.integer(node.args[1]))})
                if node.name=='EVar'else frozenset().union(*(self.inputs(c)for c in node.args)))
        return self._inputs[root]

    def substitute(self,root,bindings):
        """Exact (width,root) lookup; insert the original unsigned EExtend."""
        memo={}
        def visit(index):
            if index in memo:return memo[index]
            node=self.nodes[index]
            if node.name=='EVar'and(key:=(self.integer(node.args[0]),self.integer(node.args[1])))in bindings:
                result=self.node('EExtend',(node.args[0],self.atom('false'),bindings[key]))
            else:result=self.node(node.name,tuple(visit(c)for c in node.args))
            memo[index]=result;return result
        return visit(root)

    def iter_nodes(self,root):
        """Yield (id, Node) once, children first; atoms are explicit nodes."""
        visited=set()
        def walk(index):
            if index in visited:return
            visited.add(index)
            for child in self.nodes[index].args:yield from walk(child)
            yield index,self.nodes[index]
        return walk(root)

    def eval_closed(self,root):
        """Evaluate supported fully closed syntax; None means unknown.

        Do not approximate signedness, unsupported operators, or variables.
        """
        if self.inputs(root):return None
        memo={}
        def signed(width,value):
            if width==0:return 0
            value%=1<<width
            return value-(1<<width)if value>=(1<<(width-1))else value
        def visit(index):
            if index in memo:return memo[index]
            n=self.nodes[index];a=n.args;z=None
            if n.name=='EConst':z=self.integer(a[1])%(1<<self.integer(a[0]))
            elif n.name=='ECond':
                g=visit(a[1])
                if g is not None:
                    value=visit(a[3]if g==0 else a[2])
                    if value is not None:z=value%(1<<self.integer(a[0]))
            elif n.name=='EExtend':
                x=visit(a[2])
                flag=self.nodes[a[1]].name
                if x is not None and flag in ('true','false'):
                    if flag=='true':x=signed(self.width(a[2]),x)
                    z=x%(1<<self.integer(a[0]))
            elif n.name=='ESel':
                x,y=visit(a[1]),visit(a[2])
                if x is not None and y is not None:z=(x>>y)%(1<<self.integer(a[0]))
            elif n.name=='EConcat':
                x,y=visit(a[1]),visit(a[2])
                if x is not None and y is not None:z=((x<<self.width(a[2]))|y)%(1<<self.integer(a[0]))
            elif n.name=='EUnary':
                x=visit(a[2]);op=self.nodes[a[1]].name
                operations={'UNot':lambda:~x,'UNegate':lambda:-x,'URedOr':lambda:int(x!=0)}
                if x is not None and op in operations:z=operations[op]()%(1<<self.integer(a[0]))
            elif n.name=='EReplicate':
                x=visit(a[2]);count=self.integer(a[1]);bw=self.width(a[2]);w=self.integer(a[0])
                if x is not None:
                    z=0
                    if bw:
                        for _ in range(min(count,(w+bw-1)//bw)):z=((z<<bw)|x)%(1<<w)
            elif n.name=='EBinary':
                x,y=visit(a[2]),visit(a[3]);op=self.nodes[a[1]].name
                if x is not None and y is not None:
                    w=self.integer(a[0])
                    operations={'BEq':lambda:int(x==y),'BNeq':lambda:int(x!=y),'BAnd':lambda:x&y,'BOr':lambda:x|y,
                        'BXor':lambda:x^y,'BAdd':lambda:x+y,'BSub':lambda:x-y,'BMul':lambda:x*y,
                        'BLtU':lambda:int(x<y),'BGtU':lambda:int(x>y),
                        'BGtS':lambda:int(signed(self.width(a[2]),x)>signed(self.width(a[3]),y)),
                        'BShiftL':lambda:0 if y>=w else x<<y,'BShiftR':lambda:x>>y,
                        'BShiftRS':lambda:signed(self.width(a[2]),x)>>y}
                    if op in operations:z=operations[op]()%(1<<self.integer(a[0]))
            memo[index]=z;return z
        return visit(root)

    def fold(self,root, *, same_width=None,mode=None):
        """Legacy closed/zero-AND/equal-arm fold; optional unsigned normalization.

        This is a candidate transformer, not a correctness certificate.
        """
        if mode is None:mode='enhanced'if same_width else 'legacy'
        if mode not in ('legacy','enhanced'):raise ValueError('unknown fold mode')
        if same_width is not None and same_width!=(mode=='enhanced'):raise ValueError('conflicting fold mode')
        same_width=mode=='enhanced'
        memo={}
        def visit(index):
            if index in memo:return memo[index]
            n=self.nodes[index];a=tuple(visit(c)for c in n.args);out=self.node(n.name,a)
            if n.name=='ECond':
                w,g,y,z=a
                if self.nodes[g].name=='EConst':out=self.node('EExtend',(w,self.atom('false'),z if self.eval_closed(g)==0 else y))
                elif y==z:out=self.node('EExtend',(w,self.atom('false'),y))
            if n.name=='EBinary'and self.nodes[a[1]].name=='BAnd'and any(self.nodes[c].name=='EConst'and self.eval_closed(c)==0 for c in a[2:]):out=self.constant(self.integer(a[0]),0)
            current=self.nodes[out]
            if same_width and current.name=='EExtend'and self.nodes[current.args[1]].name=='false'and self.width(current.args[2])==self.integer(current.args[0]):out=current.args[2]
            value=self.eval_closed(out)
            if self.nodes[out].name in ARITY and value is not None:out=self.constant(self.width(out),value)
            memo[index]=out;return out
        return visit(root)

    def cofactor(self,root,values, *, same_width=None,mode=None):
        return self.fold(self.substitute(root,{key:self.constant(key[0],value)for key,value in values.items()}),same_width=same_width,mode=mode)

    def stats(self,root):
        order=list(self.iter_nodes(root));sizes={}
        for key,node in order:sizes[key]=1+sum(sizes[c]for c in node.args)
        return dict(tree_nodes=sizes[root],dag_nodes=len(order),
            inputs=sorted({(self.integer(n.args[0]),self.integer(n.args[1]))for _,n in order if n.name=='EVar'}),
            constructors=dict(Counter(n.name for _,n in order if n.name in ARITY)),context=self.context)

    def to_coq(self,root, *, prefix='dag'):
        """Emit shared Expr Definitions, ending in Definition <prefix>_root."""
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',prefix):raise ValueError('invalid Coq prefix')
        lines=[];names={}
        for index,node in self.iter_nodes(root):
            if node.name not in ARITY:
                if node.args:raise ValueError('non-atomic constructor argument')
                names[index]=f'({node.name})'if re.fullmatch(r'-\d+(?:%Z)?',node.name)else node.name;continue
            name=f'{prefix}_{index}';names[index]=name
            lines.append(f'Definition {name}:Expr:=({node.name} '+ ' '.join(names[c]for c in node.args)+').')
        if root not in names or self.nodes[root].name not in ARITY:raise ValueError('root is not Expr')
        return '\n'.join(lines)+f'\nDefinition {prefix}_root:Expr:={names[root]}.\n'
