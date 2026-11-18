"""Narrow-LLM frontend extension: inline pure straight-line local-assignment
functions from their original elaborated XML bodies; no RTL edits or assumed
comparison semantics. This translation remains outside the Coq proof boundary.
"""
import sys,copy,json,hashlib
from pathlib import Path
D=Path(__file__).resolve().parent;R=D.parent;sys.path.insert(0,str(D))
import cpu_array_frontend as F
original=F.ArrayTranslator.expr
calls=[]
def expand(self,node,env):
 if node.tag!='funcref':return original(self,node,env)
 name=node.get('name');defs=[f for f in self.root.iter('func') if f.get('name')==name]
 if len(defs)!=1:raise ValueError('pure function definition is not unique: '+name)
 fun=defs[0];decl={v.get('name'):v for v in fun.findall('var')};inputs=[v for v in fun.findall('var') if v.get('dir')=='input'];args=list(node)
 if len(inputs)!=len(args):raise ValueError('pure function arity mismatch')
 bound={}
 for formal,arg in zip(inputs,args):
  if arg.tag!='arg' or len(arg)!=1:raise ValueError('unsupported function argument')
  if self.dtype_width(formal.get('dtype_id'))!=self.width(arg[0]):raise ValueError('argument width mismatch requires explicit conversion')
  bound[formal.get('name')]=copy.deepcopy(arg[0])
 def subst(expr):
  if expr.tag=='varref':
   if expr.get('name') not in bound:raise ValueError('function reads external/uninitialized variable '+expr.get('name'))
   return copy.deepcopy(bound[expr.get('name')])
  if expr.tag in {'funcref','taskref','ccall'}:raise ValueError('nested/effectful function unsupported')
  out=copy.deepcopy(expr);out[:]=[subst(c) for c in expr];return out
 def statement(st):
  if st.tag=='var':return
  if st.tag=='begin':
   for ch in st:statement(ch)
  elif st.tag=='assign' and len(st)==2 and st[1].tag=='varref':
   target=st[1].get('name')
   if target not in decl or decl[target].get('dir')=='input':raise ValueError('function writes nonlocal/input')
   value=subst(st[0]);width=self.dtype_width(decl[target].get('dtype_id'))
   if self.width(value)!=width:raise ValueError('function assignment requires explicit width conversion')
   bound[target]=value
  else:raise ValueError('unsupported pure-function statement '+st.tag)
 for st in fun:statement(st)
 if name not in bound:raise ValueError('function return undefined')
 if self.width(bound[name])!=self.width(node):raise ValueError('function result width mismatch')
 calls.append({'function':name,'call_location':node.get('loc'),'original_function_xml_sha256':hashlib.sha256(F.ET.tostring(fun)).hexdigest()})
 self.runtime_tags['pure_function_inline']+=1
 return self.expr(bound[name],env)
F.ArrayTranslator.expr=expand
sensitivity=[]
concat_ports=[]
def reads(node):return {v.get('name') for v in node.iter('varref')}
def flow(st,defined):
 if st.tag=='begin':
  needed=set();written=set();state=set(defined)
  for ch in st:
   req,state,w=flow(ch,state);needed|=req;written|=w
  return needed,state,written
 if st.tag=='assign' and len(st)==2 and st[1].tag=='varref':
  target=st[1].get('name');return reads(st[0])-defined,defined|{target},{target}
 if st.tag=='if':
  need=reads(st[0])-defined; branches=[flow(st[1],set(defined)),flow(st[2],set(defined)) if len(st)==3 else (set(),set(defined),set())]
  return need|set.union(*(a for a,b,c in branches)),set.intersection(*(b for a,b,c in branches)),set.union(*(c for a,b,c in branches))
 if st.tag=='case':
  need=reads(st[0])-defined;branches=[];default=False
  for arm in list(st)[1:]:
   if arm.tag!='caseitem':raise ValueError('non-caseitem in sensitivity analysis')
   ch=list(arm);body=ch[-1] if ch and ch[-1].tag in {'begin','assign','if','case'} else None
   keys=ch[:-1] if body is not None else ch
   default|=not keys
   for key in keys:need|=reads(key)-defined
   branches.append(flow(body,set(defined)) if body is not None else (set(),set(defined),set()))
  if not default:branches.append((set(),set(defined),set()))
  return need|set.union(*(a for a,b,c in branches)),set.intersection(*(b for a,b,c in branches)),set.union(*(c for a,b,c in branches))
 raise ValueError('unsupported statement in sensitivity completeness check: '+st.tag)
old_init=F.ArrayTranslator.__init__
def init(self,root,top):
 def leaves(n):
  if n.tag=='concat':return [x for c in n for x in leaves(c)]
  if n.tag not in {'varref','sel','arraysel'}:raise ValueError('unsupported output concatenation target')
  return [n]
 # Split output concatenations using a fresh combinational wire; preserve port width.
 dtypes={d.get('id'):d for d in root.findall('./netlist/typetable/*')}
 def width(n):
  d=dtypes[n.get('dtype_id')]
  if d.tag!='basicdtype':raise ValueError('concat leaf width is not basic')
  return abs(int(d.get('left','0'))-int(d.get('right','0')))+1
 consttype=next(k for k,d in dtypes.items() if d.tag=='basicdtype' and d.get('left')=='31' and d.get('right')=='0' and d.get('signed') not in {'true','1'})
 for module in root.iter('module'):
  for inst in module.iter('instance'):
   for port in inst.findall('port'):
    if port.get('direction')!='out' or len(port)!=1 or port[0].tag!='concat':continue
    expr=port[0];pieces=leaves(expr);total=width(expr)
    if sum(width(n) for n in pieces)!=total:raise ValueError('concat widths inconsistent')
    name='__cold_intake_concat_'+str(len(concat_ports))
    if any(v.get('name')==name for v in module.iter('var')):raise ValueError('fresh concat name collision')
    module.append(F.ET.Element('var',{'name':name,'dtype_id':expr.get('dtype_id'),'loc':port.get('loc','')}))
    def ref():return F.ET.Element('varref',{'name':name,'dtype_id':expr.get('dtype_id')})
    port.remove(expr);port.append(ref());offset=total
    for leaf in pieces:
     offset-=width(leaf);assign=F.ET.Element('contassign',{'loc':port.get('loc','')});rhs=F.ET.Element('sel',{'dtype_id':leaf.get('dtype_id')});rhs.append(ref())
     rhs.append(F.ET.Element('const',{'name':"32'h"+format(offset,'x'),'dtype_id':consttype}));rhs.append(F.ET.Element('const',{'name':"32'h"+format(width(leaf),'x'),'dtype_id':consttype}));assign.extend([rhs,copy.deepcopy(leaf)]);module.append(assign)
    concat_ports.append({'module':module.get('name'),'instance':inst.get('name'),'port':port.get('name'),'temporary':name,'width':total,'leaf_widths':[width(n) for n in pieces]})
 for m in root.iter('module'):
  for a in m.iter('always'):
   sentree=a.find('sentree')
   if sentree is None or not any(x.get('edgeType')=='ANY' for x in sentree):continue
   if not all(x.get('edgeType')=='ANY' and len(x)==1 and x[0].tag=='varref' for x in sentree):raise ValueError('mixed ANY sensitivity not supported')
   listed={x[0].get('name') for x in sentree};need=set();defined=set();written=set()
   for st in a:
    if st.tag=='sentree':continue
    req,defined,wr=flow(st,defined);need|=req;written|=wr
   if not need<=listed:raise ValueError('incomplete sensitivity: '+str(need-listed))
   if not written<=defined:raise ValueError('possible latch in explicit sensitivity block')
   sensitivity.append({'module':m.get('name'),'location':a.get('loc'),'listed':sorted(listed),'external_reads_before_write':sorted(need),'definitely_assigned_outputs':sorted(defined),'normalization':'complete level-sensitive combinational block'})
   a.remove(sentree)
 old_init(self,root,top)
F.ArrayTranslator.__init__=init
from srv32_frontend import PaddedBankTranslator
class BoundedLoopTranslator(F.ArrayTranslator):
 unrolled_loops=[]
 _loop_unroll=PaddedBankTranslator._loop_unroll
 def stmt(self,node,env):
  if node.tag=='begin':
   kids=[c for c in node if c.tag not in {'sentree','var'}]
   if any(c.tag=='while' for c in kids):
    parts=[];k=0
    while k<len(kids):
     if k+1<len(kids) and kids[k+1].tag=='while':parts.append(self._loop_unroll(kids[k],kids[k+1],env));k+=2
     elif kids[k].tag=='while':raise ValueError('while without constant init')
     else:parts.append(self.stmt(kids[k],env));k+=1
    return 'SSeq ['+'; '.join(parts)+']'
  return super().stmt(node,env)
original_items=F.ArrayTranslator.module_items
def items(self,node,env,path):
 filtered=copy.copy(node);filtered[:]=[c for c in node if c.tag!='func']
 return original_items(self,filtered,env,path)
BoundedLoopTranslator.module_items=items
F.ArrayTranslator=BoundedLoopTranslator
try:code=F.main()
finally:(Path(sys.argv[sys.argv.index('--xml')+1]).parent/'function-inlining.json').write_text(json.dumps({'author':'OpenAI Codex narrow LLM','method':'substitute actual arguments and sequential local assignments in original XML, preserve widths, reject nonlocal effects','calls':calls,'complete_sensitivity_blocks':sensitivity,'bounded_loops':BoundedLoopTranslator.unrolled_loops,'output_concat_lowering':concat_ports,'translation_equivalence':'not_mechanized'},indent=2))
sys.exit(code)
