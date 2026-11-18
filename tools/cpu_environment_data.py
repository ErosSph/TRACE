"""Read a closed seed/write/event/phase fragment, never invariant declarations.

Unknown syntax is a residual. The generated data must also be compared with
the original named definitions by Coq; this parser is not a semantic oracle.
"""
import re
IDENT=r'[A-Za-z_][A-Za-z_0-9]*'
SYMBOL=IDENT+r'(?:\.'+IDENT+r')*'


def module_name(source):
    modules=re.findall(r'^Module\s+('+IDENT+r')\.',source,re.M)
    if len(modules)!=1:raise ValueError('one closed environment data module required')
    return modules[0]


def definition(source,name):
    if not re.fullmatch(IDENT,name):raise ValueError('simple data definition name required')
    matches=re.findall(r'^Definition\s+'+re.escape(name)+r'\b([\s\S]*?)\s*:=\s*([\s\S]*?)\.(?=\s|$)',source,re.M)
    if len(matches)!=1:raise ValueError('one named data definition required: '+name)
    return matches[0][0].strip(),' '.join(matches[0][1].split())


class Tokens:
    def __init__(self,text):
        self.items=re.findall(SYMBOL+r'|-?\d+|%nat|%Z|\S',text);self.pos=0
    def take(self):
        if self.pos>=len(self.items):raise ValueError('incomplete environment expression')
        item=self.items[self.pos];self.pos+=1;return item
    def expect(self,item):
        if self.take()!=item:raise ValueError('unsupported environment expression, expected '+item)
    def peek(self):
        if self.pos>=len(self.items):raise ValueError('incomplete environment expression')
        return self.items[self.pos]
    def integer(self,natural=False):
        value=self.take()
        if not re.fullmatch(r'-?\d+',value)or(natural and int(value)<0):raise ValueError('literal environment integer required')
        if self.pos<len(self.items)and self.items[self.pos]in['%nat','%Z']:self.pos+=1
        return int(value)
    def done(self):
        if self.pos!=len(self.items):raise ValueError('unconsumed environment syntax')


def seed_data(source,name):
    parameter,body=definition(source,name)
    if not re.fullmatch(IDENT,parameter):raise ValueError('one untyped seed parameter supported')
    tokens=Tokens(body)
    def value():
        if tokens.peek()=='(':
            tokens.take();result=value();tokens.expect(')');return result
        if re.fullmatch(r'-?\d+',tokens.peek()):return dict(kind='literal',value=tokens.integer())
        function=tokens.take()
        if not re.fullmatch(SYMBOL,function)or tokens.take()!=parameter:raise ValueError('single image-function application required')
        return dict(kind='image',function=function)
    def state():
        head=tokens.take()
        if head=='(':
            result=state();tokens.expect(')');return result
        if head=='repeat':
            if tokens.integer()!=0:raise ValueError('zero seed constructor required')
            return dict(length=tokens.integer(True),writes=[])
        if head!='write_signal':raise ValueError('closed repeat/write seed fragment required')
        result=state();root=tokens.integer(True);data=value();result['writes'].append(dict(root=root,value=data));return result
    result=state();tokens.done();functions={w['value']['function']for w in result['writes']if w['value']['kind']=='image'}
    if len(functions)!=1:raise ValueError('exactly one image application kind required')
    return dict(parameter=parameter,image_function=next(iter(functions)),**result)


def event_data(source,name):
    parameter,body=definition(source,name)
    if parameter:raise ValueError('event must be a closed record')
    if not(body.startswith('{|')and body.endswith('|}')):raise ValueError('closed Event record required')
    fields={}
    for field in body[2:-2].split(';'):
        if not field.strip():continue
        match=re.fullmatch(r'\s*('+IDENT+r')\s*:=\s*(-?\d+)(?:%nat|%Z)?\s*',field)
        if match is None or match[1]in fields:raise ValueError('literal distinct Event fields required')
        fields[match[1]]=int(match[2])
    if set(fields)!={'changed_signal','old_value','new_value'}or fields['changed_signal']<0:raise ValueError('exact Event fields required')
    return fields


def boot_data(source,name,seed_name,program):
    parameter,body=definition(source,name)
    if not re.fullmatch(IDENT,parameter):raise ValueError('one boot parameter required')
    tokens=Tokens(body);aliases=set()
    def phase():
        head=tokens.take()
        if head=='(':
            result=phase();tokens.expect(')');return result
        if head==seed_name:
            if tokens.take()!=parameter:raise ValueError('boot must use its actual seed parameter')
            return []
        if not re.fullmatch(IDENT,head):raise ValueError('closed phase alias required')
        aliases.add(head);event=tokens.take()
        if not re.fullmatch(IDENT,event):raise ValueError('closed named event required')
        return phase()+[event]
    events=phase();tokens.done()
    if not events or len(aliases)!=1:raise ValueError('one actual phase alias and nonempty boot required')
    alias=next(iter(aliases));args,alias_body=definition(source,alias);args=args.split()
    if len(args)!=2 or not all(re.fullmatch(IDENT,arg)for arg in args):raise ValueError('two-argument phase alias required')
    match=re.fullmatch(r'PhaseSemantics\s+('+SYMBOL+r')\s+'+re.escape(args[0])+r'\s+'+re.escape(args[1]),alias_body)
    if match is None or match[1]not in[program,program.rsplit('.',1)[-1]]:raise ValueError('phase alias must use the original declared Program')
    return dict(parameter=parameter,alias=alias,events=events)
