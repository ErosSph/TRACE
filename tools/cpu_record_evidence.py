"""Propose typed record projections; Coq checks every actual application.

No architecture role, record layout, field identifier or CPU name is hardcoded.
Non-propositional fields and applications with unresolved evars are refused by
the generated Ltac. Source parsing is an untrusted proposal, not evidence.
"""
from __future__ import annotations
import re
from cpu_local_evidence_catalog import commands


def fields(body):
    parts=[];start=0;depth=0
    for i,c in enumerate(body):
        if c in '([{':depth+=1
        elif c in ')]}':depth-=1
        elif c==';'and depth==0:parts.append(body[start:i]);start=i+1
    parts.append(body[start:]);out=[]
    for part in parts:
        if not part.strip():continue
        match=re.fullmatch(r'\s*([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+)',part,re.S)
        if not match or ':='in match.group(2):raise ValueError('unsupported record field syntax')
        out.append(dict(name=match.group(1),type=match.group(2).strip()))
    return out


def scoped_commands(source):
    scopes=[]
    for command in commands(source):
        opened=re.fullmatch(r'(Module(?:\s+Type)?|Section)\s+([A-Za-z_][A-Za-z0-9_]*)',command)
        if opened:scopes.append((opened.group(2),opened.group(1).startswith('Module')));continue
        closed=re.fullmatch(r'End\s+([A-Za-z_][A-Za-z0-9_]*)',command)
        if closed:
            if not scopes or scopes[-1][0]!=closed.group(1):raise ValueError('unbalanced record source scope')
            scopes.pop();continue
        yield '.'.join(n for n,module in scopes if module),command


def definitions(source):
    for prefix,command in scoped_commands(source):
        match=re.match(r'Definition\s+([A-Za-z_][A-Za-z0-9_]*)\b',command)
        if match:
            yield dict(symbol=(prefix+'.'if prefix else '')+match.group(1),command=command)


def records(source):
    for prefix,command in scoped_commands(source):
        match=re.fullmatch(r'Record\s+([A-Za-z_][A-Za-z0-9_]*)\b(.*?)\s*:=\s*'
                          r'(?:[A-Za-z_][A-Za-z0-9_]*\s*)?\{(.*)\}',command,re.S)
        if not match:continue
        name,parameters,body=match.groups()
        symbol=(prefix+'.'if prefix else '')+name
        try:entries=fields(body)
        except ValueError as exc:
            yield dict(symbol=symbol,parameters=parameters,fields=[],residual=str(exc));continue
        for entry in entries:entry['symbol']=(prefix+'.'if prefix else '')+entry['name']
        yield dict(symbol=symbol,parameters=parameters,fields=entries)


COQ_RULES=r'''
Module GeneratedRecordRules.
Ltac fresh_fact value :=
 let proposition := type of value in
 let sort := type of proposition in
 constr_eq sort Prop;
 tryif has_evar value then fail 0 "open application" else idtac;
 tryif (match goal with _ : proposition |- _ => idtac end)
 then fail 0 "already available"
 else let result := fresh "record_fact" in pose proof value as result; idtac "RECORD_FACT_ADDED".
Ltac apply_to_fact rule argument :=
 let rec attempt function fuel :=
  first [let value := constr:(function argument) in fresh_fact value
        | lazymatch fuel with
          | O => fail 0 "application budget exhausted"
          | S ?remaining => let next := uconstr:(function _) in attempt next remaining
          end] in
 let budget := constr:(16%nat) in attempt rule budget.
Ltac conjunction_fact :=
 match goal with H : and _ _ |- _ =>
 first [let value := constr:(proj1 H) in fresh_fact value
       |let value := constr:(proj2 H) in fresh_fact value] end.
Ltac local_implication_fact :=
 match goal with function : ?F |- _ =>
 lazymatch F with forall _ : _, _ =>
 match goal with argument : ?A |- _ =>
 let argument_sort := type of A in constr_eq argument_sort Prop;
 apply_to_fact function argument end end
 end.
End GeneratedRecordRules.
'''
