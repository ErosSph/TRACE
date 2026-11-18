"""Recognize a branch that produces exactly one write, not merely one leaf.

All other writes in the complete process must reduce to empty under the
same path decisions. Coq checks the resulting full bank-operation equality.
"""
import cpu_bank_index_certificate as indices
rtl=indices.rtl


def selected(plan, decisions):
    n,a=plan.name,plan.args
    if n=='BPEmpty':return []
    if n in ('BPWord','BPReset'):return [plan]
    if n=='BPSeq':
        return [leaf for child in a[0].args for leaf in selected(child,decisions)]
    if n=='BPIf':
        key=rtl.render(a[0])
        if key not in decisions:raise ValueError('unresolved sibling branch')
        return selected(a[1] if decisions[key] else a[2],decisions)
    raise ValueError('unsupported complete bank plan')


def discover(ast,index_root):
    matches=[]
    for bank in indices.ownership.bank.analyze(ast)['banks']:
        if len(bank['plans'])!=1:continue
        proc,_,plan=bank['plans'][0]
        for path,guards,leaf in indices.ownership.leaves(plan):
            if leaf.name!='BPWord':continue
            match=indices.recognize(rtl.render(leaf.args[0]))
            if not match or match['index']!=f'(EVar 5 {index_root})':continue
            decisions={};consistent=True
            for guard,taken in guards:
                key=rtl.render(guard)
                if key in decisions and decisions[key]!=taken:consistent=False
                decisions[key]=taken
            if not consistent:continue
            try:remaining=selected(plan,decisions)
            except ValueError:continue
            if remaining!=[leaf]:continue
            matches.append(dict(bank=bank['root'],total=bank['total'],process=proc['name'],
                index_root=index_root,path=list(path),guards=list(decisions.items()),
                offset=rtl.render(leaf.args[0]),data=rtl.render(leaf.args[1]),index=match))
    return matches


def render(ast,row,name='selected_bank_write'):
    root=row['bank'];entries=f'bank_{root}_entries';plan=f'bank_{root}_{row["process"]}_plan'
    proc=ast['module']+'.'+row['process'];value=f'(norm 32(eval_expr driven {row["data"]}))'
    conditions=[f'Z.eqb(eval_expr driven {guard})0={str(not taken).lower()}' for guard,taken in row['guards']]
    lines=['Require Import Lang.ExtendedSVBankIndex Lang.ExtendedSVBankPlan.',
           'Import ExtendedSVBankIndex ExtendedSVBankPlan.',
           f'Theorem {name} pre driven address:',
           f'process_matches_states pre driven {proc}=true ->',
           *[condition+' ->' for condition in conditions],
           f'norm 5(read_signal driven {row["index_root"]})=address ->',
           f'bank_phase_operations {row["total"]} pre driven {entries}=[WriteLane address {value}].',
           'Proof. intros HT '+' '.join(f'H{i}' for i in range(len(conditions)))+' HA.',
           f'unfold bank_phase_operations,{entries};cbn[flat_map bank_process bank_plan];rewrite HT.',
           f'cbn[{plan} eval_bank_plan flat_map app].']
    for i in range(len(conditions)):lines += [f'rewrite H{i};cbn[eval_bank_plan flat_map app].']
    lines += [f'change([WriteLane (Z.div(eval_expr driven {row["offset"]})32) {value}]=[WriteLane address {value}]).']
    rule=row['index']['rule']
    if rule=='shifted_index':lines+=['rewrite shifted_index.']
    else:
        offset=rtl.Parser(row['offset']).complete()
        scale=offset.args[3] if rule=='multiply_index' else offset.args[2]
        lines += [f'rewrite({rule} driven {offset.args[0].name}%nat {row["index"]["index"]} {rtl.render(scale)} ltac:(clear;lia) ltac:(reflexivity) eq_refl).']
    lines += [f'change([WriteLane (norm 5(read_signal driven {row["index_root"]})) {value}]=[WriteLane address {value}]).',
              'now rewrite HA. Qed.',f'Print Assumptions {name}.']
    return '\n'.join(lines)+'\n'
