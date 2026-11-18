"""RV32I instruction classes (design independent) and their ISA-level effects.

This table is the only source of expected controller outputs in the template
route. Values come from the RISC-V ISA (riscv-coq `Decode`/`CV32E40PDataOpExecution.result_word`),
never from an RTL result. Z-level formulas use the operand values a (rs1), b
(rs2 or the sign-extended immediate), pc and are bridged to `result_word`
by the Coq module CPUClassValueBridge (when present).

Fields: name, group (opcode group), opcode, funct3 (None: free), funct7 (None: not constrained by the controller),
writes_rd, kind (dataop|jal|jalr|branch), operand_b (rs2|imm|None), value (Z expression on a,b,pc,link) for the rd value,
cond (branch condition on a,b).
"""
OPS = {'OP': 51, 'OPIMM': 19, 'LUI': 55, 'AUIPC': 23, 'JAL': 111, 'JALR': 103, 'BRANCH': 99}


def _sg(x):
    return f'(signed_value 32 {x})'


ALU = {  # name: (funct3, funct7 for R-type, value)
    'Add': (0, 0, 'Z.add a b'), 'Sub': (0, 32, 'Z.sub a b'), 'Sll': (1, 0, 'Z.shiftl a (norm 5 b)'),
    'Slt': (2, 0, f'boolz (Z.ltb {_sg("a")} {_sg("b")})'), 'Sltu': (3, 0, 'boolz (Z.ltb a b)'),
    'Xor': (4, 0, 'Z.lxor a b'), 'Srl': (5, 0, 'Z.shiftr a (norm 5 b)'),
    'Sra': (5, 32, f'Z.shiftr {_sg("a")} (norm 5 b)'), 'Or': (6, 0, 'Z.lor a b'), 'And': (7, 0, 'Z.land a b')}
IMM = {'Addi': ('Add', None), 'Slti': ('Slt', None), 'Sltiu': ('Sltu', None), 'Xori': ('Xor', None),
       'Ori': ('Or', None), 'Andi': ('And', None), 'Slli': ('Sll', 0), 'Srli': ('Srl', 0), 'Srai': ('Sra', 32)}
BR = {'Beq': (0, 'Z.eqb a b'), 'Bne': (1, 'negb (Z.eqb a b)'), 'Blt': (4, f'Z.ltb {_sg("a")} {_sg("b")}'),
      'Bge': (5, f'negb (Z.ltb {_sg("a")} {_sg("b")})'), 'Bltu': (6, 'Z.ltb a b'), 'Bgeu': (7, 'negb (Z.ltb a b)')}


def classes():
    out = []
    for n, (f3, f7, v) in ALU.items():
        out.append(dict(name=n, group='OP', opcode=OPS['OP'], funct3=f3, funct7=f7, writes_rd=True, kind='dataop',
                        operand_b='rs2', value=v))
    for n, (base, f7) in IMM.items():
        f3, _, v = ALU[base]
        out.append(dict(name=n, group='OPIMM', opcode=OPS['OPIMM'], funct3=f3, funct7=f7, writes_rd=True,
                        kind='dataop', operand_b='imm', value=v))
    out.append(dict(name='Lui', group='LUI', opcode=OPS['LUI'], funct3=None, funct7=None, writes_rd=True,
                    kind='dataop', operand_b='imm', value='b'))
    out.append(dict(name='Auipc', group='AUIPC', opcode=OPS['AUIPC'], funct3=None, funct7=None, writes_rd=True,
                    kind='dataop', operand_b='imm', value='Z.add pc b'))
    out.append(dict(name='Jal', group='JAL', opcode=OPS['JAL'], funct3=None, funct7=None, writes_rd=True,
                    kind='jal', operand_b='imm', value='link'))
    out.append(dict(name='Jalr', group='JALR', opcode=OPS['JALR'], funct3=None, funct7=None, writes_rd=True,
                    kind='jalr', operand_b='imm', value='link'))
    for n, (f3, c) in BR.items():
        out.append(dict(name=n, group='BRANCH', opcode=OPS['BRANCH'], funct3=f3, funct7=None, writes_rd=False,
                        kind='branch', operand_b='rs2', value=None, cond=c))
    return out


if __name__ == '__main__':
    cs = classes()
    print(len(cs), [c['name'] for c in cs])
