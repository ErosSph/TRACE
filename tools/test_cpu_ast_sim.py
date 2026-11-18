#!/usr/bin/env python3
"""Unit tests for tools/cpu_ast_sim.py (ExtendedSV simulator, ISA reference, domain checkers)."""
import os
import random
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_ast_sim as S  # noqa: E402

BZ_AST = S.DEFAULT_AST['bzeeno']
DK_AST = S.DEFAULT_AST['darkriscv']
CV_AST = S.DEFAULT_AST['cv32e40p']


def proc(kind, body, events='', line=1):
    return (f'{{| process_kind := {kind}; process_events := [{events}]; '
            f'process_body := {body}; process_source_line := {line} |}}')


def make_ast(procs, nsig, lfp=9, fuel=512):
    lines = [f'Definition process_{i} : Process := {p}.' for i, p in enumerate(procs)]
    names = '; '.join(f'process_{i}' for i in range(len(procs)))
    lines.append(f'Definition t_processes : list Process := [{names}].')
    lines.append(f'Definition t_program : Program :=\n  {{| signal_count := {nsig};\n     processes := t_processes;\n'
                 f'     statement_fuel := {fuel}; lfp_fuel := {lfp} |}}.')
    return S.Sim(S.parse_ast_text('\n'.join(lines)))


POS = lambda sig: f'{{| event_edge := Posedge; event_signal := {sig} |}}'
NEG = lambda sig: f'{{| event_edge := Negedge; event_signal := {sig} |}}'


class ExprSemantics(unittest.TestCase):
    def ev(self, expr, state=None, nsig=4):
        sim = make_ast([proc('Combinational', f'SAssign false {expr} (LVar 64 3)')], nsig)
        st = list(state or [0] * nsig)
        sim.comb_round(st)
        return st[3]

    def test_norm_and_arith(self):
        self.assertEqual(self.ev('(EBinary 8 BAdd (EConst 8 250) (EConst 8 10))'), 4)
        self.assertEqual(self.ev('(EBinary 8 BSub (EConst 8 1) (EConst 8 2))'), 255)
        self.assertEqual(self.ev('(EBinary 8 BMul (EConst 8 20) (EConst 8 20))'), 144)
        self.assertEqual(self.ev('(EUnary 8 UNot (EConst 8 1))'), 254)
        self.assertEqual(self.ev('(EUnary 8 UNegate (EConst 8 1))'), 255)
        self.assertEqual(self.ev('(EUnary 1 URedOr (EConst 8 4))'), 1)

    def test_var_is_normalised_on_read(self):
        self.assertEqual(self.ev('(EVar 4 0)', [0x1F5, 0, 0, 0]), 5)

    def test_compare_signed(self):
        # BGtS compares signed_value of the operand widths; BLtU/BGtU are unsigned
        self.assertEqual(self.ev('(EBinary 1 BGtS (EConst 8 1) (EConst 8 255))'), 1)
        self.assertEqual(self.ev('(EBinary 1 BGtU (EConst 8 1) (EConst 8 255))'), 0)
        self.assertEqual(self.ev('(EBinary 1 BLtU (EConst 8 1) (EConst 8 255))'), 1)

    def test_shifts(self):
        self.assertEqual(self.ev('(EBinary 8 BShiftL (EConst 8 129) (EConst 8 1))'), 2)
        self.assertEqual(self.ev('(EBinary 8 BShiftR (EConst 8 129) (EConst 8 1))'), 64)
        self.assertEqual(self.ev('(EBinary 8 BShiftRS (EConst 8 129) (EConst 8 1))'), 192)
        self.assertEqual(self.ev('(EBinary 8 BShiftL (EConst 8 1) (EVar 8 0))', [100, 0, 0, 0]), 0)
        self.assertEqual(self.ev('(EBinary 8 BShiftL (EConst 8 1) (EVar 40 0))', [1 << 35, 0, 0, 0]), 0)

    def test_sel_concat_replicate_extend(self):
        self.assertEqual(self.ev('(ESel 4 (EConst 8 171) (EConst 3 4))'), 0xA)
        self.assertEqual(self.ev('(EConcat 12 (EConst 4 10) (EConst 8 171))'), 0xAAB)
        self.assertEqual(self.ev('(EReplicate 12 3 (EConst 4 5))'), 0x555)
        self.assertEqual(self.ev('(EExtend 16 true (EConst 8 128))'), 0xFF80)
        self.assertEqual(self.ev('(EExtend 16 false (EConst 8 128))'), 0x80)
        self.assertEqual(self.ev('(EExtend 4 true (EConst 8 0x1F))'.replace('0x1F', '31')), 15)

    def test_cond(self):
        self.assertEqual(self.ev('(ECond 8 (EConst 1 1) (EConst 8 7) (EConst 8 9))'), 7)
        self.assertEqual(self.ev('(ECond 8 (EConst 1 0) (EConst 8 7) (EConst 8 9))'), 9)


class StatementSemantics(unittest.TestCase):
    def test_nonblocking_swap_uses_the_same_pre_state(self):
        sim = make_ast([proc('Sequential', 'SSeq [SAssign true (EVar 8 1) (LVar 8 0); SAssign true (EVar 8 0) (LVar 8 1)]',
                             POS(2))], 3)
        st = sim.phase([5, 9, 0], 2, 1)
        self.assertEqual(st[:2], [9, 5])

    def test_blocking_in_sequential_is_visible_locally_and_still_emitted(self):
        # a = 1 (blocking); b <= a (reads the updated local value)
        sim = make_ast([proc('Sequential', 'SSeq [SAssign false (EConst 8 1) (LVar 8 0); SAssign true (EVar 8 0) (LVar 8 1)]',
                             POS(2))], 3)
        st = sim.phase([0, 0, 0], 2, 1)
        self.assertEqual(st[:2], [1, 1])

    def test_sequential_processes_read_pre_state_of_each_other(self):
        p0 = proc('Sequential', 'SAssign false (EConst 8 1) (LVar 8 0)', POS(2))
        p1 = proc('Sequential', 'SAssign true (EVar 8 0) (LVar 8 1)', POS(2))
        sim = make_ast([p0, p1], 3)
        st = sim.phase([0, 0, 0], 2, 1)
        self.assertEqual(st[:2], [1, 0])  # p1 saw a == 0 (process_updates uses the same driven state)

    def test_comb_blocking_chain_in_order_and_early_exit(self):
        # reverse-ordered chain needs several rounds: x2 = x1+1 listed before x1 = x0+1
        p0 = proc('Combinational', 'SAssign false (EBinary 8 BAdd (EVar 8 1) (EConst 8 1)) (LVar 8 2)')
        p1 = proc('Combinational', 'SAssign false (EBinary 8 BAdd (EVar 8 0) (EConst 8 1)) (LVar 8 1)')
        sim = make_ast([p0, p1], 3, lfp=9)
        st = sim.lfp([10, 0, 0])
        self.assertEqual(st, [10, 11, 12])
        sim1 = make_ast([p0, p1], 3, lfp=1)
        self.assertEqual(sim1.lfp([10, 0, 0]), [10, 11, 1])  # one round only: x2 saw the old x1 = 0

    def test_case_default_overrides_and_first_match_wins(self):
        body = ('SCase (EVar 2 0) [(None, SAssign false (EConst 8 1) (LVar 8 1)); '
                '(Some (EConst 2 1), SAssign false (EConst 8 2) (LVar 8 1)); '
                '(None, SAssign false (EConst 8 3) (LVar 8 1))]')
        sim = make_ast([proc('Combinational', body)], 2)
        self.assertEqual(sim.comb_round([1, 0])[1], 2)
        self.assertEqual(sim.comb_round([0, 0])[1], 3)  # the later default replaces the earlier one

    def test_slice_assignment_and_unnormalised_storage(self):
        # LSel 4 (LVar 16 0) at offset 4 := 0xAB (only 4 bits land); offset is evaluated on the pre-state
        body = 'SAssign false (EConst 8 171) (LSel 4 (LVar 16 0) (EConst 4 4))'
        sim = make_ast([proc('Combinational', body)], 1)
        self.assertEqual(sim.comb_round([0xFFFF])[0], 0xFFBF)

    def test_edges(self):
        body = 'SAssign false (EBinary 8 BAdd (EVar 8 1) (EConst 8 1)) (LVar 8 1)'
        sim = make_ast([proc('Sequential', body, POS(0)), proc('Sequential', 'SAssign false (EBinary 8 BAdd (EVar 8 2) (EConst 8 1)) (LVar 8 2)', NEG(0))], 3)
        st = sim.phase([0, 0, 0], 0, 1)
        self.assertEqual(st, [1, 1, 0])
        st = sim.phase(st, 0, 0)
        self.assertEqual(st, [0, 1, 1])
        st = sim.phase(st, 0, 0)  # no edge
        self.assertEqual(st, [0, 1, 1])

    def test_initial_processes_run_in_initialize(self):
        sim = make_ast([proc('Initial', 'SAssign false (EConst 8 7) (LVar 8 0)')], 1)
        self.assertEqual(sim.initialize([0]), [7])

    def test_statement_fuel_cuts_deep_nesting(self):
        body = 'SAssign false (EConst 8 7) (LVar 8 0)'
        for _ in range(3):
            body = f'SSeq [{body}]'
        self.assertEqual(make_ast([proc('Combinational', body)], 1, fuel=512).comb_round([0]), [7])
        self.assertEqual(make_ast([proc('Combinational', body)], 1, fuel=3).comb_round([0]), [0])
        self.assertEqual(make_ast([proc('Combinational', body)], 1, fuel=4).comb_round([0]), [7])


class IsaAndDecode(unittest.TestCase):
    def test_decode_known_words(self):
        self.assertEqual(S.decode(0x00100093), ('addi', 1, 0, 0, 1))
        self.assertEqual(S.decode(0x00000067), ('jalr', 0, 0, 0, 0))
        self.assertEqual(S.decode(0x0000006f), ('jal', 0, 0, 0, 0))
        self.assertEqual(S.decode(0x00c000e7), ('jalr', 1, 0, 0, 12))
        self.assertEqual(S.decode(0x4000_0033)[0:1], ('sub',))
        self.assertIsNone(S.decode(0x02000033))     # MUL is not RV32I
        self.assertIsNone(S.decode(0x00001093 | (1 << 25)))  # slli with shamt[5]=1 is invalid in RV32
        self.assertEqual(S.decode(4111)[0], 'fence.i')

    def test_isa_reference_small_program(self):
        words = [0x00200113, 0x00c000e7, 0x00300193, 0x00400213, 0x0000006f]
        pcs, rfs, _ = S.isa_trace(words, 6)
        # addi x2,x0,2 ; jalr x1,x0,12 (link 8) ; addi x4,x0,4 ; jal x0,0 (self loop)
        self.assertEqual(pcs[:5], [0, 4, 12, 16, 16])
        self.assertEqual((rfs[1][1], rfs[1][2]), (8, 2))
        self.assertEqual(rfs[3][4], 4)
        self.assertEqual(rfs[3][3], 0)

    def test_isa_memory_ops(self):
        regs = [0] * 32
        mem = bytearray(4)
        regs[5] = 0x8081_F2F3
        S.isa_step(regs, 0, ('sw', 0, 0, 5, 0), mem)
        for name, exp in (('lb', 0xFFFFFFF3), ('lbu', 0xF3), ('lh', 0xFFFFF2F3), ('lhu', 0xF2F3), ('lw', 0x8081F2F3)):
            S.isa_step(regs, 0, (name, 6, 0, 0, 0), mem)
            self.assertEqual(regs[6], exp, name)
        S.isa_step(regs, 0, ('sb', 0, 0, 0, 0), mem)  # store x0 byte
        self.assertEqual(int.from_bytes(mem, 'little'), 0x8081F200)

    def test_branch_and_shift_semantics(self):
        regs = [0] * 32
        regs[1] = 0x8000_0000
        regs[2] = 31
        S.isa_step(regs, 0, ('sra', 3, 1, 2, 0))
        self.assertEqual(regs[3], 0xFFFFFFFF)
        self.assertEqual(S.isa_step(regs, 8, ('blt', 0, 1, 0, -8)), 0)      # signed: -2^31 < 0
        self.assertEqual(S.isa_step(regs, 8, ('bltu', 0, 1, 0, -8)), 12)    # unsigned: 2^31 !< 0


class DomainCheckers(unittest.TestCase):
    def test_bzeeno_examples_from_coq(self):
        for w in S.BZ_EXAMPLES_ACCEPTED:
            self.assertTrue(S.jump_family_check(w), w)
        for w in S.BZ_EXAMPLES_REJECTED:
            self.assertFalse(S.jump_family_check(w), w)

    def test_bzeeno_rejects_loads_stores_mul_and_fallthrough(self):
        self.assertFalse(S.jump_family_check([0x00002003, 0x0000006f]))        # lw
        self.assertFalse(S.jump_family_check([0x00100093]))                     # falls off the image
        self.assertFalse(S.jump_family_check([0x00100093, 0x02000033, 0x0000006f]))
        self.assertFalse(S.jump_family_check([]))
        self.assertFalse(S.jump_family_check([0x00100093] * 101 + [0x0000006f]))  # 102 words

    def test_dark_image38_closed_and_variants(self):
        self.assertTrue(S.dark_closed_cfg(S.DARK_IMAGE38))
        self.assertEqual(len(S.DARK_IMAGE38), 38)
        words = list(S.DARK_IMAGE38)
        words[28] = (4 << 12) | 128 | 3 | (1 << 15)      # load with rs1 != 0
        self.assertFalse(S.dark_closed_cfg(words))
        self.assertFalse(S.dark_closed_cfg(S.DARK_IMAGE38[:-1]))                  # last is FENCE.I falls through
        self.assertFalse(S.dark_closed_cfg([0x00100093, 0x00000067 | (1 << 20)]))  # jalr imm != 0
        self.assertFalse(S.dark_closed_cfg([0x0000000f, 0x0000006f]))             # plain FENCE is unsupported

    def test_generators_only_emit_accepted_programs(self):
        rng = random.Random(3)
        for _ in range(60):
            self.assertTrue(S.jump_family_check(S.gen_program(rng)))
            self.assertTrue(S.dark_closed_cfg(S.gen_dark_program(rng)))


@unittest.skipUnless(BZ_AST.exists(), 'Bzeeno AST not present')
class BzeenoOriginal(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sim = S.load_sim(BZ_AST)

    def test_parses_everything(self):
        self.assertEqual(len(self.sim.ast['processes']), 270)
        self.assertEqual(self.sim.n, 331)
        self.assertEqual(self.sim.fuel, 9)

    def test_matches_isa_on_example_programs(self):
        for w in S.BZ_EXAMPLES_ACCEPTED:
            self.assertIsNone(S.validate_against_isa(S.DESIGNS['bzeeno'], self.sim, w, 80))

    def test_matches_isa_on_random_programs(self):
        rng = random.Random(11)
        for _ in range(6):
            w = S.gen_program(rng)
            self.assertIsNone(S.validate_against_isa(S.DESIGNS['bzeeno'], self.sim, w, 150), w)

    def test_boot_history_of_jalr_loop(self):
        tr = S.trace(S.DESIGNS['bzeeno'], self.sim, [0x00100093, 0x00000067], 12)
        self.assertEqual([t[0] for t in tr], [None, None, None, 0, 4, None, 0, 4, None, 0, 4, None])
        self.assertEqual(tr[3][1][1], 1)

    def test_a_broken_design_is_detected(self):
        text = Path(BZ_AST).read_text()
        # every adder becomes a subtractor (the ALU and PC increment are among them)
        broken = S.Sim(S.parse_ast_text(text.replace('BAdd', 'BSub')))
        rng = random.Random(5)
        hits = 0
        for _ in range(20):
            w = S.gen_program(rng)
            if S.validate_against_isa(S.DESIGNS['bzeeno'], broken, w, 150):
                hits += 1
        self.assertGreater(hits, 0)


@unittest.skipUnless(DK_AST.exists(), 'Dark AST not present')
class DarkOriginal(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sim = S.load_sim(DK_AST)

    def test_parses_everything(self):
        self.assertEqual(len(self.sim.ast['processes']), 65)
        self.assertEqual(self.sim.fuel, 1)

    def test_image38_matches_isa(self):
        self.assertIsNone(S.validate_against_isa(S.DESIGNS['darkriscv'], self.sim, S.DARK_IMAGE38, 400))

    def test_matches_isa_on_random_programs(self):
        rng = random.Random(13)
        for _ in range(6):
            w = S.gen_dark_program(rng)
            self.assertIsNone(S.validate_against_isa(S.DESIGNS['darkriscv'], self.sim, w, 200), w)


class CvDomainChecker(unittest.TestCase):
    def test_rejected_programs(self):
        for w in S.CV_REJECTED:
            self.assertFalse(S.cv_domain_check(w), [hex(x) for x in w])

    def test_accepted_programs(self):
        for w in S.CV_EXAMPLES + S.CV_ACCEPTED_EXTRA + [S.DARK_IMAGE38]:
            self.assertTrue(S.cv_domain_check(w), [hex(x) for x in w])

    def test_unreachable_unsupported_word_is_rejected(self):
        # Supported32Program constrains every word of the image, also the unreachable ones
        self.assertFalse(S.cv_domain_check([0x0000006f, 0x00000073]))
        self.assertTrue(S.cv_domain_check([0x0000006f, 0x00000013]))

    def test_status_values(self):
        self.assertEqual(S.cv_domain_status([0x0000006f]), 'closed')              # jal x0,0
        self.assertEqual(S.cv_domain_status([0x00100093]), 'bounded')             # falls into NOPs (2^30 steps to wrap)
        self.assertEqual(S.cv_domain_status([0x00100093, 0x00102223]), 'violation')

    def test_pc_wrap_reenters_the_image(self):
        # witness found while validating: a jalr to 0xFFFFFFF4 runs 3 NOPs, wraps to pc 0 and re-executes
        # the image with other register values; the second pass jumps to a misaligned pc (out of domain)
        w = [0x100f, 0x3e21b3, 0xa18033, 0x3e0e33, 0x40a55d33, 0xae7033, 0x101013, 0x100f, 0x12003, 0x2050063,
             0x2510267, 0x800e3513, 0xa071b3, 0x1c013, 0x71f013, 0x1de0567, 0x40a55e33, 0x100f, 0xae1a63, 0xe7463,
             0x18463, 0x800e3193, 0x1c1c5b3, 0x100f, 0xae4263, 0xff5e01e7]
        self.assertEqual(S.cv_domain_status(w), 'violation')

    def test_generator_output_is_in_domain_for_the_whole_run(self):
        rng = random.Random(3)
        for _ in range(40):
            w = S.gen_cv_program(rng)
            self.assertEqual(S.cv_domain_status(w), 'closed')
            for x in w:
                self.assertEqual(x & 3, 3)

    def test_isa_reference_fetches_nop_beyond_the_image(self):
        pcs, _, _ = S.isa_trace([0x00100093], 4)
        self.assertEqual(pcs, [0, 4, 8, 12])


class CvEnvironment(unittest.TestCase):
    def test_instruction_image(self):
        w = [0x111, 0x222]
        self.assertEqual(S.cv_instruction_from_image(w, 4), 0x222)
        self.assertEqual(S.cv_instruction_from_image(w, 8), 19)
        self.assertEqual(S.cv_instruction_from_image(w, 2), 19)
        self.assertEqual(S.cv_instruction_from_image(w, -4), 19)

    def test_memory_word(self):
        self.assertEqual(S.cv_memory_read_word(0x11223344, 0), 0x11223344)
        self.assertEqual(S.cv_memory_read_word(0x11223344, 3), 0x11223344)   # land (lnot 3)
        self.assertEqual(S.cv_memory_read_word(0x11223344, 4), 0)
        self.assertEqual(S.cv_memory_store_word(0, (0, True, 0b0011, 0xAABBCCDD)), 0xCCDD)
        self.assertEqual(S.cv_memory_store_word(0x11223344, (0, True, 0b1000, 0xAABBCCDD)), 0xAA223344)
        self.assertEqual(S.cv_memory_store_word(5, (4, True, 0xF, 1)), 5)       # other word
        self.assertEqual(S.cv_memory_store_word(5, (0, False, 0xF, 1)), 5)      # read request

    def test_commit_list(self):
        self.assertEqual(S.commit_list(None), [])
        self.assertEqual(S.commit_list(8), [8])
        self.assertEqual(S.commit_list((4, 8)), [4, 8])


@unittest.skipUnless(CV_AST.exists(), 'CV32E40P AST not present')
class CvOriginal(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sim = S.load_sim(CV_AST)
        cls.design = S.DESIGNS['cv32e40p']

    def test_parses_everything(self):
        self.assertEqual(len(self.sim.ast['processes']), 2001)
        self.assertEqual(self.sim.n, 1800)
        self.assertEqual(self.sim.fuel, 8)

    def test_boot_state_after_reset_release(self):
        r = S.CvRun(self.sim, [19])
        self.assertEqual(len(r.rtl), 1800)
        self.assertEqual(r.rtl[S.CV_RST], 1)
        self.assertEqual(r.rtl[S.CV_RF], 0)

    def test_startup_and_commit_pcs(self):
        step = self.design.run(self.sim, S.CV_EXAMPLES[0])
        tr = [step() for _ in range(14)]
        self.assertEqual([t[0] for t in tr[:5]], [None] * 5)
        self.assertEqual([t[0] for t in tr[5:9]], [(0,), (4,), (8,), (12,)])
        self.assertEqual([(t[1] >> 32) & S.M32 for t in tr[5:8]], [1, 1, 1])      # x1 after the first commit
        self.assertEqual((tr[7][1] >> 64) & S.M32, 2)

    def test_matches_isa_on_examples(self):
        for w in S.CV_EXAMPLES + S.CV_ACCEPTED_EXTRA:
            self.assertIsNone(S.validate_against_isa(self.design, self.sim, w, 100), w)

    def test_matches_isa_on_all_38_classes(self):
        self.assertIsNone(S.validate_against_isa(self.design, self.sim, S.DARK_IMAGE38, 300))

    def test_matches_isa_on_random_programs(self):
        rng = random.Random(17)
        for _ in range(8):
            w = S.gen_cv_program(rng)
            self.assertIsNone(S.validate_against_isa(self.design, self.sim, w, 200), w)

    def test_two_commits_in_one_cycle_happen(self):
        # a LOAD whose write-back overlaps a younger scalar retirement gives a (older, younger) pair
        rng = random.Random(23)
        seen = False
        for _ in range(40):
            w = S.gen_cv_program(rng)
            if any(isinstance(t[0], tuple) and len(t[0]) == 2 for t in S.trace(self.design, self.sim, w, 150)):
                seen = True
                break
        self.assertTrue(seen)

    def test_a_broken_design_is_detected(self):
        broken = S.Sim(S.parse_ast_text(Path(CV_AST).read_text().replace('BAdd', 'BSub')))
        rng = random.Random(5)
        hits = sum(1 for _ in range(6) if S.validate_against_isa(self.design, broken, S.gen_cv_program(rng), 120))
        self.assertGreater(hits, 0)

    def test_phase_ex_agrees_with_phase(self):
        pre = list(S.CvRun(self.sim, [19]).rtl)
        post, driven = self.sim.phase_ex(pre, S.CV_CLK, 1)
        self.assertEqual(post, self.sim.phase(pre, S.CV_CLK, 1))
        self.assertEqual(driven[S.CV_CLK], 1)


@unittest.skipUnless(os.environ.get('CPU_AST_SIM_COQ') == '1', 'set CPU_AST_SIM_COQ=1 to run the Coq vm_compute cross-check')
class CoqCrossCheck(unittest.TestCase):
    def test_bzeeno_phase_states_equal_coq(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(S.main(['coq', '--design', 'bzeeno', '--programs', '1', '--cycles', '6', '--work', d]), 0)

    def test_dark_phase_states_equal_coq(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(S.main(['coq', '--design', 'darkriscv', '--programs', '1', '--cycles', '10', '--work', d]), 0)

    def test_cv32e40p_full38_observation_equals_coq(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(S.main(['coq', '--design', 'cv32e40p', '--programs', '1', '--cycles', '8', '--work', d]), 0)


if __name__ == '__main__':
    unittest.main()
