import unittest
from cpu_expression_dag import ExpressionDAG,parse_term


class ExpressionDAGTests(unittest.TestCase):
    def test_scoped_global_aliases_and_sharing(self):
        d=ExpressionDAG.from_coq('''Module A.
Definition x:Expr:=(EVar 1 9).
Definition y:Expr:=(ECond 1 x x x).
End A.
Module B.
Definition x:Expr:=(EConst 1 0).
Definition z:Expr:=A.y.
End B.''',namespace='N',context=('actual_sample',7))
        root=d.resolve('B.z');self.assertEqual(d.stats(root)['inputs'],[(1,9)])
        self.assertEqual(d.stats(root)['context'],('actual_sample',7))
        self.assertEqual(d.nodes[d.fold(root,same_width=True)].name,'EVar')
        self.assertLess(len(d.to_coq(root).splitlines()),10)
        with self.assertRaisesRegex(ValueError,'ambiguous'):d.resolve('x')

    def test_substitution_preserves_width_and_unsigned_wrapper(self):
        d=ExpressionDAG();root=d.parse('(EConcat 3 (EVar 1 9) (EVar 2 9))')
        out=d.cofactor(root,{(1,9):3})
        self.assertEqual(d.stats(out)['inputs'],[(2,9)])
        self.assertIn('EConst 1 1',d.to_coq(out))

    def test_signed_extension_and_conditional_result_width(self):
        d=ExpressionDAG()
        self.assertEqual(d.eval_closed(d.parse('(EExtend 8 true (EConst 4 15))')),255)
        self.assertEqual(d.eval_closed(d.parse('(EExtend 8 false (EConst 4 15))')),15)
        self.assertEqual(d.eval_closed(d.parse('(ECond 1 (EConst 1 1) (EConst 8 255) (EConst 8 0))')),1)
        e=d.parse('(EExtend 8 true (EVar 4 7))')
        self.assertEqual(d.nodes[d.fold(e,same_width=True)].name,'EExtend')

    def test_cycle_unknown_substitution_and_parse_fail_closed(self):
        d=ExpressionDAG.from_coq('Definition a:Expr:=b.\nDefinition b:Expr:=a.')
        with self.assertRaisesRegex(ValueError,'cyclic'):d.resolve('a')
        with self.assertRaisesRegex(ValueError,'unsupported substitution'):
            ExpressionDAG().parse('(substitute mystery (EVar 1 3))')
        with self.assertRaises(ValueError):parse_term('(EVar 1 2) trailing')

    def test_hash_cons_and_same_width_exposes_equal_arms(self):
        d=ExpressionDAG();e=d.parse('(ECond 1 (EVar 1 8) (EExtend 1 false (EConst 1 1)) (EConst 1 1))')
        folded=d.fold(e,same_width=True)
        self.assertEqual(d.eval_closed(folded),1)
        self.assertEqual(d.stats(folded)['inputs'],[])

    def test_bitwise_not_and_strict_closed_mode(self):
        d=ExpressionDAG()
        self.assertEqual(d.eval_closed(d.parse('(EUnary 32 UNot (EConst 32 0))')),2**32-1)
        self.assertEqual(d.eval_closed(d.parse('(EUnary 32 UNot (EConst 32 1))')),2**32-2)
        e=d.parse('(ECond 1 (EConst 1 1) (EConst 1 1) (EVar 1 8))')
        self.assertIsNone(d.eval_closed(e))
        self.assertEqual(d.eval_closed(d.fold(e,mode='legacy')),1)
        shared=d.parse('(ECond 1 (EVar 1 8) (EVar 1 9) (EVar 1 9))')
        self.assertEqual(d.nodes[d.fold(shared,mode='legacy')].name,'EExtend')
        self.assertEqual(d.nodes[d.fold(shared,mode='enhanced')].name,'EVar')
        with self.assertRaisesRegex(ValueError,'conflicting fold mode'):
            d.fold(shared,mode='legacy',same_width=True)

    def test_closed_operator_signedness_and_shifts(self):
        d=ExpressionDAG()
        for term,value in [
            ('(EBinary 1 BGtS (EConst 4 15) (EConst 4 0))',0),
            ('(EBinary 1 BGtU (EConst 4 15) (EConst 4 0))',1),
            ('(EBinary 32 BShiftL (EConst 32 1) (EConst 32 4294967295))',0),
            ('(EReplicate 8 3 (EConst 3 5))',109),
            ('(ESel 4 (EConst 8 240) (EConst 3 4))',15)]:
            self.assertEqual(d.eval_closed(d.parse(term)),value)

    def test_qualified_definition_mapping_and_negative_coq_literal(self):
        d=ExpressionDAG.from_definitions({'A.x':'(EConst 8 (-1))','B.y':'A.x'})
        self.assertEqual(d.eval_closed(d.resolve('B.y')),255)
        self.assertIn('EConst 8 (-1)',d.to_coq(d.resolve('B.y')))
        with self.assertRaisesRegex(ValueError,'root is not an Expr'):d.parse('unresolved')

    def test_nested_comments_do_not_define_expressions(self):
        d=ExpressionDAG.from_coq('''(* outer (* inner *)
Definition bogus:Expr:=(EConst 1 0).
*)
Definition actual:Expr:=(EConst 1 1).''')
        self.assertEqual(set(d.definitions),{'actual'})
        with self.assertRaisesRegex(ValueError,'unterminated comment'):
            ExpressionDAG.from_coq('(*')


if __name__=='__main__':unittest.main()
