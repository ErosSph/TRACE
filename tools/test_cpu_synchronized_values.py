import unittest
import cpu_synchronized_values as s


class CouplingTests(unittest.TestCase):
    def row(self,root,width,capture,recipe='(Select (EVar 1 8) Hold Capture)'):
        return dict(root=root,width=width,capture=capture,recipe=recipe,source=7,process='process_1')
    def test_same_phase_identity_word_is_required(self):
        a=self.row(1,32,'(EVar 32 7)');b=self.row(2,5,'(ESel 5 (EVar 32 7) (EConst 5 7))')
        self.assertEqual(s.pairs([a,b]),[(0,1)])
        b['process']='process_2';self.assertEqual(s.pairs([a,b]),[])
    def test_unknown_cannot_be_dropped_for_total_relation(self):
        a=self.row(1,32,'(EVar 32 7)','(Select (EVar 1 8) Unknown Capture)')
        b=dict(a,root=2,width=5,capture='(ESel 5 (EVar 32 7) (EConst 5 7))')
        self.assertEqual(s.pairs([a,b]),[])
        with self.assertRaises(ValueError):s.total(s.RecipeParser('Unknown').complete())
    def test_recipe_parser_does_not_extend_rtl_grammar(self):
        self.assertEqual(s.RecipeParser('Hold').complete().name,'Hold')
        with self.assertRaises(ValueError):s.rtl.Parser('Hold').complete()
    def test_different_guards_do_not_imply_synchronized_values(self):
        a=self.row(1,32,'(EVar 32 7)')
        b=self.row(2,5,'(ESel 5 (EVar 32 7) (EConst 5 7))','(Select (EVar 1 9) Hold Capture)')
        self.assertEqual(s.pairs([a,b]),[])


if __name__=='__main__':unittest.main()
