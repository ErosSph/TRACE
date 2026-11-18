import unittest
from cpu_record_evidence import records,definitions,COQ_RULES

class RecordEvidenceTests(unittest.TestCase):
    def test_scoped_record_fields_and_semicolons_inside_terms(self):
        source='''Module X. Section S.
Record R (n:nat):Prop:={ number_ok:In n [1;2]; another:n=n }.
End S. End X.'''
        rows=list(records(source));self.assertEqual(rows[0]['symbol'],'X.R')
        self.assertEqual([r['symbol']for r in rows[0]['fields']],['X.number_ok','X.another'])
        self.assertEqual(rows[0]['fields'][0]['type'],'In n [1;2]')

    def test_data_and_proof_field_types_are_proposals_not_a_sort_oracle(self):
        rows=list(records('Module X. Record R:Type:={ data:nat; proof:data=data }. End X.'))
        self.assertEqual(len(rows[0]['fields']),2)
        self.assertIn('constr_eq sort Prop',COQ_RULES)
        self.assertIn('has_evar value',COQ_RULES)
        self.assertIn('already available',COQ_RULES)

    def test_default_fields_are_reported_as_unsupported(self):
        rows=list(records('Record R:Type:={ default:nat:=0 }.'))
        self.assertEqual(rows[0]['fields'],[]);self.assertIn('residual',rows[0])

    def test_module_aliases_do_not_add_false_scopes(self):
        source='Module X. Module Alias:=Other. Definition step x:=x. Record R:Prop:={ field:True }. End X.'
        self.assertEqual(list(records(source))[0]['symbol'],'X.R')
        self.assertEqual(list(definitions(source))[0]['symbol'],'X.step')

    def test_comments_and_strings_cannot_inject_fields(self):
        source='''(* Record Fake:Prop:={ wrong:False }. *) Module X.
Definition message:="Record Fake:Prop:={ wrong:False }.".
Record Real:Prop:={ right:True }. End X.'''
        self.assertEqual([r['symbol']for r in records(source)],['X.Real'])

    def test_unbalanced_scope_is_rejected(self):
        with self.assertRaises(ValueError):list(records('Module X. End Y.'))

if __name__=='__main__':unittest.main()
