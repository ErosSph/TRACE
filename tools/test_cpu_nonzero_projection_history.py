import unittest
import cpu_nonzero_projection_history as h


class SourceHistoryMatchingTests(unittest.TestCase):
    def test_parent_mapping_cannot_override_provider_namespaces(self):
        flags=h.connection_flags([],'.')
        self.assertLess(flags.index('GeneratedProjectionHistory'),flags.index('GeneratedNonzeroCapture'))
        self.assertLess(flags.index('GeneratedProjectionHistory'),flags.index('GeneratedConnectedProjections'))

    def test_only_actual_previous_source_root_matches(self):
        rows=[dict(source=337,root=594),dict(source=718,root=618)]
        self.assertEqual(h.matching(rows,[337]),[(0,rows[0])])
        self.assertEqual(h.matching(rows,[]),[])

    def test_source_match_does_not_make_architectural_validity_claim(self):
        row=dict(source=2,root=3,width=2)
        self.assertEqual(h.matching([row],[2]),[(0,row)])
        self.assertNotIn('valid',row)


if __name__=='__main__':unittest.main()
