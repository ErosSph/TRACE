import unittest
import cpu_selector_metadata as m


class SelectorMetadataTests(unittest.TestCase):
    def wire(self,w=5,terminal=12):
        return dict(input=8,width=w,terminal=terminal,edges=[dict(root=8,parent=terminal)])

    def test_exact_root_and_width(self):
        yes,no=m.connect(dict(sources=[self.wire()]),dict(copy_edges=[dict(root=12,width=5)]))
        self.assertEqual((len(yes),len(no)),(1,0))

    def test_width_mismatch_remains_open(self):
        yes,no=m.connect(dict(sources=[self.wire(6)]),dict(copy_edges=[dict(root=12,width=5)]))
        self.assertEqual((len(yes),len(no)),(0,1))

    def test_ambiguous_relation_not_guessed(self):
        yes,no=m.connect(dict(sources=[self.wire()]),dict(copy_edges=[dict(root=12,width=5)]*2))
        self.assertEqual((len(yes),len(no)),(0,1))

    def test_proof_index_includes_unmatched_predecessor(self):
        a=self.wire();b=dict(self.wire(),input=9,terminal=13)
        yes,no=m.connect(dict(sources=[a,b]),dict(copy_edges=[dict(root=13,width=5)]))
        self.assertEqual(yes[0]['source_index'],1)
        self.assertEqual(yes[0]['copy_index'],0)
        self.assertEqual(len(no),1)

    def test_connected_capture_selects_its_own_rule(self):
        yes,no=m.connect(dict(sources=[self.wire()]),dict(copy_edges=[]),
            dict(projections=[dict(root=12,width=5)]))
        self.assertEqual(yes[0]['kind'],'connected')
        self.assertEqual(no,[])

    def test_two_rule_kinds_do_not_hide_ambiguity(self):
        yes,no=m.connect(dict(sources=[self.wire()]),dict(copy_edges=[dict(root=12,width=5)]),
            dict(projections=[dict(root=12,width=5)]))
        self.assertEqual(yes,[])
        self.assertEqual(len(no),1)


if __name__=='__main__':unittest.main()
