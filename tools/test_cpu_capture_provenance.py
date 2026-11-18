import unittest
from pathlib import Path
from unittest.mock import patch
import cpu_capture_provenance as p

class ProvenanceTests(unittest.TestCase):
    def test_edges_not_stage_number_determine_origin(self):
        chain=dict(rows=[{}, {}, {}],edges=[dict(target=2,source=0)])
        s=p.render('Raw.p',chain)
        self.assertIn('projection_2_origin;apply projection_recorded;[exact H2|exact H0]',s)
        self.assertIn('projection_1_origin;apply projection_recorded;[exact H1|exact HG]',s)

    def test_boot_has_no_history_correctness_assumption(self):
        s=p.render('Raw.p',dict(rows=[{}],edges=[]))
        goal=s.split('Theorem boot_recorded',1)[1].split('Proof.',1)[0]
        self.assertNotIn('->',goal)
        self.assertIn('H.boot_history image events',goal)

    def test_empty_chain_rejected(self):
        with self.assertRaises(ValueError):p.render('Raw.p',dict(rows=[],edges=[]))

    def test_no_cpu_theorem_lookup(self):
        with patch.object(Path,'read_text',side_effect=AssertionError('old proof')):
            s=p.render('Raw.p',dict(rows=[{}],edges=[]))
        self.assertNotIn('Admitted',s)
        self.assertNotIn('Axiom ',s)

if __name__=='__main__':unittest.main()
