import tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import cpu_field_selector_gap as c

class FieldGapTests(unittest.TestCase):
    def test_model_selection_never_counts_as_proof(self):
        with tempfile.TemporaryDirectory()as d,patch.object(c.selector.chain.p.origins,'raw_binding',return_value=({'source_sha256':'test'},None,None)),patch.object(c,'proposal',return_value=({'field_1':c.STRATEGIES},[])),patch.object(c.llm,'query',return_value=({'status':'accepted_unproved'},{'field_1':'derive_guarded_projection_reference'}))as query:
            r=c.run('raw','Raw',Path(d)/'out','test')
            self.assertFalse(r['accepted']);self.assertFalse(r['proof_generated']);self.assertFalse(r['complete_R_generated'])
            query.assert_called_once()
    def test_no_gap_skips_remote_call(self):
        with tempfile.TemporaryDirectory()as d,patch.object(c.selector.chain.p.origins,'raw_binding',return_value=({'source_sha256':'test'},None,None)),patch.object(c,'proposal',return_value=({},[])),patch.object(c.llm,'query')as query:
            r=c.run('raw','Raw',Path(d)/'out','test')
            self.assertEqual(r['llm']['attempts'],0);query.assert_not_called()

if __name__=='__main__':unittest.main()
