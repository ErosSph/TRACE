import hashlib,json,tempfile,unittest
from pathlib import Path
import cpu_pending_covered_fields as c


class CoveredFieldProviderTests(unittest.TestCase):
    def fixture(self,folder):
        data={'known_validity':{'1':2}};source='generated fixture';obj=b'not a native proof, gate test only'
        folder.joinpath('plan.json').write_text(json.dumps(data));folder.joinpath('Rule.v').write_text(source)
        folder.joinpath('Rule.vo').write_bytes(obj)
        report=dict(accepted=True,coqc_exit=0,coqchk_exit=0,assumptions_closed=True,old_inv_read=False,
            old_pending_read=False,global_inv_proved=False,itree_refinement_proved=False,
            source_sha256=hashlib.sha256(source.encode()).hexdigest(),object_sha256=hashlib.sha256(obj).hexdigest())
        folder.joinpath('report.json').write_text(json.dumps(report));return data,source,report

    def test_exact_json_native_plan_is_accepted_by_gate_only(self):
        with tempfile.TemporaryDirectory()as tmp:
            folder=Path(tmp);data,source,report=self.fixture(folder)
            self.assertEqual(c.verify(folder,'Rule.v',data,source),report)

    def test_wider_claims_and_old_inv_reads_are_rejected(self):
        with tempfile.TemporaryDirectory()as tmp:
            folder=Path(tmp);data,source,report=self.fixture(folder)
            for key in['old_inv_read','old_pending_read','global_inv_proved','itree_refinement_proved','validity_completeness_proved','isa_effect_proved']:
                wrong=dict(report);wrong[key]=True;folder.joinpath('report.json').write_text(json.dumps(wrong))
                with self.assertRaises(ValueError):c.verify(folder,'Rule.v',data,source)

    def test_stale_object_cannot_satisfy_current_gate(self):
        with tempfile.TemporaryDirectory()as tmp:
            folder=Path(tmp);data,source,report=self.fixture(folder);folder.joinpath('Rule.vo').write_bytes(b'changed')
            with self.assertRaises(ValueError):c.verify(folder,'Rule.v',data,source)


if __name__=='__main__':unittest.main()
