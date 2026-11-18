import hashlib,json,tempfile,unittest
from pathlib import Path
import cpu_pending_case_consumer as c


class PendingCaseConsumerTests(unittest.TestCase):
    def fixture(self,folder):
        plan={'old_inv_read':False};source='newly generated source';obj=b'fixture object, not a native proof'
        folder.joinpath('plan.json').write_text(json.dumps(plan));folder.joinpath('CaseInputs.v').write_text(source)
        folder.joinpath('CaseInputs.vo').write_bytes(obj)
        report=dict(accepted=True,coqc_exit=0,coqchk_exit=0,assumptions_closed=True,old_inv_read=False,
            domain_reachability_proved=False,itree_refinement_proved=False,
            source_sha256=hashlib.sha256(source.encode()).hexdigest(),object_sha256=hashlib.sha256(obj).hexdigest())
        folder.joinpath('report.json').write_text(json.dumps(report))
        return plan,source,report

    def test_current_provider_gate(self):
        with tempfile.TemporaryDirectory()as tmp:
            folder=Path(tmp);plan,source,report=self.fixture(folder)
            self.assertEqual(c.verify_case_provider(folder,plan,source),report)

    def test_no_promotion_of_local_proof_to_complete_inv(self):
        with tempfile.TemporaryDirectory()as tmp:
            folder=Path(tmp);plan,source,report=self.fixture(folder)
            for key in ['global_inv_proved','domain_reachability_proved','itree_refinement_proved','old_inv_read']:
                wrong=dict(report);wrong[key]=True;folder.joinpath('report.json').write_text(json.dumps(wrong))
                with self.assertRaises(ValueError):c.verify_case_provider(folder,plan,source)

    def test_stale_source_or_object_is_rejected(self):
        with tempfile.TemporaryDirectory()as tmp:
            folder=Path(tmp);plan,source,report=self.fixture(folder)
            with self.assertRaises(ValueError):c.verify_case_provider(folder,plan,source+' changed')
            folder.joinpath('CaseInputs.vo').write_bytes(b'changed')
            with self.assertRaises(ValueError):c.verify_case_provider(folder,plan,source)


if __name__=='__main__':unittest.main()
