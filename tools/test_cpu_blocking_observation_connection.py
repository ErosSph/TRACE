import hashlib,json,unittest
from unittest.mock import patch
from pathlib import Path
import cpu_blocking_observation_connection as c

class ConnectionTests(unittest.TestCase):
    def verify(self,changes=None,exists=True):
        report=dict(accepted=True,coqc_exit=0,coqchk_exit=0,old_inv_read=False,
          source_sha256=hashlib.sha256(b'checked').hexdigest())
        report.update(changes or {})
        with patch.object(Path,'read_text',return_value=json.dumps(report)),patch.object(Path,'read_bytes',return_value=b'checked'),patch.object(Path,'is_file',return_value=exists):
            return c.verified_input('/unused')
    def test_accept_verified_input(self):self.assertTrue(self.verify()['accepted'])
    def test_reject_unfinished(self):
        with self.assertRaises(ValueError):self.verify({'accepted':False})
    def test_reject_missing_inner_check(self):
        with self.assertRaises(ValueError):self.verify({'coqchk_exit':None})
    def test_reject_changed_source(self):
        with self.assertRaises(ValueError):self.verify({'source_sha256':'other'})
    def test_reject_missing_object(self):
        with self.assertRaises(ValueError):self.verify(exists=False)
    def test_reject_old_inv_input(self):
        with self.assertRaises(ValueError):self.verify({'old_inv_read':True})

if __name__=='__main__':unittest.main()
