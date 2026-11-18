import tempfile
import threading
import time
import unittest
from pathlib import Path
from cpu_certificate_acceptance import run_stage


class StageLoggingTests(unittest.TestCase):
    def test_success_preserves_distinct_audit_streams(self):
        with tempfile.TemporaryDirectory() as directory:
            log=Path(directory)/'stage.log'
            result,timed=run_stage(['/bin/sh','-c',
                "printf 'proof-output\\r\\n'; printf 'diagnostic\\n' >&2"],log,5)
            self.assertEqual(result.returncode,0);self.assertFalse(timed)
            self.assertEqual(result.stdout,'proof-output\n')
            self.assertEqual(result.stderr,'diagnostic\n')
            self.assertIn('proof-output',log.read_text())
            self.assertIn('diagnostic',log.read_text())

    def test_nonzero_exit_does_not_become_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            result,timed=run_stage(['/bin/sh','-c',"printf 'Error\\n' >&2; exit 3"],
                Path(directory)/'stage.log',5)
            self.assertEqual(result.returncode,3);self.assertFalse(timed)
            self.assertEqual(result.stderr,'Error\n')

    def test_timeout_keeps_partial_output_and_exit124(self):
        with tempfile.TemporaryDirectory() as directory:
            log=Path(directory)/'stage.log'
            result,timed=run_stage(['/bin/sh','-c',"printf 'before\\n'; exec sleep 3"],log,.2)
            self.assertTrue(timed);self.assertEqual(result.returncode,124)
            self.assertEqual(result.stdout,'before\n')
            self.assertEqual(log.read_text(),'before\n')

    def test_log_is_visible_while_same_process_is_running(self):
        with tempfile.TemporaryDirectory() as directory:
            log=Path(directory)/'stage.log';results=[]
            worker=threading.Thread(target=lambda:results.append(run_stage(
                ['/bin/sh','-c',"printf 'ready\\n'; sleep 1; printf 'done\\n'"],log,5)))
            worker.start()
            try:
                deadline=time.monotonic()+4
                while time.monotonic()<deadline:
                    if log.exists() and 'ready' in log.read_text():break
                    time.sleep(.01)
                self.assertIn('ready',log.read_text())
                self.assertTrue(worker.is_alive())
                self.assertNotIn('done',log.read_text())
            finally:worker.join()
            self.assertEqual(results[0][0].stdout,'ready\ndone\n')
            self.assertFalse(results[0][1])

    def test_lingering_child_pipes_do_not_escape_stage_deadline(self):
        with tempfile.TemporaryDirectory() as directory:
            start=time.monotonic()
            result,timed=run_stage(['/bin/sh','-c',"printf 'before\\n'; sleep 3 & exit 0"],
                Path(directory)/'stage.log',.2)
            self.assertTrue(timed);self.assertEqual(result.returncode,124)
            self.assertEqual(result.stdout,'before\n')
            self.assertLess(time.monotonic()-start,2)


if __name__=='__main__':unittest.main()
