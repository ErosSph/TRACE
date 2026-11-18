import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
TOOL = ROOT / "tools" / "cpu_pipeline_skeleton.py"
MANIFESTS = ROOT / "framework" / "pipeline-skeletons"


def generate(manifest, out):
    subprocess.run([sys.executable, str(TOOL), str(manifest), "--out-dir", str(out)],
                   check=True, capture_output=True, text=True)


class PipelineSkeletonTest(unittest.TestCase):
    def check(self, name, goals, filled):
        manifest = MANIFESTS / f"{name}.json"
        module = json.loads(manifest.read_text())["module"]
        with tempfile.TemporaryDirectory() as tmp:
            generate(manifest, tmp)
            text = (pathlib.Path(tmp) / f"{module}.v").read_text()
            for goal in goals:
                self.assertIn(f"Definition goal_{goal}(", text)
            self.assertNotIn("Admitted", text)
            self.assertNotIn("Axiom", text)
            self.assertIn("Theorem assembled(", text)
            fill = pathlib.Path(tmp) / f"{module}Fill.v"
            self.assertEqual(fill.exists(), filled)
            if filled:
                ftext = fill.read_text()
                for goal in goals:
                    self.assertIn(f"Theorem goal_{goal}_holds(", ftext)
                self.assertIn("Theorem same_statement_as_reference(", ftext)
                self.assertNotIn("Admitted", ftext)

    def test_darkriscv_plan(self):
        self.check("darkriscv", ["shape", "transport", "admission", "observer", "front", "arch",
                                 "rank", "boot", "startup"], True)

    def test_bzeeno_ctx(self):
        self.check("bzeeno", ["obligation", "rank", "boot", "startup"], True)

    def test_cv32e40p_plan_m(self):
        self.check("cv32e40p", ["shape", "bounds", "transport", "admission", "observer", "front",
                                "arch", "rank", "boot", "startup"], False)

    def test_cv32e40p_rh(self):
        self.check("cv32e40p-m", ["obligation", "rank", "boot", "startup"], True)
        with tempfile.TemporaryDirectory() as tmp:
            generate(MANIFESTS / "cv32e40p-m.json", tmp)
            text = (pathlib.Path(tmp) / "CV32E40PSkeletonM.v").read_text()
            self.assertIn("Ex.External.CPUPipelineRetireHold", text)
            self.assertIn(":=StagedObligationRH(design", text)
            self.assertIn("claude-sonnet-5-5", text)

    def test_cv32e40p_m3_unconditional(self):
        self.check("cv32e40p-m3", ["obligation", "rank", "boot", "startup"], True)
        with tempfile.TemporaryDirectory() as tmp:
            generate(MANIFESTS / "cv32e40p-m3.json", tmp)
            text = (pathlib.Path(tmp) / "CV32E40PSkeletonM3.v").read_text()
            ftext = (pathlib.Path(tmp) / "CV32E40PSkeletonM3Fill.v").read_text()
            self.assertNotIn("HU", text)
            self.assertNotIn("HU", ftext)
            self.assertNotIn("CoverRemaining", ftext)
            self.assertIn("hyps3_all", ftext)
            self.assertIn("Proof. exact(actual_reset_infinite_rtl_isa_refinement image cert). Qed.", ftext)

    def test_other_modes_do_not_import_retire_hold(self):
        for name in ["darkriscv", "bzeeno", "cv32e40p"]:
            module = json.loads((MANIFESTS / f"{name}.json").read_text())["module"]
            with tempfile.TemporaryDirectory() as tmp:
                generate(MANIFESTS / f"{name}.json", tmp)
                self.assertNotIn("RetireHold", (pathlib.Path(tmp) / f"{module}.v").read_text())

    def test_unknown_mode_rejected(self):
        m = json.loads((MANIFESTS / "darkriscv.json").read_text())
        m["mode"] = "bogus"
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "m.json"
            path.write_text(json.dumps(m))
            r = subprocess.run([sys.executable, str(TOOL), str(path), "--out-dir", tmp],
                               capture_output=True, text=True)
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("unknown mode", r.stderr)

    def test_missing_fill_goal_rejected(self):
        m = json.loads((MANIFESTS / "darkriscv.json").read_text())
        del m["fill"]["goals"]["arch"]
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "m.json"
            path.write_text(json.dumps(m))
            r = subprocess.run([sys.executable, str(TOOL), str(path), "--out-dir", tmp],
                               capture_output=True, text=True)
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("lacks goals", r.stderr)


if __name__ == "__main__":
    unittest.main()
