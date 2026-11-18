import json
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
TOOL = ROOT / "tools" / "cpu_chain_replay.py"
sys.path.insert(0, str(ROOT / "tools"))
import cpu_chain_replay as replay  # noqa: E402

HAVE_COQ = (ROOT / "_opam/bin/coqc").exists() and (ROOT / "_opam/bin/coqdep").exists()


class PureTest(unittest.TestCase):
    def test_parse_coqdep(self):
        text = ("A/B.vo A/B.glob A/B.v.beautified A/B.required_vo: A/B.v A/C.vo ../dep/x/D.vo\n"
                "A/B.vio: A/B.v A/C.vio\n")
        got = replay.parse_coqdep(text, "/w")
        self.assertEqual(got, {pathlib.Path("/w/A/B.v"): [
            pathlib.Path("/w/A/C.v"), pathlib.Path("/w/../dep/x/D.v").resolve()]})

    def test_critical_path(self):
        deps = {"a": [], "b": ["a"], "c": ["a"], "d": ["b", "c"]}
        wall = {"a": 1.0, "b": 5.0, "c": 2.0, "d": 1.0}
        seconds, files = replay.critical_path(deps, wall)
        self.assertEqual(seconds, 7.0)
        self.assertEqual(files, ["a", "b", "d"])

    def test_phase_key_and_peak_rss(self):
        self.assertEqual(replay.phase_key("a/b.v", None), "a__b.v")
        self.assertEqual(replay.phase_key("a/b.v", "vok"), "a__b.v.vok")
        entries = [dict(started=0, ended=2, max_rss_kb=10), dict(started=1, ended=3, max_rss_kb=5),
                   dict(started=3, ended=4, max_rss_kb=7)]
        self.assertEqual(replay.peak_concurrent_rss_kb(entries), 15)

    def test_run_timed_unlimited_stack(self):
        with tempfile.TemporaryDirectory() as tmp:
            log = pathlib.Path(tmp) / "l"
            replay.run_timed(["sh", "-c", "ulimit -s"], log, unlimited_stack=True)
            import resource
            hard = resource.getrlimit(resource.RLIMIT_STACK)[1]
            want = "unlimited" if hard == resource.RLIM_INFINITY else str(hard // 1024)
            self.assertEqual(log.read_text().strip(), want)

    def test_parse_assumptions(self):
        text = ("Closed under the global context\n"
                "Axioms:\nFunctionalExtensionality.functional_extensionality_dep\n  : forall x,\n  y\n"
                "  continued\nAxioms:\nFunctionalExtensionality.functional_extensionality_dep : t\n")
        self.assertEqual(replay.parse_assumptions(text),
                         [[], ["FunctionalExtensionality.functional_extensionality_dep"],
                          ["FunctionalExtensionality.functional_extensionality_dep"]])

    def test_remap_directory(self):
        got = replay.remap_directory("/other/place/" + replay.ROOT.name + "/src")
        self.assertEqual(got, (ROOT / "src").resolve())

    def test_existing_out_dir_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            proc = subprocess.run([sys.executable, str(TOOL), "--target", "x.v", "--out-dir", tmp],
                                  capture_output=True, text=True)
            self.assertNotEqual(proc.returncode, 0)
            self.assertIn("already exists", proc.stderr)


@unittest.skipUnless(HAVE_COQ, "coq binaries missing")
class FakeClosureTest(unittest.TestCase):
    def setUp(self):
        self.tmp = pathlib.Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp, True)
        lib = self.tmp / "lib"
        lib.mkdir()
        (lib / "A.v").write_text("Definition a := 1.\n")
        (lib / "B.v").write_text("Require Import Fake.A.\nDefinition b := a + 1.\n")
        (lib / "C.v").write_text("Definition c := 3.\n")
        (lib / "Unused.v").write_text("Definition u := 0.\n")
        (lib / "Top.v").write_text("Require Import Fake.B.\nRequire Import Fake.C.\nTheorem t : b = 2. Proof. reflexivity. Qed.\n"
                                   "Print Assumptions t.\n")
        self.providers = self.tmp / "providers.json"
        self.providers.write_text(json.dumps([{"directory": str(lib), "namespace": "Fake"}]))
        self.lib = lib

    def run_tool(self, name, *extra):
        out = self.tmp / name
        proc = subprocess.run([sys.executable, str(TOOL), "--target", "Fake.Top", "--no-base-loadpaths",
                               "--providers", str(self.providers), "--out-dir", str(out), "-j", "4",
                               *extra], capture_output=True, text=True)
        return proc, out

    def test_clean_run(self):
        proc, out = self.run_tool("ok", "--assumptions", "Fake.Top.t")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        report = json.loads((out / "report.json").read_text())
        self.assertEqual(report["closure_files"], 4)
        self.assertTrue(report["build_ok"])
        self.assertEqual(report["coqchk"]["exit"], 0)
        self.assertTrue(report["assumptions"]["only_allowed"])
        self.assertIsNone(report["first_failure"])
        self.assertIsNone(report["ast_substitution_hash"])
        self.assertFalse(list(out.rglob("*.vo")))
        self.assertGreater(report["critical_path_s"], 0)

    def test_require_lib_edge_and_flag(self):
        (self.lib / "Q.v").write_text("Definition q := 4.\n")
        (self.lib / "UsesQ.v").write_text("Definition uq := Fake.Q.q.\n")
        (self.lib / "Top.v").write_text("Require Import Fake.UsesQ.\nTheorem t : uq = 4. Proof. reflexivity. Qed.\n")
        proc, out = self.run_tool("noreqlib")
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        proc, out = self.run_tool("reqlib", "--require-lib", "Fake.UsesQ=Fake.Q", "--assumptions", "Fake.Top.t")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        report = json.loads((out / "report.json").read_text())
        self.assertEqual(report["closure_files"], 3)
        self.assertTrue(report["build_ok"])

    def test_substitution_failure_stops(self):
        mutant = self.tmp / "A_mut.v"
        mutant.write_text("Definition a := 5.\n")
        proc, out = self.run_tool("bad", "--substitute", f"Fake.A={mutant}", "--stop-on-first-error")
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        report = json.loads((out / "report.json").read_text())
        self.assertFalse(report["build_ok"])
        self.assertEqual(report["first_failure"]["module"], "Fake.Top")
        self.assertIn("Error", report["first_failure"]["error"])
        self.assertEqual(len(report["ast_substitution_hash"]), 64)

    def test_prepare_only_and_keep_objects(self):
        proc, out = self.run_tool("prep", "--prepare-only")
        self.assertEqual(proc.returncode, 0)
        self.assertTrue((out / "Makefile").exists())
        proc, out = self.run_tool("keep", "--keep-objects")
        self.assertTrue(list(out.rglob("*.vo")))

    def test_two_substitutions_by_file_path(self):
        m1, m2 = self.tmp / "A2.v", self.tmp / "B2.v"
        m1.write_text("Definition a := 1.\n")
        m2.write_text("Require Import Fake.A.\nDefinition b := a + 5.\n")
        proc, out = self.run_tool("two", "--substitute", f"{self.lib}/A.v={m1}",
                                  "--substitute", f"{self.lib}/B.v={m2}", "--stop-on-first-error")
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        report = json.loads((out / "report.json").read_text())
        self.assertEqual(len(report["ast_substitutions"]), 2)
        self.assertEqual(report["first_failure"]["module"], "Fake.Top")

    def test_design_subset_and_analyze(self):
        proc, out = self.run_tool("sub", "--design-root", "Fake.A")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        report = json.loads((out / "report.json").read_text())
        design, rest = report["design_subset"]["design_dependent"], report["design_subset"]["rest"]
        self.assertEqual((design["files"], rest["files"]), (3, 1))
        self.assertEqual(design["critical_path"][0].split("/")[-1], "A.v")
        again = subprocess.run([sys.executable, str(TOOL), "--analyze-subset", str(out),
                                "--design-root", "Fake.B"], capture_output=True, text=True)
        self.assertEqual(again.returncode, 0, again.stderr)
        redo = json.loads((out / "design_subset.json").read_text())
        self.assertEqual(redo["design_dependent"]["files"], 2)

    def reuse_setup(self):
        proc, base = self.run_tool("base", "--keep-objects")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        mutant = self.tmp / "A_ok.v"
        mutant.write_text("Definition a := 1.\nDefinition extra := 2.\n")
        return base, mutant

    def test_reuse_from_baseline(self):
        base, mutant = self.reuse_setup()
        proc, out = self.run_tool("mut", "--substitute", f"Fake.A={mutant}", "--reuse-from", str(base),
                                  "--stop-on-first-error", "--design-root", "Fake.A")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        report = json.loads((out / "report.json").read_text())
        self.assertEqual([f.split("/")[-1] for f in report["reuse"]["reused"]], ["C.v"])
        self.assertEqual(len(report["reuse"]["compiled"]), 3)
        self.assertEqual(report["files_reused"], 1)
        self.assertEqual(report["files_built"], 3)
        self.assertTrue(report["build_ok"])

    def test_reuse_refused_on_changed_source(self):
        base, mutant = self.reuse_setup()
        for c in base.rglob("C.v"):
            c.write_text("Definition c := 4.\n")
        proc, _ = self.run_tool("mut2", "--substitute", f"Fake.A={mutant}", "--reuse-from", str(base))
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("refusing reuse", proc.stderr)

    def test_reuse_needs_objects(self):
        proc, base = self.run_tool("noobj")
        mutant = self.tmp / "A_ok.v"
        mutant.write_text("Definition a := 1.\n")
        proc, _ = self.run_tool("mut3", "--substitute", f"Fake.A={mutant}", "--reuse-from", str(base))
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("no object", proc.stderr)

    # ---- two-phase modes
    def test_two_phase_vos_clean(self):
        proc, out = self.run_tool("tpv", "--two-phase", "vos", "--assumptions", "Fake.Top.t", "--keep-objects")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        report = json.loads((out / "report.json").read_text())
        self.assertTrue(report["build_ok"])
        info = report["two_phase"]
        self.assertEqual(set(info["phases"]), {"vos", "vok"})
        self.assertEqual(info["phases"]["vok"]["files_ok"], 4)
        self.assertFalse(info["guarantees"]["coqchk"])
        self.assertFalse(info["guarantees"]["equivalent_to_one_phase_double_zero"])
        self.assertIsNone(report["coqchk"])
        self.assertIsNone(report["assumptions"])
        self.assertFalse(list(out.rglob("*.vo")))
        self.assertEqual(len(list((out / "sandbox").rglob("*.vok"))), 4)
        self.assertEqual(json.loads(proc.stdout.splitlines()[-1])["mode"], "vos")

    def test_two_phase_vos_catches_proof_error_only_in_vok(self):
        mutant = self.tmp / "Top_bad.v"
        mutant.write_text("Require Import Fake.B.\nRequire Import Fake.C.\nTheorem t : b = 2. Proof. exact (eq_refl 3). Qed.\n")
        proc, out = self.run_tool("tpbad", "--two-phase", "vos", "--substitute", f"Fake.Top={mutant}")
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        report = json.loads((out / "report.json").read_text())
        self.assertFalse(report["build_ok"])
        self.assertEqual(report["two_phase"]["phases"]["vos"]["files_failed"], 0)
        self.assertEqual(report["two_phase"]["phases"]["vok"]["files_failed"], 1)
        self.assertEqual(report["first_failure"]["phase"], "vok")
        self.assertEqual(report["first_failure"]["module"], "Fake.Top")

    def test_two_phase_vos_catches_statement_error_in_dependency(self):
        mutant = self.tmp / "A_bad.v"
        mutant.write_text("Definition a := 1.\nDefinition broken : nat := true.\n")
        proc, out = self.run_tool("tpstmt", "--two-phase", "vos", "--substitute", f"Fake.A={mutant}")
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        report = json.loads((out / "report.json").read_text())
        self.assertEqual(report["first_failure"]["phase"], "vos")
        self.assertEqual(report["first_failure"]["module"], "Fake.A")

    def test_two_phase_vos_defined_and_section_proofs(self):
        (self.lib / "A.v").write_text(
            "Section S.\nVariable n : nat.\nHypothesis H : n = 0.\n"
            "Theorem u : n = 0. Proof using H. exact H. Qed.\nEnd S.\n"
            "Definition d : {n : nat | n = 2}. Proof. exists 2. reflexivity. Defined.\n"
            "Definition a := proj1_sig d.\n")
        (self.lib / "B.v").write_text("Require Import Fake.A.\nDefinition b := a - 1.\n")
        (self.lib / "Top.v").write_text("Require Import Fake.B.\nRequire Import Fake.C.\n"
                                        "Theorem t : b = 1. Proof. reflexivity. Qed.\n")
        proc, out = self.run_tool("tpdef", "--two-phase", "vos")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def test_two_phase_vio_full_assurance(self):
        proc, out = self.run_tool("tpio", "--two-phase", "vio", "--assumptions", "Fake.Top.t", "--keep-objects")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        report = json.loads((out / "report.json").read_text())
        self.assertTrue(report["build_ok"])
        self.assertEqual(report["coqchk"]["exit"], 0)
        self.assertTrue(report["assumptions"]["only_allowed"])
        self.assertEqual(report["two_phase"]["phases"]["vio2vo"]["exit"], 0)
        self.assertEqual(len(list(out.rglob("*.vo"))), 5)   # 4 files + Assumptions driver

    def test_two_phase_vio_catches_proof_error(self):
        mutant = self.tmp / "Top_bad.v"
        mutant.write_text("Require Import Fake.B.\nRequire Import Fake.C.\nTheorem t : b = 2. Proof. exact (eq_refl 3). Qed.\n")
        proc, out = self.run_tool("tpiobad", "--two-phase", "vio", "--substitute", f"Fake.Top={mutant}")
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        report = json.loads((out / "report.json").read_text())
        self.assertFalse(report["build_ok"])
        self.assertIsNone(report["coqchk"])

    def test_two_phase_with_require_lib(self):
        (self.lib / "Q.v").write_text("Definition q := 4.\n")
        (self.lib / "UsesQ.v").write_text("Definition uq := Fake.Q.q.\n")
        (self.lib / "Top.v").write_text("Require Import Fake.UsesQ.\nTheorem t : uq = 4. Proof. reflexivity. Qed.\n")
        for mode in ("vos", "vio"):
            proc, out = self.run_tool("tprq" + mode, "--two-phase", mode, "--require-lib", "Fake.UsesQ=Fake.Q")
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def test_two_phase_refuses_reuse(self):
        base, mutant = self.reuse_setup()
        proc, _ = self.run_tool("tpreuse", "--two-phase", "vos", "--substitute", f"Fake.A={mutant}",
                                "--reuse-from", str(base))
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("cannot be combined", proc.stderr)


    def test_substitute_outside_closure_rejected(self):
        mutant = self.tmp / "U.v"
        mutant.write_text("Definition u := 1.\n")
        proc, _ = self.run_tool("out", "--substitute", f"Fake.Unused={mutant}")
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("not in the closure", proc.stderr)


if __name__ == "__main__":
    unittest.main()
