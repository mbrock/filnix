"""Exercise sentence timing warnings and the glibc capture through public CLIs."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
REPORTER = HERE / "rocq_time.py"


class RocqTimeTests(unittest.TestCase):
    def report(self, source, log):
        with tempfile.TemporaryDirectory() as directory:
            source_path = Path(directory) / "Timing.v"
            log_path = Path(directory) / "timings.log"
            source_path.write_text(source)
            log_path.write_text(log)
            return subprocess.run([sys.executable, str(REPORTER), str(source_path), str(log_path)],
                                  capture_output=True, text=True, timeout=10)

    def test_strictly_over_five_seconds_and_no_watchdog_duplicates(self):
        log = "".join(f"Chars 0 - 10 [Goal~True.] {seconds} secs (0.u,0.s)\n"
                      for seconds in ["0.", "4.999", "5.0", "5.000", "5.000001", "12.345"])
        log += "@@nanofil-progress running last=Chars 0 - 10 [Goal~True.] 12.345 secs (0.u,0.s)\n"
        result = self.report("Goal True.\n", log)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(result.stdout.splitlines()), 2)
        self.assertIn("took 5.000001s", result.stdout)
        self.assertIn("took 12.345s", result.stdout)
        self.assertIn(":1:1: warning:", result.stdout)
        self.assertIn("proof/vernacular", result.stdout)

    def test_real_rocq_format_utf8_offsets_and_loading_split(self):
        # These offsets and previews were emitted by Rocq 9.1.1 -time.
        source = "(* λ *)\nFrom Corelib Require Import Init.Prelude.\nGoal True.\nProof.\n  exact I.\nQed.\n"
        result = self.report(source,
                             "Chars 9 - 50 [From~Corelib~Require~Import~In...] 6.003 secs (0.003u,0.s)\n"
                             "Chars 71 - 79 [exact~I.] 7. secs (0.u,0.s)\n"
                             "Chars 80 - 84 [Qed.] 8. secs (0.u,0.s)\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        lines = result.stdout.splitlines()
        self.assertEqual(len(lines), 3)
        self.assertIn(":2:1: warning:", lines[0])
        self.assertIn("module loading", lines[0])
        self.assertIn(":5:3: warning:", lines[1])
        self.assertIn("proof/vernacular", lines[1])
        self.assertIn(":6:1: warning:", lines[2])

    def test_unqualified_require_load_and_multiline_require(self):
        for source in ["Require Import X.", 'Load "X".', "From X\nRequire Export Y."]:
            with self.subTest(source=source):
                result = self.report(source, f"Chars 0 - {len(source)} [command] 6. secs (1.u,0.s)\n")
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("module loading", result.stdout)

    def test_empty_and_unrelated_output_is_not_a_gate(self):
        for log in ["", "Error: failed\nChars malformed\n"]:
            result = self.report("Goal True.", log)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, "")

    def test_actual_nix_capture_keeps_compiler_status_and_logs(self):
        # Exercise the exact shell slice used in glibc.nix, replacing only Nix
        # interpolations. A fake rocq avoids building the full proof campaign.
        nix = (HERE.parent / "nix" / "glibc.nix").read_text()
        capture = nix[nix.index("        start=$(date"):nix.index("        mkdir $out")]
        capture = (capture.replace("${watch}", str(HERE / "watch.py"))
                   .replace("${../tests/rocq_time.py}", str(REPORTER))
                   .replace("${path.${n}}", "Timing"))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "glibc").mkdir()
            (root / "glibc" / "Timing.v").write_text("Goal True.\n")
            rocq = root / "rocq"
            rocq.write_text('#!/bin/sh\necho "Chars 0 - 10 [Goal~True.] 6. secs (0.u,0.s)"\n'
                            'echo "compiler diagnostic" >&2\nexit "$COMPILER_STATUS"\n')
            rocq.chmod(0o755)
            for status, reporter_fails in [(0, False), (7, False), (124, False), (0, True), (7, True)]:
                with self.subTest(status=status, reporter_fails=reporter_fails):
                    source = root / "glibc" / "Timing.v"
                    source.write_text("Goal True.\n")
                    if reporter_fails:
                        source.unlink()
                    result = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", capture],
                                            cwd=root, capture_output=True, text=True, timeout=10,
                                            env={**os.environ, "PATH": f"{root}:{os.environ['PATH']}",
                                                 "COMPILER_STATUS": str(status)})
                    self.assertEqual(result.returncode, status, result.stdout + result.stderr)
                    if reporter_fails:
                        self.assertIn("warning: Rocq sentence timing reporter failed", result.stderr)
                    else:
                        self.assertIn("warning: Rocq sentence took 6.s", result.stdout)
                    log = (root / "sentence-timings.log").read_text()
                    self.assertIn("compiler diagnostic", log)
                    self.assertIn(f"done exit={status}", log)


if __name__ == "__main__":
    unittest.main()
