#!/usr/bin/env python3
"""Tests for rocq_totals.py on a small tree whose answers are worked out by hand."""
import pathlib
import subprocess
import sys
import tempfile
import unittest

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import rocq_totals  # noqa: E402

# A (10 s, 100 lines) is imported by B (1 s) and C (20 s); D (5 s) imports B.
# An edit to A rechecks all four files serially in 36 s, but with unlimited
# cores only A then C, 30 s, so a sum and a longest path give different
# answers. D also names files of another tree, one of them sharing A's
# base name, which must not count.
TIMES = """\
@@glibc   10.0s   100 lines dir/A.v
@@glibc    1.0s    10 lines dir/B.v
@@glibc   20.0s     1 lines other/C.v
@@glibc    5.0s     1 lines D.v
noise that is not a record
"""
DEPS = """\
A:
B: Glibc/A
C: Glibc/A
D: Glibc/B Nanofil/Elsewhere Nanofil/A B
"""


class Totals(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        d = pathlib.Path(self.dir.name)
        (d / "times").write_text(TIMES)
        (d / "deps").write_text(DEPS)
        self.times, self.deps = str(d / "times"), str(d / "deps")

    def tearDown(self):
        self.dir.cleanup()

    def test_totals(self):
        time, lines, deps = rocq_totals.load(self.times, self.deps, "Glibc")
        self.assertEqual(deps["D"], {"B"})
        serial, critical, chain, own, rebuild, path = rocq_totals.totals(time, lines, deps)
        self.assertEqual(serial, 36)
        self.assertEqual(critical, 30)
        self.assertEqual(chain, ["C", "A"])
        # Line weights 100, 10, 1, 1 over own times 10, 1, 20, 5; recheck
        # sums 36, 6, 20, 5; recheck paths 30, 6, 20, 5.
        self.assertAlmostEqual(own, 1035 / 112)
        self.assertAlmostEqual(rebuild, 3685 / 112)
        self.assertAlmostEqual(path, 3085 / 112)

    def test_warning_only_over_threshold(self):
        out = subprocess.run(
            [sys.executable, str(HERE / "rocq_totals.py"), "--label", "t", "--warn", "15", "--namespace", "Glibc",
             self.times, self.deps],
            check=True, capture_output=True, text=True).stdout
        warnings = [line for line in out.splitlines() if "warning:" in line]
        self.assertEqual(len(warnings), 1)
        self.assertIn("C.v took 20.0s", warnings[0])
        self.assertIn("4 files, serial 36.0s, critical path 30.0s", out)


if __name__ == "__main__":
    unittest.main()
