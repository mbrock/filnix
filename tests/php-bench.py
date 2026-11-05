#!/usr/bin/env python3
"""Run without Nix, PHP or perf: python3 tests/php-bench.py."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class ProfileReportTests(unittest.TestCase):
    def test_old_anonymous_jit_samples_are_not_pcre(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            profile = {
                "app": "mediawiki", "variant": "filc-staging-jit",
                "period": 1000000, "passes": 1,
                "symbols": [
                    {"samples": 10, "dso": "libpcre2-8.so", "sym": "match", "cat": "PCRE"},
                    {"samples": 80, "dso": "[JIT] tid 123", "sym": "0x1234", "cat": "PCRE"},
                    {"samples": 10, "dso": "php", "sym": "extension_helper", "cat": "PHP functions & extensions"},
                ],
            }
            (path / "old.profile.json").write_text(json.dumps(profile))
            subprocess.run([sys.executable, str(ROOT / "bench/php/bench.py"),
                            "profile-report", directory], check=True, capture_output=True, text=True)
            rows = {}
            for line in (path / "profile.md").read_text().splitlines():
                if line.startswith("|"):
                    cells = [cell.strip() for cell in line.strip("|").split("|")]
                    rows[cells[0]] = cells
            self.assertEqual(float(rows["PCRE"][2]), 10)
            self.assertEqual(float(rows["generated JIT code (unresolved)"][2]), 80)
            self.assertEqual(float(rows["PHP functions & extensions"][2]), 10)


if __name__ == "__main__":
    unittest.main()
