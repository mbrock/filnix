"""Exercise the check watchdog through its command-line interface."""
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

WATCH = str(Path(__file__).with_name("watch.py"))


class WatchTests(unittest.TestCase):
    def run_check(self, code, *options):
        return subprocess.run([sys.executable, WATCH, "--label", "test fixture",
                               *options, "--", sys.executable, "-u", "-c", code],
                              capture_output=True, text=True, timeout=10)

    def test_preserves_output_exit_code_and_does_not_duplicate_step_records(self):
        result = self.run_check("print('@@nanofil-step ok 1 fixture'); raise SystemExit(7)")
        self.assertEqual(result.returncode, 7)
        self.assertEqual(result.stdout.count("@@nanofil-step ok 1 fixture"), 1)
        self.assertIn("done exit=7", result.stdout)

    def test_silent_check_reports_regular_progress_and_warns_before_completion(self):
        result = self.run_check("import time; print('active corpus/file'); time.sleep(.5)",
                                "--interval", ".1", "--warn-after", ".2", "--timeout", "2")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertGreaterEqual(result.stdout.count(" running "), 2)
        self.assertEqual(result.stdout.count(" WARNING "), 1)
        self.assertIn("last=active corpus/file", result.stdout)
        self.assertRegex(result.stdout, r"@@nanofil-progress \d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ")
        self.assertLess(result.stdout.index(" WARNING "), result.stdout.index("done exit=0"))

    def test_deadline_kills_descendants_and_handles_child_closing_stdout(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / "escaped"
            child = ("import time,pathlib,signal; signal.signal(signal.SIGTERM, signal.SIG_IGN); "
                     f"time.sleep(2); pathlib.Path({str(marker)!r}).touch()")
            code = ("import subprocess,sys,os,time; "
                    f"subprocess.Popen([sys.executable,{WATCH!r},'--label','nested watchdog','--',"
                    f"sys.executable,'-c',{child!r}], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL); "
                    "os.close(1); os.close(2); time.sleep(5)")
            result = self.run_check(code, "--interval", ".1", "--warn-after", ".2", "--timeout", ".5")
            self.assertEqual(result.returncode, 124, result.stdout + result.stderr)
            self.assertIn("TIMEOUT budget=0.5s", result.stdout)
            time.sleep(2.1)
            self.assertFalse(marker.exists(), "timed-out grandchild must not survive")


if __name__ == "__main__":
    unittest.main()
