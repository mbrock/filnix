"""Exercise rocq_reject.py through its CLI, with the real compiler and with stand-ins."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
RUNNER = HERE / "rocq_reject.py"


class RocqRejectTests(unittest.TestCase):
    def run_in(self, directory, command, timeout=60, file="T.v"):
        return subprocess.run(
            [sys.executable, str(RUNNER), "--file", file, "--timeout", str(timeout),
             "--log", "log", "--", *command],
            cwd=directory, capture_output=True, text=True, timeout=120)

    def rocq(self, source, **options):
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory) / "T.v").write_text(source)
            result = self.run_in(directory, ["rocq", "c", "-q", "T.v"], **options)
            return result, (Path(directory) / "log").read_text()

    def stand_in(self, script, **options):
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory) / "T.v").write_text("Goal True.\n")
            return self.run_in(directory, ["sh", "-c", script], **options)

    def refused(self, result, reason):
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("rocq_reject: refused: " + reason, result.stderr)

    def test_a_type_error_from_rocq_is_accepted(self):
        result, log = self.rocq("Definition x : nat := true.\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("rocq_reject: accepted: Rocq rejects T.v at line 1", result.stdout)
        self.assertIn('has type "bool" while it is expected to have type "nat"', log)

    def test_a_file_that_compiles_is_refused(self):
        result, _ = self.rocq("Definition x : nat := 0.\n")
        self.refused(result, "T.v compiles")

    def test_a_missing_library_is_refused(self):
        result, _ = self.rocq("From Nowhere Require Import X.\nDefinition x : nat := true.\n")
        self.refused(result, "the error at line 1 is not a rejection of the file: Cannot find a physical path")

    def test_a_timeout_is_refused(self):
        slow = ("Fixpoint slow (n : nat) : nat := match n with O => O | S m => slow m + slow m end.\n"
                "Eval cbv in slow 60.\nDefinition x : nat := true.\n")
        result, _ = self.rocq(slow, timeout=1)
        self.refused(result, "the compiler did not finish in 1 seconds")
        self.refused(self.stand_in("exit 124"), "the compiler exited with status 124")

    def test_a_signal_is_refused(self):
        self.refused(self.stand_in("kill -KILL $$"), "the compiler was ended by signal 9")
        self.refused(self.stand_in("kill -SEGV $$"), "the compiler was ended by signal 11")

    def test_an_unexpected_status_is_refused(self):
        located = 'printf \'File "./T.v", line 1, characters 0-1:\\nError: wrong\\n\'; '
        self.refused(self.stand_in(located + "exit 2"), "the compiler exited with status 2")
        self.refused(self.stand_in(located + "exit 129"), "the compiler exited with status 129")
        self.assertEqual(self.stand_in(located + "exit 1").returncode, 0)

    def test_status_one_without_an_error_in_the_file_is_refused(self):
        self.refused(self.stand_in("echo broken; exit 1"), "the compiler reported no error at a position in T.v")
        other = 'printf \'File "./Other.v", line 1, characters 0-1:\\nError: wrong\\n\'; exit 1'
        self.refused(self.stand_in(other), "the compiler reported no error at a position in T.v")
        warning = 'printf \'File "./T.v", line 1, characters 0-1:\\nWarning: odd\\n\'; exit 1'
        self.refused(self.stand_in(warning), "the compiler reported no error at a position in T.v")

    def test_a_resource_error_at_a_position_is_refused(self):
        for phrase in ["Out of memory.", "Stack overflow.", "Timeout!"]:
            script = f'printf \'File "./T.v", line 3, characters 0-9:\\nError: {phrase}\\n\'; exit 1'
            self.refused(self.stand_in(script), "the error at line 3 is not a rejection of the file")

    def test_a_tool_that_does_not_start_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            result = self.run_in(directory, ["./no-such-compiler", "T.v"])
        self.refused(result, "the compiler did not start")


if __name__ == "__main__":
    unittest.main()
