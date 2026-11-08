"""Program harness failures must explain their cause in retained check logs."""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


PROGTEST = Path(__file__).with_name("progtest.sh")


class HarnessTests(unittest.TestCase):
    def test_compile_timeout_reports_source_mode_status_and_timing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            compiler = root / "compiler"
            compiler.write_text(f"#!{shutil.which('bash')}\necho compiler-started >&2\nsleep 2\n")
            compiler.chmod(0o755)
            env = {**os.environ, "FILCC": shutil.which("true"), "SWIPL": str(compiler),
                   "NANOFIL_HOST": "swi", "NANOFIL_OPT": "-O",
                   "NANOFIL_CHECKS": "reference", "COMPILE_TIMEOUT": "0.1"}
            for companion in (False, True):
                source = root / "program.c"
                source.write_text("// nanofil-link: companion.c\n" if companion else "")
                (root / "companion.c").write_text("int helper(void) { return 0; }\n")
                for retained in (False, True):
                    with self.subTest(companion=companion, retained=retained):
                        output = root / "result"
                        args = ["--result", str(output)] if retained else []
                        result = subprocess.run(["bash", str(PROGTEST), *args, str(source)],
                                                env=env, text=True, capture_output=True, timeout=5)
                        self.assertNotEqual(result.returncode, 0)
                        log = (output / "log").read_text() if retained else result.stderr
                        self.assertIn("compile-timeout", log)
                        self.assertIn("companion.c" if companion else "program.c", log)
                        self.assertIn("checks=reference", log)
                        self.assertIn("-O", log)
                        self.assertIn("exit=124", log)
                        self.assertIn("compiler-started", log)
                        self.assertRegex(log, r"elapsed=[0-9.]+ user=[0-9.]+ system=[0-9.]+")
                        if retained:
                            self.assertEqual((output / "result").read_text(), "compile-timeout\n")

    def test_corpus_partitions_cover_each_outcome_once_and_detect_new_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copy(PROGTEST.with_name("corpus.py"), root / "corpus.py")
            # The program harness's public --result protocol, with controlled
            # outcomes so this checks selection and baseline comparison only.
            (root / "progtest.sh").write_text(
                'mkdir -p "$2"\nIFS= read -r outcome < "$3"\n'
                'printf "%s\\n" "${outcome#// }" > "$2/result"\n')
            expected = []
            for suite, path in (("cproc", "cproc/test"),
                                ("c-testsuite", "cts/tests/single-exec")):
                sources = root / path
                sources.mkdir(parents=True)
                for i in range(11):
                    outcome = ("pass", "reject", "no-main")[i % 3]
                    name = f"case-{i:02}.c"
                    code = "int helper(void);" if outcome == "no-main" else "int main(void) {}"
                    (sources / name).write_text(f"// {outcome}\n{code}\n")
                    expected.append(f"{suite}/{name}\t{outcome}\n")
            baseline = root / "corpus-expected.tsv"
            baseline.write_text(''.join(expected))
            command = [sys.executable, str(root / "corpus.py"), str(root / "cproc"), str(root / "cts")]
            observed = []
            for part in range(1, 5):
                work = root / f"part-{part}"
                result = subprocess.run([*command, "--partition", f"{part}/4", "--work", str(work)],
                                        text=True, capture_output=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                observed.extend((work / "results.tsv").read_text().splitlines(True))
            self.assertCountEqual(observed, expected)
            result = subprocess.run([*command, "--partition", "1/4", "--record"],
                                    text=True, capture_output=True, timeout=10)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(baseline.read_text(), ''.join(expected))
            (root / "cproc/test/new.c").write_text("// pass\nint main(void) {}\n")
            statuses = [subprocess.run([*command, "--partition", f"{part}/4"],
                                       text=True, capture_output=True, timeout=10).returncode
                        for part in range(1, 5)]
            self.assertEqual(sum(status != 0 for status in statuses), 1)


if __name__ == "__main__":
    unittest.main()
