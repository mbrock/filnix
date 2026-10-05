"""The version audit must follow Git pins and see descriptor-only ports."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    "audit", Path(__file__).resolve().parents[1] / "scripts/audit-port-versions.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class PortVersionAuditTests(unittest.TestCase):
    def test_pinned_tree_includes_projeny_but_not_archives_or_dirty_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            def git(*args):
                return subprocess.check_output(["git", "-C", tmp, *args], text=True).strip()
            git("init", "-q")
            git("config", "user.name", "Test")
            git("config", "user.email", "test@example.invalid")
            projects = repo / "projects"
            (projects / "libuv-1.52.1").mkdir(parents=True)
            (projects / "libuv-1.52.1/source.c").write_text("original\n")
            descriptor = projects / "libuv.projeny"
            descriptor.write_text("Origname: libuv-1.53.0\ndiff --git a/x b/x\n"
                                  "Origname: libuv-999\n")
            (projects / "libuv-100.tar.gz").write_text("archive\n")
            git("add", ".")
            git("-c", "commit.gpgsign=false", "commit", "-qm", "Pinned")
            pinned = git("rev-parse", "HEAD")
            descriptor.write_text("Origname: libuv-2.0.0\n")
            git("add", ".")
            git("-c", "commit.gpgsign=false", "commit", "-qm", "Later")
            descriptor.write_text("Origname: libuv-3.0.0\n")
            self.assertEqual(audit.upstream_projects(repo, pinned),
                             ["libuv-1.52.1", "libuv-1.53.0"])

    def test_candidates_use_package_aliases_and_exact_prefixes(self):
        projects = ["grep-3.12", "grep-tools-99", "libuv-1.53.0", "libuv-extra-2.0"]
        self.assertEqual(audit.candidates({"name": "gnugrep", "pname": "gnugrep"},
                                         projects), ["3.12"])
        self.assertEqual(audit.candidates({"name": "libuv", "pname": "libuv"},
                                         projects), ["1.53.0"])
        self.assertEqual(audit.candidates({"name": "gtk3", "pname": "gtk+"},
                                         ["gtk-3.24.52", "gtk-4.14.5"]), ["3.24.52"])

    def test_malformed_descriptor_fails_instead_of_hiding_port(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            subprocess.run(["git", "init", "-q", tmp], check=True)
            (repo / "projects").mkdir()
            (repo / "projects/broken.projeny").write_text("Name: broken\n")
            subprocess.run(["git", "-C", tmp, "add", "."], check=True)
            subprocess.run(["git", "-C", tmp, "-c", "user.name=Test",
                            "-c", "user.email=test@example.invalid", "-c", "commit.gpgsign=false",
                            "commit", "-qm", "Broken"], check=True)
            with self.assertRaisesRegex(ValueError, "missing Origname"):
                audit.upstream_projects(repo, "HEAD")


if __name__ == "__main__":
    unittest.main()
