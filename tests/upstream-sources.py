#!/usr/bin/env python3
"""Exercise source isolation and pinned patch extraction without compiling LLVM.

Run from any directory with Python, Git and Nix available. Uses temporary Git
repositories and the flake's pinned nixpkgs; never changes the real upstream clone.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


def run(*args, cwd=None, check=True, env=None):
    return subprocess.run(args, cwd=cwd, check=check, env=env, text=True, capture_output=True)


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def write_json(path, value):
    write(path, json.dumps(value, indent=2) + "\n")


class UpstreamTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.repo = self.base / "upstream"
        self.repo.mkdir()
        run("git", "init", "-q", str(self.repo))
        self.git("config", "user.name", "Source isolation test")
        self.git("config", "user.email", "test@example.invalid")
        self.filnix = self.base / "filnix"
        for directory in ("lib", "scripts", "ports"):
            (self.filnix / directory).mkdir(parents=True)
        for name in ("lib/filc-upstream.json", "lib/filc-hashes.json", "lib/sources.nix",
                     "scripts/update-filc-source-hashes.py", "scripts/update-ports-pin.py", "ports/extract-patch.sh",
                     "ports/upstream.json", "ports/Makefile", "ports/extract-projeny.py"):
            shutil.copy2(ROOT / name, self.filnix / name)

    def test_ports_pin(self):
        write(self.repo / "projects/projeny/Makefile", "all:\n\ttrue\n")
        first = self.commit()
        script = self.filnix / "scripts/update-ports-pin.py"
        pin = self.filnix / "ports/upstream.json"
        def update(rev):
            return run("python3", str(script), "--repo", str(self.repo), "--rev", rev, check=False)
        self.assertEqual(update(first).returncode, 0)
        before = json.loads(pin.read_text())
        write(self.repo / "projects/other/source.c", "unrelated port\n")
        second = self.commit()
        self.assertEqual(update(second).returncode, 0)
        after = json.loads(pin.read_text())
        self.assertEqual(before["projenyHash"], after["projenyHash"])
        self.assertEqual(after["portsRev"], second)
        write(self.repo / "projects/projeny/Makefile", "all:\n\tfalse\n")
        third = self.commit()
        self.assertEqual(update(third).returncode, 0)
        self.assertNotEqual(after["projenyHash"], json.loads(pin.read_text())["projenyHash"])
        expected = pin.read_bytes()
        self.assertNotEqual(update("not-a-revision").returncode, 0)
        self.assertEqual(pin.read_bytes(), expected)
        shutil.rmtree(self.repo / "projects/projeny")
        self.assertNotEqual(update(self.commit()).returncode, 0)
        self.assertEqual(pin.read_bytes(), expected)

    @unittest.skipUnless(shutil.which(os.environ.get("PROJENY", "projeny")), "requires packaged Projeny")
    def test_projeny_import(self):
        projeny = shutil.which(os.environ.get("PROJENY", "projeny"))
        projects = self.repo / "projects"
        original = projects / "example-1.0"
        write(original / "source.c", "original\n")
        write(original / "configure", "generated original\n")
        write(original / "removed.c", "remove me\n")
        run("tar", "czf", "example-1.0.tar.gz", "example-1.0", cwd=projects)
        shutil.rmtree(original)
        descriptor = projects / "example.projeny"
        write(descriptor, "Archive: example-1.0.tar.gz\nOrigname: example-1.0\nName: example\n\n")
        run(projeny, "setup", str(descriptor))
        work = projects / "example"
        write(work / "source.c", "ported\n")
        write(work / "configure", "generated ported\n")
        write(work / "added.c", "new source\n")
        run(projeny, "add", str(descriptor), str(work / "added.c"))
        run(projeny, "rm", str(descriptor), str(work / "removed.c"))
        run(projeny, "commit", str(descriptor))
        shutil.rmtree(work)
        revision = self.commit()
        output = self.base / "patches"
        extractor = self.filnix / "ports/extract-patch.sh"
        def extract(rev):
            return run(str(extractor), "example.projeny", str(self.repo), str(output), rev, check=False)
        self.assertEqual(extract(revision).returncode, 0)
        patch = output / "example-1.0.patch"
        expected = patch.read_bytes()
        self.assertNotIn(b"generated", expected)
        run("tar", "xf", "example-1.0.tar.gz", cwd=projects)
        run("patch", "-p1", "-i", str(patch), cwd=original)
        self.assertEqual((original / "source.c").read_text(), "ported\n")
        self.assertTrue((original / "added.c").exists())
        self.assertFalse((original / "removed.c").exists())
        self.assertEqual((original / "configure").read_text(), "generated original\n")
        descriptor.write_text("dirty descriptor must not participate\n")
        self.assertEqual(extract(revision).returncode, 0)
        self.assertEqual(patch.read_bytes(), expected)
        self.assertNotEqual(extract("invalid-revision").returncode, 0)
        self.assertEqual(patch.read_bytes(), expected)
        self.git("checkout", revision, "--", "projects/example.projeny")
        run(projeny, "setup", str(descriptor))
        (work / "binary.dat").write_bytes(b"\x00\x01binary")
        run(projeny, "add", str(descriptor), str(work / "binary.dat"))
        run(projeny, "commit", str(descriptor))
        binary_revision = self.commit()
        result = extract(binary_revision)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Binary changes", result.stderr)
        self.assertEqual(patch.read_bytes(), expected)

    def git(self, *args):
        return run("git", "-C", str(self.repo), *args).stdout.strip()

    def commit(self):
        self.git("add", ".")
        self.git("commit", "-qm", "Fixture change")
        return self.git("rev-parse", "HEAD")

    def update(self, rev):
        run("python3", str(self.filnix / "scripts/update-filc-source-hashes.py"),
            "--repo", str(self.repo), "--rev", rev)
        return json.loads((self.filnix / "lib/filc-hashes.json").read_text())["hashes"]

    def nix(self, expression):
        return json.loads(run("nix", "eval", "--impure", "--json", "--expr", expression).stdout)

    def source_paths(self):
        # Exercise real fetchgit and downstream output identity. The .drv files
        # may change with the fetch URL/revision even when outputs are reusable.
        return self.nix(f'''
          let
            pkgs = import (builtins.getFlake "path:{ROOT}").inputs.nixpkgs {{ system = "x86_64-linux"; }};
            sources = import {self.filnix}/lib/sources.nix {{ inherit pkgs; }};
          in builtins.mapAttrs (name: _: {{
            source = sources.${{name}}.outPath;
            consumer = (pkgs.runCommand "source-consumer" {{ src = sources.${{name}}; }} "true").outPath;
          }}) sources.sourcePatterns
        ''')

    def test_component_hashes_and_store_identity(self):
        config = json.loads((self.filnix / "lib/filc-upstream.json").read_text())
        for patterns in config["sourcePatterns"].values():
            for pattern in patterns:
                relative = pattern.lstrip("/")
                if relative.endswith("/"):
                    relative += "fixture.c"
                write(self.repo / relative, "original\n")
        first = self.commit()
        hashes = self.update(first)
        paths = self.source_paths()

        # These must not enter any core fetch, including ancestor-directory files.
        for relative in ("README.md", "build_projeny.sh", "projects/README.md",
                         "projects/projeny/main.cpp", "filc/README.md", "filc/tests/new/test.c"):
            write(self.repo / relative, "unrelated change\n")
        next_rev = self.commit()
        self.assertEqual(hashes, self.update(next_rev[:12]))
        self.assertEqual(paths, self.source_paths())
        self.assertEqual(next_rev, json.loads((self.filnix / "lib/filc-upstream.json").read_text())["coreRev"])

        # A real change must invalidate precisely its component's consumers.
        for relative, component in (("libcxx/src/new.cpp", "libcxx-src"),
                                    ("libc/shared/new.h", "libcxx-src"),
                                    ("filc/src/new.c", "libpas-src"),
                                    ("llvm/lib/new.cpp", "filc0-src")):
            write(self.repo / relative, "core change\n")
            updated = self.update(self.commit())
            updated_paths = self.source_paths()
            self.assertEqual([component], [k for k in hashes if hashes[k] != updated[k]])
            self.assertEqual([component], [k for k in paths if paths[k] != updated_paths[k]])
            hashes, paths = updated, updated_paths
        self.assertEqual(1, self.git("worktree", "list", "--porcelain").count("worktree "))

        # A failed update must leave both the previous pin and hashes intact.
        before = [(self.filnix / "lib" / name).read_bytes()
                  for name in ("filc-upstream.json", "filc-hashes.json")]
        result = run("python3", str(self.filnix / "scripts/update-filc-source-hashes.py"),
                     "--repo", str(self.base / "missing"), "--rev", first, check=False)
        self.assertNotEqual(0, result.returncode)
        # Also fail during hashing, after a temporary worktree has been created.
        fake_nix = self.base / "bin/nix"
        write(fake_nix, "#!/bin/sh\nexit 42\n")
        fake_nix.chmod(0o755)
        result = run("python3", str(self.filnix / "scripts/update-filc-source-hashes.py"),
                     "--repo", str(self.repo), "--rev", first, check=False,
                     env=dict(os.environ, PATH=f"{fake_nix.parent}:{os.environ['PATH']}"))
        self.assertEqual(42, result.returncode)
        self.assertEqual(1, self.git("worktree", "list", "--porcelain").count("worktree "))
        shutil.rmtree(self.repo / "yolounwind")
        result = run("python3", str(self.filnix / "scripts/update-filc-source-hashes.py"),
                     "--repo", str(self.repo), "--rev", self.commit(), check=False)
        self.assertNotEqual(0, result.returncode)
        self.assertIn("source patterns matched no files", result.stderr)
        self.assertEqual(1, self.git("worktree", "list", "--porcelain").count("worktree "))
        self.assertEqual(before, [(self.filnix / "lib" / name).read_bytes()
                                 for name in ("filc-upstream.json", "filc-hashes.json")])

    def extract(self, project="example-1", rev=None, check=True):
        args = ["bash", str(self.filnix / "ports/extract-patch.sh"), project,
                str(self.repo), str(self.base / "patch")]
        if rev:
            args.append(rev)
        return run(*args, check=check)

    def test_pinned_extraction(self):
        project = self.repo / "projects/example-1"
        for name in ("code.c", "parser.y", "parser.c", "scanner.l", "scanner.c", "configure"):
            write(project / name, "original\n")
        original = self.commit()
        for name in ("code.c", "parser.c", "scanner.c", "configure"):
            write(project / name, "ported\n")
        pinned = self.commit()
        write_json(self.filnix / "ports/upstream.json", {"portsRev": pinned})
        self.extract()
        patch = self.base / "patch/example-1.patch"
        expected = patch.read_bytes()
        self.assertIn(b"+ported", expected)
        self.assertNotIn(b"parser.c", expected)
        self.assertNotIn(b"scanner.c", expected)
        self.assertNotIn(b"configure", expected)

        # New history plus dirty/untracked grammar files cannot change extraction.
        write(project / "code.c", "future\n")
        write(self.repo / "projects/future-1/code.c", "future project\n")
        self.commit()
        write(project / "code.y", "would incorrectly exclude code.c\n")
        (project / "parser.y").unlink()
        (project / "scanner.l").unlink()
        self.extract()
        self.assertEqual(expected, patch.read_bytes())
        listed = run("make", "-s", "list", f"REPO_DIR={self.repo}",
                     cwd=self.filnix / "ports").stdout.splitlines()
        self.assertEqual(["example-1"], listed)
        patch.write_text("stale patch\n")
        run("make", "-s", str(patch), f"REPO_DIR={self.repo}",
            f"OUTPUT_DIR={patch.parent}", cwd=self.filnix / "ports")
        self.assertEqual(expected, patch.read_bytes())

        # Works with an absent worktree project; a bad pin preserves the old patch.
        shutil.rmtree(project)
        self.extract()
        self.assertEqual(expected, patch.read_bytes())
        self.assertNotEqual(0, self.extract(rev="not-a-revision", check=False).returncode)
        self.assertEqual(expected, patch.read_bytes())
        self.extract(rev=original)
        self.assertFalse(patch.exists(), "an empty diff must remove a stale patch")

    def test_gettext_symbol_list(self):
        symbols = self.repo / "projects/gettext-1/libtextstyle/lib/libtextstyle.sym.in"
        write(symbols, "api\n")
        self.commit()
        write(symbols, "pizlonated_api\n")
        pinned = self.commit()
        self.extract("gettext-1", pinned)
        patch = self.base / "patch/gettext-1.patch"
        self.assertFalse(patch.exists())
        write(symbols, "pizlonated_api\npizlonated_new_api\n")
        self.extract("gettext-1", self.commit())
        self.assertIn("pizlonated_new_api", patch.read_text())

    def test_ports_pin_does_not_change_toolchain(self):
        # Evaluate the real toolchain before/after changing only ports provenance.
        checkout = self.base / "checkout"
        shutil.copytree(ROOT, checkout, ignore=shutil.ignore_patterns(".git", ".direnv", "result*", "__pycache__"))
        expression = f'''let pkgs = import (builtins.getFlake "path:{ROOT}").inputs.nixpkgs {{ system = "x86_64-linux"; }};
          in (import {checkout}/toolchain.nix {{ inherit pkgs; }}).drvPath'''
        before = self.nix(expression)
        write_json(checkout / "ports/upstream.json", {"portsRev": "0" * 40})
        self.assertEqual(before, self.nix(expression))


if __name__ == "__main__":
    unittest.main(verbosity=2)
