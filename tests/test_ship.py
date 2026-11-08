"""Shipping contracts against real disposable Git remotes and HTTP caches.

Nix evaluation/builds and SSH publication are controlled fixtures; the
ship/hook/checker CLIs and Git fast-forward checks are real.
"""
import copy
import functools
import http.server
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import threading
import unittest

ROOT = Path(__file__).resolve().parents[1]
ATTRS = [line for line in (ROOT / "scripts/ship-outputs.txt").read_text().splitlines()
         if line and not line.startswith("#")]
STAGING = "packages.x86_64-linux.filcc-staging"
SWIPL = "packages.x86_64-linux.site-swipl"


# One fixture command dispatcher, never used outside the temporary repository.
COMMAND = r'''#!/usr/bin/env python3
import json, os, pathlib, subprocess, sys, tempfile
p = pathlib.Path(os.environ['SHIP_FIXTURE'])
args = sys.argv[1:]
name = pathlib.Path(sys.argv[0]).name
with (p / 'commands').open('a') as f:
    f.write(json.dumps([name] + args) + '\n')
outputs = json.loads((p / 'outputs.json').read_text())
if name == 'nix':
    if 'eval' in args:
        if (p / 'advance-main').exists():
            (p / 'advance-main').unlink()
            remote = str(p / 'origin.git')
            base = subprocess.check_output(['git', '--git-dir', remote, 'rev-parse', 'main'], text=True).strip()
            tree = subprocess.check_output(['git', '--git-dir', remote, 'rev-parse', base + '^{tree}'], text=True).strip()
            sha = subprocess.check_output(['git', '--git-dir', remote, 'commit-tree', tree, '-p', base], input='other landing\n', text=True).strip()
            subprocess.run(['git', '--git-dir', remote, 'update-ref', 'refs/heads/main', sha], check=True)
        if (p / 'change-head').exists():
            (p / 'change-head').unlink()
            subprocess.run(['git', '-C', str(p / 'repo'), 'reset', '--hard', 'HEAD^'], check=True, stdout=subprocess.DEVNULL)
        if 'builtins.currentSystem' in args:
            print('x86_64-linux')
        elif (p / 'eval-error').exists():
            sys.exit(1)
        else:
            target = next(a for a in args if '#' in a)
            attr = target.split('#', 1)[1]
            print(json.dumps(outputs[attr]))
    elif 'build' in args:
        attr = next(a for a in args if '#' in a).split('#', 1)[1].removesuffix('^*')
        print('\n'.join(outputs[attr]))
    elif 'copy' not in args:
        sys.exit('unexpected nix invocation')
elif name == 'ssh':
    while args[0] == '-o': args = args[2:]
    args = args[1:]  # host
    if args[0].startswith('test -x '):
        sys.exit(0 if (p / 'publisher').exists() else 1)
    if '--help' in args:
        print('--republish-root' if not (p / 'old-publisher').exists() else '--extra-root')
    elif args[0] == 'mktemp':
        print(tempfile.mkdtemp(dir=p))
    elif args[0] == 'rm':
        import shutil
        shutil.rmtree(args[-1])
    elif args[0] == 'sudo':
        target = args[args.index('/opt/filnix-cache/bin/filnix-publish-cache') + 1]
        paths = [args[i + 1] for i, a in enumerate(args) if a in ('--extra-root', '--republish-root')]
        if target == 'cachix':
            # Model closure copying by publishing the fixture's reference graph.
            for root in paths:
                for path in [root] + json.loads((p / 'references.json').read_text()).get(root, []):
                    source = p / 'available' / (path.split('/')[-1].split('-')[0] + '.narinfo')
                    (p / 'cache' / 'filc' / source.name).write_text(source.read_text())
    elif args[0] != '/nix/var/nix/profiles/default/bin/nix-store':
        sys.exit('unexpected ssh invocation: ' + repr(args))
elif name == 'sudo':
    sys.exit(1)  # force the SSH path, never invoke a real publisher
'''


class QuietCache(http.server.SimpleHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def do_GET(self):
        if (Path(self.directory).parent / "http-error").exists():
            self.send_error(503)
        else:
            super().do_GET()


class ShippingTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.tmp = Path(temporary.name)
        self.repo = self.tmp / "repo"
        self.repo.mkdir()
        self.remote = self.tmp / "origin.git"
        self.bin = self.tmp / "bin"
        self.bin.mkdir()
        self.env = {**os.environ, "SHIP_FIXTURE": str(self.tmp),
                    "PATH": str(self.bin) + os.pathsep + os.environ["PATH"],
                    "GIT_AUTHOR_NAME": "Shipping test", "GIT_AUTHOR_EMAIL": "test@example.invalid",
                    "GIT_COMMITTER_NAME": "Shipping test", "GIT_COMMITTER_EMAIL": "test@example.invalid",
                    "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
                    "FILNIX_REQUIRE_CACHE": "0", "FILNIX_PUBLISH_HOST": "fixture.invalid"}
        self.env.pop("GITHUB_STEP_SUMMARY", None)
        for name in ("nix", "ssh", "sudo", "treefmt", "nixfmt", "actionlint"):
            path = self.bin / name
            path.write_text(COMMAND)
            path.chmod(0o755)
        self.outputs = {attr: [f"/nix/store/{i:032d}-{attr.rsplit('.', 1)[1]}"]
                        for i, attr in enumerate(ATTRS, 1)}
        # Multi-output attr: one output can need repair while the other is healthy.
        self.outputs[SWIPL].append("/nix/store/" + "9" * 32 + "-play-dev")
        (self.tmp / "outputs.json").write_text(json.dumps(self.outputs))
        self.available = self.tmp / "available"
        self.available.mkdir()
        for cache in ("filc", "nixos", "swa"):
            (self.tmp / "cache" / cache).mkdir(parents=True)
        self.child = "/nix/store/" + "8" * 32 + "-dependency"
        self.references = {paths[0]: [self.child] for paths in self.outputs.values()}
        (self.tmp / "references.json").write_text(json.dumps(self.references))
        for path in [p for paths in self.outputs.values() for p in paths] + [self.child]:
            refs = " ".join(p.removeprefix("/nix/store/") for p in self.references.get(path, []))
            name = path.split("/")[-1].split("-")[0] + ".narinfo"
            (self.available / name).write_text(f"StorePath: {path}\nReferences: {refs}\n")
            shutil.copy(self.available / name, self.tmp / "cache" / "filc" / name)
        server = http.server.ThreadingHTTPServer(
            ("127.0.0.1", 0), functools.partial(QuietCache, directory=str(self.tmp / "cache")))
        thread = threading.Thread(target=lambda: server.serve_forever(poll_interval=0.01), daemon=True)
        thread.start()
        self.addCleanup(thread.join)
        self.addCleanup(server.server_close)
        self.addCleanup(server.shutdown)
        url = f"http://127.0.0.1:{server.server_port}"
        for file in ("scripts/ship", "scripts/release", "scripts/ship-outputs.txt",
                     "scripts/swa-cache-outputs.txt", "scripts/ci-outputs.txt",
                     "scripts/git-hooks/lib.sh", "scripts/git-hooks/pre-push"):
            target = self.repo / file
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(ROOT / file, target)
        shutil.copy(ROOT / "scripts/ci-cache-check.py", self.repo / "scripts/cache-check-real.py")
        (self.repo / "scripts/ci-cache-check.py").write_text(
            "import runpy\nfrom pathlib import Path\n"
            "module = runpy.run_path(str(Path(__file__).with_name('cache-check-real.py')))\n"
            f"module['main'].__globals__['CACHES'] = ('{url}/filc', '{url}/nixos')\n"
            f"module['main'].__globals__['SWA_CACHE'] = '{url}/swa'\n"
            # closure's default captured the production tuple at definition time.
            f"module['closure'].__defaults__ = (('{url}/filc', '{url}/nixos'),)\n"
            "try:\n    module['main']()\nexcept Exception:\n    raise SystemExit(2)\n")
        self.run_command("git", "init", "-q", "--bare", "--initial-branch=main", str(self.remote))
        self.git("init", "-q", "--initial-branch=main")
        self.git("add", ".")
        self.git("commit", "-qm", "fixture foundation")
        self.base = self.git("rev-parse", "HEAD").stdout.strip()
        self.git("remote", "add", "origin", str(self.remote))
        self.git("push", "-q", "origin", "HEAD:main")
        # lib/ can change the foundations, so the candidate gets the cache gate.
        self.commit("lib/candidate.nix", "candidate")
        self.sha = self.git("rev-parse", "HEAD").stdout.strip()

    def run_command(self, *command, check=True, **kwargs):
        result = subprocess.run(command, cwd=self.repo, env=self.env, text=True,
                                capture_output=True, timeout=30, **kwargs)
        if check:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def git(self, *args, **kwargs):
        return self.run_command("git", *args, **kwargs)

    def commit(self, file, message):
        (self.repo / file).parent.mkdir(parents=True, exist_ok=True)
        (self.repo / file).write_text(message + "\n")
        self.git("add", file)
        self.git("commit", "-qm", message)

    def main(self):
        return self.git("--git-dir", str(self.remote), "rev-parse", "main").stdout.strip()

    def lose(self, path):
        (self.tmp / "cache/filc" / (path.split("/")[-1].split("-")[0] + ".narinfo")).unlink()

    def commands(self, name):
        file = self.tmp / "commands"
        return [row for line in file.read_text().splitlines() if (row := json.loads(line))[0] == name] if file.exists() else []

    def ship(self, *args, **kwargs):
        return self.run_command("bash", "scripts/ship", *args, **kwargs)

    def test_cached_change_rebases_and_lands_without_publication(self):
        other = self.tmp / "other"
        self.run_command("git", "clone", "-q", str(self.remote), str(other))
        (other / "docs").mkdir()
        (other / "docs/other.md").write_text("other\n")
        self.run_command("git", "-C", str(other), "add", "docs/other.md")
        self.run_command("git", "-C", str(other), "commit", "-qm", "other")
        self.run_command("git", "-C", str(other), "push", "-q", "origin", "HEAD:main")
        self.ship()
        head = self.git("rev-parse", "HEAD").stdout.strip()
        self.assertEqual(self.main(), head)
        self.assertEqual(self.git("log", "--format=%s", "-3").stdout.splitlines(),
                         ["candidate", "other", "fixture foundation"])
        self.assertFalse(self.commands("ssh"))
        self.assertFalse([r for r in self.commands("nix") if "build" in r])

    def test_nanofil_and_docs_changes_skip_the_cache_gate(self):
        self.git("reset", "-q", "--hard", self.base)
        self.lose(self.outputs[STAGING][0])
        self.commit("nanofil/src/ir.pl", "compiler")
        self.commit("docs/notes.md", "notes")
        self.git("config", "core.hooksPath", "scripts/git-hooks")
        self.ship("--no-publish")
        self.assertEqual(self.main(), self.git("rev-parse", "HEAD").stdout.strip())
        self.assertFalse(self.commands("nix"))
        # The playground's SWI-Prolog is a foundation inside nanofil/.
        self.commit("nanofil/web/play/swipl.nix", "swipl")
        failed = self.ship("--no-publish", check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertNotEqual(self.main(), self.git("rev-parse", "HEAD").stdout.strip())

    def test_main_moving_during_the_cache_check_rebases_and_pushes_again(self):
        (self.tmp / "advance-main").touch()
        result = self.ship()
        self.assertIn("main moved", result.stdout)
        head = self.git("rev-parse", "HEAD").stdout.strip()
        self.assertEqual(self.main(), head)
        self.assertEqual(self.git("log", "--format=%s", "-2").stdout.splitlines(), ["candidate", "other landing"])

    def test_no_publish_is_not_a_cache_waiver_but_cached_push_needs_no_publisher(self):
        self.lose(self.outputs[SWIPL][0])
        failed = self.ship("--no-publish", check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("not publishing", failed.stderr)
        self.assertEqual(self.main(), self.base)
        self.assertFalse(self.commands("ssh"))
        shutil.copytree(self.available, self.tmp / "cache/filc", dirs_exist_ok=True)
        self.ship("--no-publish")
        self.assertEqual(self.main(), self.sha)

    def test_missing_publisher_stops_without_push(self):
        self.lose(self.child)
        failed = self.ship(check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("no cache publisher", failed.stderr)
        self.assertEqual(self.main(), self.base)

    def test_hook_requires_main_caches_but_allows_feature_branch(self):
        self.lose(self.outputs[SWIPL][0])
        # Staged/working files cannot hide the committed missing foundation.
        (self.repo / "scripts/ship-outputs.txt").write_text(STAGING + "\n")
        self.git("config", "core.hooksPath", "scripts/git-hooks")
        result = self.git("push", "origin", "HEAD:main", check=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.main(), self.base)
        self.git("push", "origin", "HEAD:refs/heads/worker")
        self.assertEqual(self.git("--git-dir", str(self.remote), "rev-parse", "worker").stdout.strip(), self.sha)

    def test_publish_only_repairs_missing_output_at_already_main_and_is_idempotent(self):
        self.git("push", "-q", "origin", "HEAD:main")
        # Candidate differs from invoking HEAD: manifest/evaluation must use X.
        self.git("checkout", "-q", "--detach", self.base)
        missing = self.outputs[SWIPL][1]
        self.lose(missing)
        (self.tmp / "publisher").touch()
        self.ship("--publish-only", "--rev", self.sha)
        self.assertEqual(self.main(), self.sha)
        self.assertEqual(self.git("rev-parse", "HEAD").stdout.strip(), self.base)
        builds = [r for r in self.commands("nix") if "build" in r]
        self.assertEqual(len(builds), 1)
        self.assertIn(f"?rev={self.sha}#{SWIPL}^*", builds[0][-1])
        queues = [r for r in self.commands("ssh") if "--batches" in r]
        self.assertEqual(len(queues), 2)
        self.assertEqual(queues[0][-2:], ["--extra-root", missing])
        self.assertEqual(queues[1][-2:], ["--republish-root", missing])
        self.ship("--publish-only", "--rev", self.sha)
        self.assertEqual(len([r for r in self.commands("ssh") if "--batches" in r]), 2)

    def test_old_publisher_and_checker_errors_never_push(self):
        self.lose(self.outputs[SWIPL][0])
        (self.tmp / "publisher").touch()
        (self.tmp / "old-publisher").touch()
        failed = self.ship(check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("updated cache publisher", failed.stderr)
        for marker in ("http-error", "eval-error"):
            with self.subTest(marker=marker):
                (self.tmp / marker).touch()
                failed = self.ship(check=False)
                self.assertEqual(failed.returncode, 2)
                (self.tmp / marker).unlink()
        self.assertEqual(self.main(), self.base)
        self.assertFalse([r for r in self.commands("nix") if "build" in r])

    def test_json_report_tracks_transitive_misses_and_upstream_fallback(self):
        self.lose(self.child)
        failed = self.run_command(sys.executable, "scripts/ci-cache-check.py", "--json", STAGING, SWIPL, check=False)
        self.assertEqual(failed.returncode, 1)
        rows = json.loads(failed.stdout)
        self.assertEqual([r["missing"] for r in rows], [[self.child], [self.child]])
        self.assertEqual(rows[1]["outputs"][1]["missing"], [])
        source = self.available / (self.child.split("/")[-1].split("-")[0] + ".narinfo")
        shutil.copy(source, self.tmp / "cache/swa")
        self.assertEqual(self.run_command(sys.executable, "scripts/ci-cache-check.py", STAGING, check=False).returncode, 1)
        shutil.copy(source, self.tmp / "cache/nixos")
        self.run_command(sys.executable, "scripts/ci-cache-check.py", STAGING)


if __name__ == "__main__":
    unittest.main()
