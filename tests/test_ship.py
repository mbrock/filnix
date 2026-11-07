"""Shipping contracts against real disposable Git remotes and HTTP caches.

Nix evaluation/builds, SSH publication and Amp workers are controlled fixtures;
the ship/hook/checker/fleet CLIs and Git fast-forward checks are real.
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
PLAY = "packages.x86_64-linux.site-play"


def receipt(sha):
    jobs = [f"nanofil@{i}/6" for i in range(1, 7)] + ["nanofil-rocq"]
    results = [{"job": job, "rev": sha, "status": "pass"} for job in jobs]
    for i, result in enumerate(results[:6]):
        result.update(shard=f"{i + 1}/6", all_steps={"count": 8, "hash": "0123456789abcdef"},
                      steps=[["ok", i + 1, f"step-{i}"]])
    results[0]["steps"] += [["ok", 13, "extra-a"], ["ok", 2, "extra-b"]]
    return {"fleet": {"rev": sha, "jobs": jobs, "size": "fixture", "bundle": False},
            "ok": True, "results": results}


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
            print(json.dumps(['nanofil-rocq', 'nanofil-rocq-full', 'nanofil-lua'] if attr == 'checks.x86_64-linux' else outputs[attr]))
    elif 'build' in args:
        attr = next(a for a in args if '#' in a).split('#', 1)[1].removesuffix('^*')
        if attr == 'checks.x86_64-linux.nanofil-rocq':
            if (p / 'quick-fails').exists(): sys.exit(1)
            if (p / 'worker-warnings').exists():
                print('@@nanofil-progress 2026-11-06T20:00:00Z WARNING budget=60s label=slow')
                print('@@nanofil-progress 2026-11-06T20:00:01Z TIMEOUT budget=300s label=slow')
                print('@@nanofil-rocq 2026-11-06T20:00:02Z start validator file=next.ir')
        else:
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
elif name == 'amp':
    job = args[args.index('--title') + 1].split()[-1]
    data = json.loads((p / 'worker-results.json').read_text())
    result = next(r for r in data['results'] if r['job'] == job)
    if job == 'nanofil-rocq' and (p / 'stream-progress').exists():
        import time
        progress = '@@nanofil-rocq 2026-11-06T20:00:00Z done validator opt=plain checks=reference file=/build/ldouble.c seconds=12'
        print(json.dumps({'type': 'user', 'message': {'content': [{'type': 'text', 'text': '@@nanofil-rocq prompt-only'}]}}), flush=True)
        response = json.dumps({'output': progress + '\n[120s] building: still working\n' + progress, 'running': True})
        event = json.dumps({'type': 'user', 'message': {'content': [{'type': 'tool_result', 'content': response}]}})
        sys.stdout.write(event[:10]); sys.stdout.flush()
        time.sleep(1.2)
        print(event[10:], flush=True)
        deadline = time.time() + 15
        while not (p / 'resume-worker').exists() and time.time() < deadline:
            time.sleep(.05)
        result['log_tail'] = [progress]
    print(json.dumps({'type': 'result', 'result': 'NANOFIL-FLEET-RESULT ' + json.dumps(result)}))
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
        for name in ("nix", "ssh", "sudo", "amp", "treefmt", "nixfmt", "actionlint"):
            path = self.bin / name
            path.write_text(COMMAND)
            path.chmod(0o755)
        self.outputs = {attr: [f"/nix/store/{i:032d}-{attr.rsplit('.', 1)[1]}"]
                        for i, attr in enumerate(ATTRS, 1)}
        # Multi-output attr: one output can need repair while the other is healthy.
        self.outputs[PLAY].append("/nix/store/" + "9" * 32 + "-play-dev")
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
        for file in ("scripts/ship", "scripts/release", "scripts/nanofil-fleet", "scripts/ship-outputs.txt",
                     "scripts/swa-cache-outputs.txt", "scripts/ci-outputs.txt",
                     "scripts/git-hooks/lib.sh", "scripts/git-hooks/pre-push",
                     "nanofil/tests/watch.py"):
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
        (self.repo / "nanofil/src").mkdir(parents=True)
        (self.repo / "nanofil/src/ir.pl").write_text("candidate\n")
        self.git("add", "nanofil/src/ir.pl")
        self.git("commit", "-qm", "candidate")
        self.sha = self.git("rev-parse", "HEAD").stdout.strip()
        self.evidence = self.tmp / "results.json"
        self.evidence.write_text(json.dumps(receipt(self.sha)))
        (self.tmp / "worker-results.json").write_text(self.evidence.read_text())

    def run_command(self, *command, check=True, **kwargs):
        result = subprocess.run(command, cwd=self.repo, env=self.env, text=True,
                                capture_output=True, timeout=30, **kwargs)
        if check:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def git(self, *args, **kwargs):
        return self.run_command("git", *args, **kwargs)

    def main(self):
        return self.git("--git-dir", str(self.remote), "rev-parse", "main").stdout.strip()

    def lose(self, path):
        (self.tmp / "cache/filc" / (path.split("/")[-1].split("-")[0] + ".narinfo")).unlink()

    def commands(self, name):
        file = self.tmp / "commands"
        return [row for line in file.read_text().splitlines() if (row := json.loads(line))[0] == name] if file.exists() else []

    def ship(self, *args, **kwargs):
        return self.run_command("bash", "scripts/ship", *args, **kwargs)

    def exact(self, **kwargs):
        return self.ship("--exact", self.sha, "--fleet-results", str(self.evidence), **kwargs)

    def test_cached_exact_lands_same_sha_without_publication(self):
        self.exact()
        self.assertEqual(self.main(), self.sha)
        self.assertEqual(self.git("rev-parse", "HEAD").stdout.strip(), self.sha)
        self.assertFalse(self.commands("ssh"))
        self.assertFalse([r for r in self.commands("nix") if "build" in r])
        self.assertFalse(self.commands("amp"))

    def test_no_publish_is_not_a_cache_waiver_but_cached_push_needs_no_publisher(self):
        self.lose(self.outputs[PLAY][0])
        failed = self.ship("--no-publish", check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("cannot waive", failed.stderr)
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
        self.lose(self.outputs[PLAY][0])
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
        missing = self.outputs[PLAY][1]
        self.lose(missing)
        (self.tmp / "publisher").touch()
        self.ship("--publish-only", "--rev", self.sha)
        self.assertEqual(self.main(), self.sha)
        self.assertEqual(self.git("rev-parse", "HEAD").stdout.strip(), self.base)
        builds = [r for r in self.commands("nix") if "build" in r]
        self.assertEqual(len(builds), 1)
        self.assertIn(f"?rev={self.sha}#{PLAY}^*", builds[0][-1])
        queues = [r for r in self.commands("ssh") if "--batches" in r]
        self.assertEqual(len(queues), 2)
        self.assertEqual(queues[0][-2:], ["--extra-root", missing])
        self.assertEqual(queues[1][-2:], ["--republish-root", missing])
        self.ship("--publish-only", "--rev", self.sha)
        self.assertEqual(len([r for r in self.commands("ssh") if "--batches" in r]), 2)

    def test_old_publisher_and_checker_errors_never_push(self):
        self.lose(self.outputs[PLAY][0])
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

    def test_exact_rejects_stale_head_and_main_movement_before_or_during_checks(self):
        self.git("checkout", "-q", "--detach", self.base)
        self.assertNotEqual(self.exact(check=False).returncode, 0)
        self.git("checkout", "-q", "--detach", self.sha)
        for marker in ("change-head", "advance-main"):
            with self.subTest(marker=marker):
                (self.tmp / marker).touch()
                failed = self.exact(check=False)
                self.assertNotEqual(failed.returncode, 0)
                self.assertNotEqual(self.main(), self.sha)
                self.git("checkout", "-q", "--detach", self.sha)
        failed = self.exact(check=False)
        self.assertIn("main diverged", failed.stderr)
        self.assertEqual(self.git("rev-parse", "HEAD").stdout.strip(), self.sha)

    def test_receipt_verifier_rejects_wrong_or_incomplete_evidence(self):
        original = receipt(self.sha)
        mutations = {
            "other-revision": lambda e: e["fleet"].update(rev="f" * 40),
            "root-missing-revision": lambda e: e["results"][-1].pop("rev"),
            "worker-wrong-revision": lambda e: e["results"][0].update(rev="e" * 40),
            "duplicate-shard": lambda e: e["results"].__setitem__(1, copy.deepcopy(e["results"][0])),
            "missing-shard": lambda e: e["results"].pop(2),
            "missing-rocq": lambda e: (e["results"].pop(), e["fleet"]["jobs"].pop()),
            "root-failed": lambda e: e["results"][-1].update(status="fail"),
            "step-failed": lambda e: e["results"][0]["steps"][0].__setitem__(0, "FAIL"),
            "coverage-gap": lambda e: e["results"][0]["steps"].pop(),
            "different-step-list": lambda e: e["results"][1]["all_steps"].update(hash="f" * 16),
        }
        for name, mutate in mutations.items():
            with self.subTest(name=name):
                evidence = copy.deepcopy(original)
                mutate(evidence)
                self.evidence.write_text(json.dumps(evidence))
                self.assertNotEqual(self.exact(check=False).returncode, 0)
                self.assertEqual(self.main(), self.base)
        self.evidence.write_text('{"ok":true,')
        self.assertNotEqual(self.exact(check=False).returncode, 0)
        # Requesting an additional root must not replace mandatory Rocq.
        evidence = copy.deepcopy(original)
        evidence["fleet"]["jobs"][-1] = "nanofil-lua"
        evidence["results"][-1]["job"] = "nanofil-lua"
        self.evidence.write_text(json.dumps(evidence))
        failed = self.ship("--exact", self.sha, "--fleet-results", str(self.evidence),
                           "--roots", "nanofil-lua", check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertFalse(self.commands("nix"))

    def test_collection_and_verification_share_coverage_contract(self):
        directory = self.tmp / "fleet"
        directory.mkdir()
        evidence = receipt(self.sha)
        (directory / "fleet.json").write_text(json.dumps(evidence["fleet"]))
        for wall in (539, 540):
            evidence["results"][0]["wall_s"] = wall
            for result in evidence["results"]:
                name = result["job"].replace("@", "_").replace("/", "_")
                event = {"type": "result", "result": "NANOFIL-FLEET-RESULT " + json.dumps(result)}
                (directory / (name + ".jsonl")).write_text(json.dumps(event) + "\n")
            collected = self.run_command(sys.executable, "scripts/nanofil-fleet", "collect", str(directory))
            self.assertEqual("WARNING: shard headroom" in collected.stdout, wall == 540)
            self.assertEqual("cp " in collected.stdout, wall == 540)
            self.assertIn("13\textra-a\n", (directory / "times.tsv").read_text())
        self.run_command(sys.executable, "scripts/nanofil-fleet", "verify", str(directory / "results.json"), "--rev", self.sha)
        self.assertTrue(json.loads((directory / "results.json").read_text())["coverage"]["complete"])

    def test_rocq_selection_and_evidence_distinguish_web_quick_and_full(self):
        quick = self.run_command(sys.executable, "scripts/nanofil-fleet", "run", "--dry-run")
        self.assertIn("--- nanofil-rocq\n", quick.stdout)
        all_roots = self.run_command(sys.executable, "scripts/nanofil-fleet", "run", "--roots", "all", "--dry-run")
        self.assertNotIn("--- nanofil-rocq-full\n", all_roots.stdout)
        full = self.run_command(sys.executable, "scripts/nanofil-fleet", "run", "--roots", "nanofil-rocq-full", "--dry-run")
        self.assertIn("--- nanofil-rocq-full\n", full.stdout)
        # A quick receipt is not release/soundness mutation evidence.
        rejected = self.run_command(sys.executable, "scripts/nanofil-fleet", "verify", str(self.evidence),
                                    "--rev", self.sha, "--roots", "nanofil-rocq-full", check=False)
        self.assertNotEqual(rejected.returncode, 0)
        full_evidence = receipt(self.sha)
        full_evidence["fleet"]["jobs"][-1] = "nanofil-rocq-full"
        full_evidence["results"][-1]["job"] = "nanofil-rocq-full"
        self.evidence.write_text(json.dumps(full_evidence))
        self.run_command(sys.executable, "scripts/nanofil-fleet", "verify", str(self.evidence),
                         "--rev", self.sha, "--roots", "nanofil-rocq-full")
        self.git("checkout", "-q", "--detach", self.base)
        (self.repo / "nanofil/web").mkdir(parents=True)
        (self.repo / "nanofil/web/style.css").write_text("body {}\n")
        self.git("add", ".")
        self.git("commit", "-qm", "web only")
        web = self.git("rev-parse", "HEAD").stdout.strip()
        selected = self.run_command(sys.executable, "scripts/nanofil-fleet", "required-roots")
        self.assertEqual(selected.stdout.strip(), "")
        evidence = receipt(web)
        evidence["fleet"]["jobs"].pop()
        evidence["results"].pop()
        self.evidence.write_text(json.dumps(evidence))
        self.run_command(sys.executable, "scripts/nanofil-fleet", "verify", str(self.evidence), "--rev", web)
        self.run_command("scripts/ship", "--exact", web, "--fleet-results", str(self.evidence))
        self.assertEqual(self.main(), web)

    def test_ordinary_ship_blocks_on_failed_quick_gate(self):
        (self.tmp / "quick-fails").touch()
        failed = self.ship("--no-publish", check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertEqual(self.main(), self.base)
        self.assertIn("checks.x86_64-linux.nanofil-rocq", " ".join(" ".join(c) for c in self.commands("nix")))

    def test_release_rejects_quick_receipt_before_creating_tag(self):
        self.git("push", "-q", "origin", self.sha + ":main")
        failed = self.run_command("scripts/release", "--fleet-results", str(self.evidence), "v-test", check=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("missing required roots", failed.stderr)
        self.assertEqual(self.git("tag", "-l").stdout.strip(), "")
        self.assertFalse(self.commands("nix"))

    def test_fleet_preflight_uses_candidate_and_stops_before_any_workers(self):
        self.lose(self.child)
        failed = self.run_command(sys.executable, "scripts/nanofil-fleet", "run", "--rev", self.sha,
                                  "--roots", "nanofil-rocq", "--out", str(self.tmp / "fleet"), check=False)
        self.assertEqual(failed.returncode, 1)
        self.assertIn("no workers launched", failed.stderr)
        self.assertFalse(self.commands("amp"))
        evals = self.commands("nix")
        self.assertIn(f"?rev={self.sha}#{STAGING}", " ".join(evals[0]))
        (self.tmp / "http-error").touch()
        failed = self.run_command(sys.executable, "scripts/nanofil-fleet", "run", "--rev", self.sha,
                                  "--roots", "nanofil-rocq", "--out", str(self.tmp / "fleet"), check=False)
        self.assertEqual(failed.returncode, 2)
        self.assertFalse(self.commands("amp"))

    def test_missing_playground_does_not_block_fleet_and_dry_run_launches_nothing(self):
        self.lose(self.outputs[PLAY][0])
        directory = self.tmp / "fleet"
        self.run_command(sys.executable, "scripts/nanofil-fleet", "run", "--rev", self.sha,
                         "--roots", "nanofil-rocq", "--out", str(directory), "--dry-run")
        self.assertFalse(self.commands("amp"))
        self.assertFalse(self.commands("nix"))
        self.run_command(sys.executable, "scripts/nanofil-fleet", "run", "--rev", self.sha,
                         "--roots", "all", "--out", str(directory), "--dry-run")
        self.assertIn(f"?rev={self.sha}#checks.x86_64-linux", " ".join(self.commands("nix")[0]))
        self.run_command(sys.executable, "scripts/nanofil-fleet", "run", "--rev", self.sha,
                         "--roots", "nanofil-rocq", "--out", str(directory))
        result = json.loads((directory / "results.json").read_text())
        self.assertTrue(result["ok"])
        self.assertEqual(result["fleet"]["rev"], self.sha)
        self.assertEqual(result["fleet"]["main"], self.base)
        self.assertEqual(len(self.commands("amp")), 7)

    def test_fleet_relays_timestamped_progress_before_worker_finishes(self):
        import queue
        (self.tmp / "stream-progress").touch()
        directory = self.tmp / "fleet"
        process = subprocess.Popen(
            [sys.executable, "scripts/nanofil-fleet", "run", "--rev", self.sha,
             "--roots", "nanofil-rocq", "--out", str(directory)],
            cwd=self.repo, env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        lines, arrived = [], queue.Queue()

        def read():
            for line in process.stdout:
                lines.append(line)
                arrived.put(line)

        reader = threading.Thread(target=read)
        reader.start()
        try:
            while "building: still working" not in arrived.get(timeout=15):
                pass
            self.assertIsNone(process.poll(), "progress must arrive before completion")
        finally:
            (self.tmp / "resume-worker").touch()
            process.wait(timeout=15)
            reader.join(timeout=5)
            errors = process.stderr.read()
            process.stdout.close()
            process.stderr.close()
        self.assertEqual(process.returncode, 0, errors)
        output = "".join(lines)
        self.assertRegex(output, r"\[\d{4}-\d\d-\d\dT[^]]+Z\] nanofil-rocq: @@nanofil-rocq")
        self.assertEqual(output.count("file=/build/ldouble.c seconds=12"), 1)
        self.assertNotIn("prompt-only", output)
        self.assertNotIn('"running":', output)
        self.assertTrue(json.loads((directory / "results.json").read_text())["ok"])

    def test_worker_never_samples_away_budget_warnings(self):
        (self.tmp / "worker-warnings").touch()
        self.env["HOME"] = str(self.tmp)
        (self.tmp / ".nix-profile").mkdir()
        (self.tmp / ".nix-profile/bin").symlink_to(self.bin)
        result = self.run_command(sys.executable, "scripts/nanofil-fleet", "worker", "nanofil-rocq")
        # The receipt retains warnings too, but they must reach the live output
        # even when later ordinary progress arrives in the same log read.
        live = result.stdout.split("NANOFIL-FLEET-RESULT ")[0]
        self.assertIn("@@nanofil-progress 2026-11-06T20:00:00Z WARNING ", live)
        self.assertIn("@@nanofil-progress 2026-11-06T20:00:01Z TIMEOUT ", live)

    def test_json_report_tracks_transitive_misses_and_upstream_fallback(self):
        self.lose(self.child)
        failed = self.run_command(sys.executable, "scripts/ci-cache-check.py", "--json", STAGING, PLAY, check=False)
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
