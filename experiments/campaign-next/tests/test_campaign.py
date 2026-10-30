"""End-to-end tests for the DuckDB-backed campaign prototype."""

import http.client
import json
import os
from pathlib import Path
import shutil
import signal
import socket
import selectors
import subprocess
import sys
import tempfile
import time
import unittest
import urllib.error
import urllib.parse
import urllib.request

import duckdb

BINARY = Path(sys.argv.pop(1)).resolve()
FIXTURES = Path(__file__).with_name("fixtures.nix")


def invoke(*args, check=True, timeout=25, **kwargs):
    return subprocess.run(
        [str(BINARY), *map(str, args)],
        capture_output=True,
        check=check,
        timeout=timeout,
        **kwargs,
    )


class CampaignTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="campaign-next-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.store = (
            f"local?store={self.root}/store&state={self.root}/state&log={self.root}/log"
        )
        self.env = dict(
            os.environ,
            NIX_CONF_DIR=str(self.root),
            NIX_USER_CONF_FILES="",
            NIX_STATE_DIR=str(self.root / "nix-state"),
            NIX_CONFIG=(
                "sandbox = false\nbuild-users-group =\nsubstituters =\n"
                "build-hook =\nbuilders =\nmax-jobs = 1\ncores = 1\n"
            ),
        )
        self.db = self.root / "campaign.duckdb"

    def drv(self, name):
        return subprocess.check_output(
            [
                "nix-instantiate",
                "--store",
                self.store,
                str(FIXTURES),
                "-A",
                name,
                "--argstr",
                "shell",
                shutil.which("bash"),
                "--argstr",
                "path",
                os.environ["PATH"],
            ],
            env=self.env,
            text=True,
        ).strip()

    def record(self, drv, *args, check=False):
        return invoke(
            "record",
            drv,
            self.db,
            "--store",
            self.store,
            *args,
            check=check,
            env=self.env,
        )

    def state(self, run=None, base=None):
        query = {} if run is None else {"run": run}
        return json.loads(
            urllib.request.urlopen(
                f"{base or ''}/api/state?{urllib.parse.urlencode(query)}", timeout=5
            ).read()
        )

    def serve(self, database=None, mode="serve", drv=None, args=(), binary=None):
        proc = subprocess.Popen(
            [
                str(binary or BINARY),
                mode,
                *([str(drv)] if drv else []),
                str(database or self.db),
                *(["--store", self.store] if mode == "watch" else []),
                "--port",
                "0",
                *args,
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=self.env,
        )
        deadline = time.monotonic() + 6
        messages = b""
        with selectors.DefaultSelector() as selector:
            selector.register(proc.stderr, selectors.EVENT_READ)
            while time.monotonic() < deadline:
                if selector.select(timeout=0.1):
                    line = proc.stderr.readline()
                    messages += line
                    if line:
                        import re

                        match = re.search(
                            rb"Listening on http://127\.0\.0\.1:(\d+)", line
                        )
                        if match:
                            return proc, f"http://127.0.0.1:{match.group(1).decode()}"
                if proc.poll() is not None:
                    self.fail(f"viewer exited: {messages!r}, {proc.communicate()}")
        proc.kill()
        proc.communicate()
        self.fail(f"viewer did not announce its listening address: {messages!r}")

    def stop(self, proc, sig=signal.SIGTERM):
        if proc.poll() is None:
            proc.send_signal(sig)
        return proc.communicate(timeout=8)

    def rows(self, table):
        with duckdb.connect(str(self.db), read_only=True) as db:
            return db.execute(f"select * from {table} order by all").fetchall()

    def service(self, binary=None):
        """Start the campaign service on this test's store; return its
        process and HTTP base. Admin requests go to self.socket."""
        self.state_dir = self.root / "service"
        self.socket = self.state_dir / "admin.sock"
        return self.serve(database=self.state_dir, mode="service", binary=binary,
                          args=("--socket", str(self.socket), "--store", self.store))

    def admin(self, method, path, body=None, status=200):
        connection = http.client.HTTPConnection("localhost", timeout=20)
        connection.sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        connection.sock.connect(str(self.socket))
        connection.request(method, path, body=None if body is None else json.dumps(body))
        response = connection.getresponse()
        data = json.loads(response.read())
        connection.close()
        self.assertEqual(response.status, status, data)
        return data

    def submit(self, roots, policy=None, **extra):
        manifest = self.root / f"manifest-{time.monotonic_ns()}.json"
        manifest.write_text(json.dumps({
            "id": "test", "name": "Test campaign", "kind": "test", "revision": "0" * 40,
            "roots": [{"name": name, "drv": self.drv(fixture), **more}
                      for name, fixture, more in roots]}))
        body = {"manifest": str(manifest), "policy": policy or {}, **extra}
        return self.admin("POST", "/campaigns", body)["id"]

    def settled(self, id, states=("finished", "cancelled", "paused")):
        deadline = time.monotonic() + 30
        while time.monotonic() < deadline:
            shown = self.admin("GET", f"/campaigns/{id}")
            if shown["campaign"]["state"] in states:
                return shown
            time.sleep(0.05)
        self.fail(f"campaign {id} did not settle: {shown}")

    def test_service_requires_failure_analysis_outputs_and_restart(self):
        proc, base = self.service()
        try:
            id = self.submit([("bad", "bad", {}),
                              ("survey", "nanofilish", {"tags": ["nf"]}),
                              ("good", "good", {"tags": ["ref"]}),
                              ("after-bad", "graph", {"requires": ["bad"]}),
                              ("after-good", "left", {"requires": ["good"]})],
                             {"parallel_roots": 2, "graph": "direct"})
            unpublished = self.submit([("shared", "shared", {})], {"publish": False})
            shown = self.settled(id)
            self.assertEqual(shown["campaign"]["stop_reason"], "all-roots-attempted")
            roots = {r["name"]: r for r in shown["roots"]}
            self.assertEqual({n: r["outcome"] for n, r in roots.items()},
                             {"bad": "failed", "survey": "failed", "good": "built",
                              "after-bad": "skipped", "after-good": "built"})
            self.assertEqual(roots["bad"]["native_status"], "PermanentFailure")
            self.assertEqual(roots["bad"]["phase"], "buildPhase")
            self.assertEqual(roots["bad"]["error"], "dependency-failed")
            self.assertEqual(roots["bad"]["failed_drv"], self.drv("bad"))
            # nanofil's own message wins over an earlier compiler error.
            self.assertEqual(roots["survey"]["error"], "nanofil: unsupported construct at x.c:3")
            self.assertEqual(roots["survey"]["counts"],
                             {"objects": 7, "cxx": 1, "fallbacks": 2})
            self.assertIsNone(roots["after-bad"]["run"])
            for name in ("good", "after-good", "bad"):
                self.assertGreater(roots[name]["wall_ns"], 0)
                self.assertGreater(roots[name]["build_ns"], 0)
                self.assertEqual(roots[name]["machine"], "")
                self.assertGreaterEqual(roots[name]["load1"], 0)
            self.assertGreater(roots["good"]["wall_ns"], 500_000_000)  # its sleep
            self.settled(unpublished)
            listing = self.admin("GET", "/campaigns")
            row = next(c for c in listing if c["id"] == id)
            self.assertEqual((row["roots"], row["succeeded"], row["failed"], row["skipped"]),
                             (5, 2, 2, 1))
            # Only campaigns whose policy publishes feed the caches.
            outputs = json.load(urllib.request.urlopen(base + "/api/outputs", timeout=5))
            attempts = self.admin("GET", f"/campaigns/{id}/results")["attempts"]
            expected = sorted(o["path"] for a in attempts if a["outcome"] == "built"
                              for o in a["outputs"])
            self.assertEqual(len(expected), 2)
            self.assertEqual(sorted(outputs["paths"]), expected)
            page = urllib.request.urlopen(base + "/", timeout=5).read()
            self.assertIn(f'href="c/{id}/"'.encode(), page)
            self.assertIn(unpublished.encode(), page)
            state = json.load(urllib.request.urlopen(base + f"/c/{id}/api/state", timeout=5))
            self.assertEqual((state["cohort"]["succeeded"], state["cohort"]["failed"],
                              state["cohort"]["unattempted"]), (2, 2, 1))
            overview = urllib.request.urlopen(base + f"/c/{id}/", timeout=5).read()
            self.assertIn(b'class="campaign-table"', overview)
            self.assertIn(b'href="../../"', overview)
            self.assertIn(b"after-good", urllib.request.urlopen(
                base + f"/c/{id}/sessions?filter=all", timeout=5).read())
            old = urllib.request.urlopen(base + f"/?run={roots['good']['run']}", timeout=5)
            self.assertEqual(old.url, base + f"/c/{id}/?run={roots['good']['run']}")
            survey = urllib.request.urlopen(base + f"/c/{id}/survey", timeout=5).read()
            self.assertIn(b"nanofil: unsupported construct", survey)
            with self.assertRaises(urllib.error.HTTPError) as denied:
                urllib.request.urlopen(urllib.request.Request(
                    base + f"/c/{id}/", method="POST", data=b"{}"), timeout=5)
            self.assertEqual(denied.exception.code, 405)
        finally:
            self.stop(proc)
        attempts = self.rows_of("SELECT count(*) FROM attempts")
        proc, base = self.service()
        try:
            time.sleep(1)
            self.assertEqual(self.admin("GET", f"/campaigns/{id}")["campaign"]["state"],
                             "finished")
            self.assertEqual(self.rows_of("SELECT count(*) FROM attempts"), attempts)
        finally:
            self.stop(proc)

    def rows_of(self, query):
        # The catalog is the service's; read it only while it is stopped
        # or through a copy.
        copy = self.root / f"catalog-{time.monotonic_ns()}.duckdb"
        shutil.copy2(self.state_dir / "catalog.duckdb", copy)
        wal = self.state_dir / "catalog.duckdb.wal"
        if wal.exists():
            shutil.copy2(wal, str(copy) + ".wal")
        with duckdb.connect(str(copy)) as db:
            return [r[0] for r in db.execute(query).fetchall()]

    def test_service_timeout_budget_stop_retry_and_controls(self):
        proc, base = self.service()
        try:
            timed = self.submit([("slow", "slow", {}), ("good", "good", {})],
                                {"root_timeout": 1})
            shown = self.settled(timed)
            self.assertEqual([r["outcome"] for r in shown["roots"]], ["timed-out", "built"])
            budget = self.submit([("slow", "slow", {}), ("shared", "shared", {})],
                                 {"budget": 1})
            shown = self.settled(budget)
            self.assertEqual(shown["campaign"]["stop_reason"], "budget-exhausted")
            self.assertEqual([r["state"] for r in shown["roots"]], ["settled", "pending"])
            # Priority orders the queue: the later, higher one runs first.
            first = self.submit([("bad", "bad", {})], {}, priority=0)
            self.admin("POST", f"/campaigns/{first}/pause", {})
            second = self.submit([("graph", "graph", {})], {}, priority=5)
            self.settled(second)
            self.admin("POST", f"/campaigns/{first}/resume", {})
            shown = self.settled(first)
            self.assertEqual(shown["roots"][0]["outcome"], "failed")
            retried = self.admin("POST", f"/campaigns/{first}/retry", {})
            self.assertEqual(retried["retried"], ["bad"])
            shown = self.settled(first)
            self.assertEqual(shown["roots"][0]["attempt"], 2)
            self.admin("POST", f"/campaigns/{first}/resume", {}, status=400)
            # A service stop interrupts a root; restart runs it again.
            stopped = self.submit([("slow", "slow", {})], {"root_timeout": 30})
            deadline = time.monotonic() + 10
            while not self.admin("GET", "/status")["in_flight"]:
                self.assertLess(time.monotonic(), deadline)
                time.sleep(0.05)
        finally:
            self.stop(proc)
        proc, base = self.service()
        try:
            shown = self.settled(stopped)
            self.assertEqual(shown["roots"][0]["outcome"], "built")
            self.assertEqual(shown["roots"][0]["attempt"], 2)
            results = self.admin("GET", f"/campaigns/{stopped}/results")
            self.assertEqual([(a["attempt"], a["outcome"], a["note"]) for a in results["attempts"]],
                             [(1, "cancelled", "service-stopping"), (2, "built", None)])
            cancel = self.submit([("cancelled", "cancelled", {})], {"root_timeout": 30})
            deadline = time.monotonic() + 10
            while not self.admin("GET", "/status")["in_flight"]:
                self.assertLess(time.monotonic(), deadline)
                time.sleep(0.05)
            self.admin("POST", f"/campaigns/{cancel}/cancel", {})
            deadline = time.monotonic() + 10
            while (shown := self.settled(cancel))["roots"][0]["state"] != "settled":
                self.assertLess(time.monotonic(), deadline)
                time.sleep(0.05)
            self.assertEqual(shown["campaign"]["state"], "cancelled")
            self.assertEqual(shown["roots"][0]["outcome"], "cancelled")
            exported = self.root / "export"
            self.admin("POST", f"/campaigns/{timed}/export", {"directory": str(exported)})
            self.assertEqual(len(json.loads((exported / "results.json").read_text())["roots"]), 2)
            self.assertTrue((exported / "events.parquet").exists())
        finally:
            self.stop(proc)

    def test_service_registers_recordings_and_rejects_invalid_manifests(self):
        self.assertEqual(self.record(self.drv("good")).returncode, 0)
        self.assertEqual(self.record(self.drv("bad")).returncode, 1)
        copy = self.root / "copy.duckdb"
        shutil.copy2(self.db, copy)
        proc, base = self.service()
        try:
            registered = self.admin("POST", "/register", {"path": str(self.db), "id": "old"})
            self.assertEqual((registered["roots"], registered["attempts"]), (2, 2))
            duplicate = self.admin("POST", "/register", {"path": str(copy)})
            self.assertEqual(duplicate["duplicate_of"], "old")
            self.assertEqual([c["id"] for c in self.admin("GET", "/campaigns")], ["old"])
            self.assertEqual(len(self.admin("GET", "/campaigns?all=1")), 2)
            shown = self.admin("GET", "/campaigns/old")
            self.assertEqual(sorted(r["outcome"] for r in shown["roots"]), ["built", "failed"])
            self.assertEqual(shown["campaign"]["state"], "historical")
            state = json.load(urllib.request.urlopen(base + "/c/old/api/state", timeout=10))
            self.assertEqual(len(state["sessions"]), 2)
            self.admin("POST", "/campaigns/old/retry", {}, status=400)
            manifest = self.root / "invalid.json"
            root = {"name": "test", "drv": "/store/test.drv"}
            for roots, message in (([dict(root, name="")], "invalid root"),
                                   ([dict(root, drv="relative.drv")], "invalid root"),
                                   ([root, root], "invalid root"),
                                   ([dict(root, requires=["later"]), dict(root, name="later")],
                                    "requires an earlier root")):
                manifest.write_text(json.dumps({"id": "invalid", "name": "invalid",
                                                "roots": roots}))
                error = self.admin("POST", "/campaigns", {"manifest": str(manifest)}, status=400)
                self.assertIn(message, error["error"])
            manifest.write_text(json.dumps({"id": "valid", "name": "valid", "roots": [root]}))
            error = self.admin("POST", "/campaigns", {"manifest": str(manifest),
                                                      "policy": {"parallel_roots": 99}},
                               status=400)
            self.assertIn("parallel_roots", error["error"])
        finally:
            self.stop(proc)

    def test_build_replay_cached_run_http_and_parquet_roundtrip(self):
        drv = self.drv("good")
        result = self.record(drv)
        self.assertEqual(result.returncode, 0, result.stderr.decode(errors="replace"))
        summary = json.loads(result.stdout)
        run = summary["run"]
        with duckdb.connect(str(self.db), read_only=True) as db:
            events = db.execute(
                "select run,seq,wall_ns,elapsed_ns,kind,payload from events "
                "where run=? order by seq",
                [run],
            ).fetchall()
            self.assertTrue(db.execute("select count(*) from recipes").fetchone()[0])
        self.assertEqual([r[1] for r in events], list(range(1, len(events) + 1)))
        with duckdb.connect(str(self.db), read_only=True) as db:
            output = [
                row[0]
                for row in db.execute(
                    "select bytes from logs where run=? order by seq", [run]
                ).fetchall()
            ]
        self.assertIn(b"stdout-before", output)
        self.assertIn(b"stderr-after", output)
        colored = b"\x1b[32;1mcolored:\x1b[0m <text>&"
        self.assertIn(colored, output)
        self.assertIn(b"binary:\xff", output)
        self.assertIn(b"<script>alert(1)</script>", output)
        self.assertEqual(summary["outcome"], "built")
        self.assertEqual(summary, json.loads(invoke("inspect", self.db).stdout))
        for entry in summary["outputs"]:
            self.assertTrue(entry["valid"])
            self.assertEqual((Path(entry["path"]) / "result").read_text(), "artifact\n")
        captured = {
            bytes.fromhex(json.loads(row[5])["fields"][0]["string_hex"]): json.loads(
                row[5]
            )["capture"]["mono_ns"]
            for row in events
            if row[4] == "nix.result" and json.loads(row[5])["build_output"]
        }
        self.assertGreater(
            captured[b"stderr-after"] - captured[b"stdout-before"], 60_000_000
        )
        replay = invoke("replay", self.db, "--run", run, "--speed", "0", "--json")
        envelopes = [json.loads(line) for line in replay.stdout.splitlines()]
        self.assertEqual([e["seq"] for e in envelopes], list(range(1, len(events) + 1)))
        self.assertEqual(
            [e["offset"] for e in envelopes], sorted(e["offset"] for e in envelopes)
        )
        self.assertEqual(
            [
                (
                    e["run"],
                    e["seq"],
                    e["wall_ns"],
                    e["elapsed_ns"],
                    e["kind"],
                    e["payload"],
                )
                for e in envelopes
            ],
            [(r[0], r[1], r[2], r[3], r[4], json.loads(r[5])) for r in events],
        )
        raw_replay = invoke("replay", self.db, "--speed", "0").stdout
        self.assertIn(b"binary:\xff", raw_replay)
        self.assertIn(colored, raw_replay)
        for speed in ("nan", "inf", "-1", "1garbage"):
            self.assertEqual(
                invoke("replay", self.db, "--speed", speed, check=False).returncode, 2
            )

        # A meaningful gap distinguishes both unpaced and speed-ignored bugs.
        timeline = [row[3] for row in events]
        self.assertEqual(timeline, sorted(timeline))
        duration = (timeline[-1] - timeline[0]) / 1e9
        self.assertGreater(duration, 0.5)
        t0 = time.monotonic()
        invoke("replay", self.db, "--run", run, "--speed", "1", "--json")
        realtime = time.monotonic() - t0
        self.assertGreaterEqual(realtime, duration - 0.04)
        t0 = time.monotonic()
        invoke("replay", self.db, "--run", run, "--speed", "10", "--json")
        self.assertLess(time.monotonic() - t0, realtime * 0.75)

        viewer, base = self.serve()
        try:
            page = urllib.request.urlopen(base + "/?run=" + run, timeout=2).read()
            self.assertIn(b"&lt;script&gt;alert(1)&lt;/script&gt;", page)
            self.assertNotIn(b"<script>alert(1)</script>", page)
            self.assertIn(b"binary:\xef\xbf\xbd", page)
            rendered = b'<pre><span style="color:var(--ansi-2);font-weight:700;">colored:</span> &lt;text&gt;&amp;</pre>'
            self.assertIn(rendered, page)
            streamed = urllib.request.urlopen(
                base + "/logs?run=" + run + "&after=0", timeout=2
            ).read()
            self.assertIn(rendered, streamed)
            raw_logs = json.load(
                urllib.request.urlopen(base + "/api/logs?run=" + run, timeout=2)
            )
            self.assertIn(colored.hex(), [row["bytes_hex"] for row in raw_logs])
            for query in ("after=-1", "run=%1g", "run=%00"):
                with self.assertRaises(urllib.error.HTTPError) as error:
                    urllib.request.urlopen(base + "/api/logs?" + query, timeout=2)
                self.assertEqual(error.exception.code, 400)
        finally:
            self.stop(viewer)

        second = self.record(drv)
        self.assertEqual(second.returncode, 0, second.stderr.decode(errors="replace"))
        run2 = json.loads(second.stdout)["run"]
        self.assertNotEqual(run, run2)
        self.assertEqual(json.loads(second.stdout)["outcome"], "already-valid")
        with duckdb.connect(str(self.db), read_only=True) as db:
            self.assertEqual(
                db.execute("select count(distinct run) from runs").fetchone()[0], 2
            )
            offsets = db.execute(
                'select "offset" from events order by "offset"'
            ).fetchall()
            self.assertEqual(offsets, [(n,) for n in range(1, len(offsets) + 1)])

        target = self.root / "export"
        exported = invoke("export", self.db, target)
        self.assertEqual(
            exported.returncode, 0, exported.stderr.decode(errors="replace")
        )
        manifest = json.loads((target / "manifest.json").read_text())
        self.assertEqual(manifest["schema_version"], 2)
        self.assertIsInstance(manifest["watermark"], int)
        self.assertEqual(manifest["watermark"], offsets[-1][0])
        self.assertEqual(
            set(manifest["tables"]),
            {"events", "runs", "recipes", "edges", "activities", "logs"},
        )
        for table in manifest["tables"]:
            with duckdb.connect() as parquet:
                from_parquet = parquet.execute(
                    f"select * from read_parquet('{target / (table + '.parquet')}')"
                ).fetchall()
            self.assertEqual(
                sorted(from_parquet, key=repr), sorted(self.rows(table), key=repr)
            )
        before = sorted(p.name for p in target.iterdir())
        refused = invoke("export", self.db, target, check=False)
        self.assertNotEqual(refused.returncode, 0)
        self.assertEqual(sorted(p.name for p in target.iterdir()), before)

    def test_graph_http_cursor_offline_and_schema_rejection(self):
        result = self.record(self.drv("graph"))
        self.assertEqual(result.returncode, 0, result.stderr.decode(errors="replace"))
        run = json.loads(result.stdout)["run"]
        proc, base = self.serve()
        self.addCleanup(lambda: self.stop(proc))
        state = self.state(run, base)
        self.assertFalse(state["live"])
        self.assertGreaterEqual(len(state["sessions"]), 1)
        edges = state["edges"]
        self.assertTrue(all(isinstance(e["outputs"], list) for e in edges))
        self.assertTrue(all(isinstance(e["dynamic"], bool) for e in edges))
        shared = self.drv("shared")
        self.assertEqual(
            {e["parent_drv"] for e in edges if e["child_drv"] == shared},
            {self.drv("left"), self.drv("right")},
        )
        first = json.loads(
            urllib.request.urlopen(
                f"{base}/api/logs?run={run}&after=0", timeout=2
            ).read()
        )
        self.assertLessEqual(len(first), 256)
        if first:
            cursor = first[-1]["seq"]
            next_rows = json.loads(
                urllib.request.urlopen(
                    f"{base}/api/logs?run={run}&after={cursor}", timeout=2
                ).read()
            )
            self.assertTrue(all(row["seq"] > cursor for row in next_rows))
            activity = next((row["activity"] for row in first if row["activity"]), None)
            self.assertIsNotNone(activity)
            fragment = urllib.request.urlopen(
                f"{base}/logs?run={run}&activity={activity}&after=0", timeout=2
            ).read()
            self.assertIn(b"hx-swap-oob", fragment)
            self.assertIn(b'data-after="', fragment)
            tail = urllib.request.urlopen(
                f"{base}/logs?run={run}&after={cursor}&tail=1", timeout=2
            ).read()
            self.assertIn(b'class="log-row"', tail)
        self.assertEqual(
            urllib.request.urlopen(f"{base}/state?run={run}", timeout=2).status, 200
        )
        page = urllib.request.urlopen(base + "/?run=" + run, timeout=2).read()
        self.assertIn(b"graph-panel", page)
        self.assertIn(b"1 static inputs", page)
        self.assertNotIn(b'data-name="campaign-shared"', page)
        graph = urllib.request.urlopen(f"{base}/graph?run={run}", timeout=2).read()
        self.assertIn(b"reference", graph)
        self.assertIn(b'data-name="campaign-shared"', graph)
        for asset in ("htmx.js", "observatory.css", "observatory.js"):
            self.assertEqual(
                urllib.request.urlopen(base + "/" + asset, timeout=2).status, 200
            )
        with self.assertRaises(urllib.error.HTTPError) as error:
            urllib.request.urlopen(
                urllib.request.Request(base + "/api/state", method="POST"), timeout=2
            )
        self.assertEqual(error.exception.code, 405)
        self.stop(proc)

        missing = invoke(
            "serve", self.root / "missing.duckdb", "--port", "0", check=False
        )
        self.assertNotEqual(missing.returncode, 0)
        wrong = self.root / "unsupported.duckdb"
        with duckdb.connect(str(wrong)) as db:
            db.execute("create table unrelated(x int)")
        self.assertNotEqual(
            invoke("serve", wrong, "--port", "0", check=False).returncode, 0
        )

    def test_failure_worker_error_and_watch_cancel_live_http(self):
        failed = self.record(self.drv("blocked"))
        self.assertEqual(failed.returncode, 1, failed.stderr.decode(errors="replace"))
        run = json.loads(failed.stdout)["run"]
        with duckdb.connect(str(self.db), read_only=True) as db:
            results = db.execute(
                "select payload from events where run=? and kind='nix.build-result'",
                [run],
            ).fetchall()
            self.assertTrue(results)
            self.assertTrue(all(not json.loads(row[0])["success"] for row in results))
            output = [
                row[0]
                for row in db.execute(
                    "select bytes from logs where run=?", [run]
                ).fetchall()
            ]
            self.assertIn(b"dependency-failed", output)
            self.assertNotIn(b"consumer-must-not-run", output)
        viewer, base = self.serve()
        try:
            failed_state = self.state(run, base)
            self.assertEqual(failed_state["phases"][-1]["phase"], "buildPhase")
            page = urllib.request.urlopen(f"{base}/?run={run}", timeout=2).read()
            self.assertIn(b'class="failure"', page)
            self.assertIn(b"builder failed with exit code 13", page)
            self.assertIn(b"dependency-failed", page)
            self.assertIn(b'data-status="failed"', page)
            last_seq = failed_state["logs"][-1]["seq"]
            tail = urllib.request.urlopen(
                f"{base}/logs?run={run}&after={last_seq}&tail=1", timeout=2
            ).read()
            self.assertIn(b"dependency-failed", tail)
        finally:
            self.stop(viewer)
        drv = self.drv("good")
        Path(drv).unlink()
        api_error = self.record(drv)
        self.assertEqual(
            api_error.returncode, 2, api_error.stderr.decode(errors="replace")
        )

        proc, base = self.serve(mode="watch", drv=self.drv("slow"))
        try:
            state = None
            deadline = time.monotonic() + 8
            while time.monotonic() < deadline:
                state = self.state(base=base)
                if state["live"] and state["activities"]:
                    break
                time.sleep(0.05)
            self.assertTrue(state["live"])
            self.assertTrue(state["activities"])
            out, err = self.stop(proc, signal.SIGINT)
            self.assertNotEqual(proc.returncode, 0, err)
            self.assertIn(b'"outcome":"cancelled"', out.replace(b" ", b""))
            with duckdb.connect(str(self.db), read_only=True) as db:
                self.assertGreater(
                    db.execute("select count(*) from events").fetchone()[0], 0
                )
        finally:
            if proc.poll() is None:
                self.stop(proc, signal.SIGKILL)

    def test_recorder_error_pauses_the_campaign(self):
        # A broken worker protocol is an observer failure, not a build failure
        # eligible for continuation. The campaign stops admitting.
        bindir = self.root / "broken-worker"
        bindir.mkdir()
        binary = bindir / BINARY.name
        shutil.copy2(BINARY, binary)
        worker = bindir / "filnix-nix-worker"
        worker.write_text("#!" + shutil.which("bash") + "\nprintf 'broken protocol\\n' >&3\n")
        worker.chmod(0o755)
        proc, base = self.service(binary=binary)
        try:
            id = self.submit([("first", "good", {}), ("later", "shared", {})])
            shown = self.settled(id)
            self.assertEqual(shown["campaign"]["state"], "paused")
            self.assertEqual(shown["campaign"]["stop_reason"], "recorder-error")
            self.assertEqual([(r["state"], r["outcome"]) for r in shown["roots"]],
                             [("settled", "recorder-error"), ("pending", None)])
        finally:
            self.stop(proc)

    def test_large_journal_budget_and_v1_compatibility(self):
        # Generate a large closed recording quickly, then exercise the real
        # viewer. Repeated output/progress is deliberately much larger than
        # the 300-row overview; the overview must not materialize that journal.
        self.assertEqual(self.record(self.drv("good")).returncode, 0)
        count = int(os.environ.get("CAMPAIGN_MEMORY_TEST_ROWS", "2000000"))
        roots = [{"name": f"root-{i}", "drv": f"/store/root-{i}.drv"}
                 for i in range(300)]
        cohort = {"id": "memory-test", "name": "Large journal", "roots": roots}
        with duckdb.connect(str(self.db), read_only=True) as db:
            schema = db.execute("SELECT sql FROM duckdb_tables() WHERE NOT temporary").fetchall()
            original = db.execute("SELECT * FROM runs LIMIT 1").fetchone()
        # Start a fresh recording, as the real campaign does. Never rewrite
        # timestamps in an existing journal or depend on its old statistics.
        self.db = self.root / "large.duckdb"
        with duckdb.connect(str(self.db), config={"memory_limit": "1 GiB", "threads": 2}) as db:
            for (sql,) in schema:
                db.execute(sql)
            db.execute("INSERT INTO campaign_meta VALUES (2)")
            self.assertFalse(db.execute("SELECT index_name FROM duckdb_indexes() WHERE "
                                        "table_name IN ('events','logs')").fetchall())
            self.assertFalse(db.execute("SELECT constraint_type FROM duckdb_constraints() WHERE "
                                        "table_name IN ('events','logs') AND constraint_type "
                                        "IN ('PRIMARY KEY','UNIQUE')").fetchall())
            summary = json.loads(original[-1])
            summary.update(complete=False, outcome="incomplete")
            for i, root in enumerate(roots):
                run = f"run-{i}"
                db.execute("INSERT INTO runs VALUES (?,?,?,?,?,?,?,?::JSON)",
                           [run, root["drv"], "local", root["name"], "x86_64-linux",
                            i, count + i + 1, json.dumps(dict(summary, run=run))])
                db.execute("INSERT INTO events VALUES (?,?,1,0,0,'run.requested',?::JSON)",
                           [count+i+1, run, json.dumps(dict(root, store="local", cohort=cohort, index=i))])
            db.execute("""INSERT INTO events SELECT i+1,'run-'||(i%300)::VARCHAR,
                i//300+2,i,i,'nix.result',CASE WHEN i%13=0 THEN
                json_object('id',i%300,'type',101,'build_output',true,'fields',
                    json_array(json_object('string_hex',hex('build output '||i::VARCHAR||repeat('x',200)))))
                ELSE json_object('id',i%300,'type',105,'fields',
                    json_array(json_object('integer',i))) END FROM range(?) t(i)""", [count])
            db.execute("""INSERT INTO logs SELECT e."offset",run,seq,
                (e."offset"-1)%300,elapsed_ns,
                from_hex(json_extract_string(payload,'$.fields[0].string_hex')),kind
                FROM events e WHERE (e."offset"-1)%13=0 AND kind='nix.result'""")
            db.execute("""INSERT INTO events VALUES
                (?, 'run-299', ?,0,?,'nix.message',?::JSON),
                (?, 'run-299', ?,0,?,'nix.build-result',?::JSON)""",
                [count+301,count+2,count+1,json.dumps({"level":0,"text_hex":"626f6f6d"}),
                 count+302,count+3,count+2,json.dumps({"result":{"status":"failed"}})])
        # Both current recordings and indexed v1 archives must stay bounded.
        for version in (2, 1):
            if version == 1:
                with duckdb.connect(str(self.db)) as db:
                    db.execute("UPDATE campaign_meta SET schema_version=1")
                    db.execute('ALTER TABLE events ADD PRIMARY KEY ("offset")')
                    db.execute('CREATE UNIQUE INDEX legacy_sequence ON events(run,seq)')
                    db.execute('ALTER TABLE logs ADD PRIMARY KEY ("offset")')
                    db.execute('CREATE INDEX log_cursor ON logs(run,seq)')
            proc, base = self.serve()
            try:
                for _ in range(5):
                    # /sessions exercises the lightweight view without graphs/logs.
                    urllib.request.urlopen(base + "/sessions?run=run-299", timeout=5).read()
                state = self.state("run-299", base)
                unpinned = self.state(base=base)
                self.assertEqual(unpinned["session"]["run"], "run-299")
                self.assertEqual(unpinned["cohort"]["id"], "memory-test")
                self.assertEqual(len(state["sessions"]), 300)
                self.assertEqual(state["session"]["cause_hex"], "626f6f6d")
                self.assertEqual(state["session"]["native_status"], "failed")
                self.assertEqual(state["session"]["duration_ns"], count+2)
                self.assertEqual(state["cohort"]["incomplete"], 300)
                self.assertEqual(state["cohort"]["stop_reason"], "recording-interrupted")
                overview = urllib.request.urlopen(base + "/overview", timeout=5).read()
                self.assertIn(b"300</b> incomplete", overview)
                self.assertNotIn(b"300</b> building", overview)
                resources = json.load(urllib.request.urlopen(base + "/api/resources", timeout=2))
                self.assertEqual(resources["settings"][0], {"memory_limit":"1.0 GiB", "threads":2})
                high_water = next(int(line.split()[1]) * 1024 for line in
                                  Path(f"/proc/{proc.pid}/status").read_text().splitlines()
                                  if line.startswith("VmHWM:"))
                self.assertLess(high_water, 1600 * 1024**2)
                print(f"schema={version} events={count+302} peak_rss={high_water}", flush=True)
            finally:
                self.stop(proc)

    def test_abrupt_observer_recovery_and_read_only_methods(self):
        proc, base = self.serve(mode="watch", drv=self.drv("slow"))
        deadline = time.monotonic() + 8
        while time.monotonic() < deadline:
            live = self.state(base=base)
            if live["live"] and live["activities"]:
                break
            time.sleep(0.05)
        else:
            proc.kill()
            proc.wait(timeout=5)
            self.fail("watch did not expose its active build")
        request = urllib.request.Request(base + "/api/state", method="HEAD")
        self.assertEqual(urllib.request.urlopen(request, timeout=2).status, 200)
        proc.kill()  # Deliberately skip shutdown/finalization to exercise WAL recovery.
        proc.communicate(timeout=5)
        state = invoke("inspect", self.db)
        self.assertEqual(state.returncode, 0, state.stderr.decode(errors="replace"))
        summary = json.loads(state.stdout)
        self.assertFalse(summary["complete"])
        self.assertEqual(summary["outcome"], "incomplete")
        viewer, base = self.serve()
        try:
            offline = self.state(base=base)
            self.assertFalse(offline["live"])
            self.assertFalse(offline["session"]["complete"])
            fragment = urllib.request.urlopen(base + "/state", timeout=2).read()
            self.assertIn(b'data-status="incomplete"', fragment)
            self.assertNotIn(b"Live ", fragment)
        finally:
            self.stop(viewer)


if __name__ == "__main__":
    unittest.main()
