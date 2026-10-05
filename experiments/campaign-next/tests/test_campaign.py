"""End-to-end tests for the DuckDB-backed campaign prototype."""

import json
import os
from pathlib import Path
import shutil
import signal
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
                f"{base or ''}/api/state?{urllib.parse.urlencode(query)}", timeout=2
            ).read()
        )

    def serve(self, database=None, mode="serve", drv=None, args=()):
        proc = subprocess.Popen(
            [
                str(BINARY),
                mode,
                *([str(drv)] if drv else []),
                str(database or self.db),
                *(["--store", self.store] if mode in ("watch", "cohort") else []),
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

    def cohort(self, roots, budget=10, root_timeout=5):
        manifest = self.root / "manifest.json"
        manifest.write_text(
            json.dumps(
                {
                    "id": "test-cohort",
                    "name": "Test landmark world",
                    "roots": [{"name": name, "drv": self.drv(name)} for name in roots],
                }
            )
        )
        return manifest, self.serve(
            mode="cohort",
            drv=manifest,
            args=("--budget", str(budget), "--root-timeout", str(root_timeout)),
        )

    def settled_cohort(self, base):
        deadline = time.monotonic() + 12
        while time.monotonic() < deadline:
            state = self.state(base=base)
            if state["cohort"] and state["cohort"]["stop_reason"]:
                return state
            time.sleep(0.05)
        self.fail("cohort did not publish its terminal admission event")

    def test_cohort_continues_failure_and_restart_never_retries(self):
        manifest, (proc, base) = self.cohort(["bad", "good"])
        try:
            state = self.settled_cohort(base)
            self.assertEqual(state["cohort"]["completed"], 2)
            self.assertEqual(state["cohort"]["succeeded"], 1)
            self.assertEqual(state["cohort"]["failed"], 1)
            self.assertEqual(state["cohort"]["unattempted"], 0)
            self.assertEqual(state["cohort"]["stop_reason"], "all-roots-attempted")
            published = json.load(urllib.request.urlopen(base + "/api/outputs", timeout=2))
            verified = sorted({o["path"] for s in state["sessions"]
                               if s["complete"] and s["outcome"] == "built"
                               for o in s["outputs"] if o["valid"]})
            self.assertTrue(verified)
            self.assertEqual(published["paths"], verified)
            self.assertEqual(published["watermark"], state["watermark"])
            good_run = state["session"]["run"]
            bad_run = next(s["run"] for s in state["sessions"] if s["run"] != good_run)
            pinned = self.state(bad_run, base)
            self.assertEqual(pinned["session"]["outcome"], "failed")
            self.assertEqual(pinned["cohort"]["succeeded"], 1)
            page = urllib.request.urlopen(base + "/", timeout=2).read()
            self.assertIn(b'src="./htmx.js"', page)
            self.assertIn(b'class="campaign-table"', page)
            self.assertNotIn(b'class="graph-panel"', page)
            self.assertNotIn(b'class="log-panel"', page)
            self.assertNotIn(b"every ", page)
            self.assertIn(b"2 of 2 roots settled", page)
            failed_roots = urllib.request.urlopen(
                base + "/sessions?overview=1&filter=failed", timeout=2
            ).read()
            self.assertIn(b"campaign-bad", failed_roots)
            self.assertNotIn(b"campaign-good", failed_roots)
            follow = urllib.request.urlopen(base + "/?follow=1", timeout=2).read()
            self.assertIn(b'class="graph-panel"', follow)
            self.assertIn(good_run.encode(), follow)
            watermark = state["watermark"]
        finally:
            self.stop(proc)
        restarted, base = self.serve(mode="cohort", drv=manifest)
        try:
            state = self.settled_cohort(base)
            self.assertEqual(state["watermark"], watermark)
            self.assertEqual(len(state["sessions"]), 2)
            self.assertEqual(json.load(urllib.request.urlopen(base + "/api/outputs"))["paths"], verified)
            self.assertFalse(state["live"])
        finally:
            self.stop(restarted)

    def test_cohort_root_timeout_continues_but_total_budget_stops_admission(self):
        _, (proc, base) = self.cohort(["slow", "good"], root_timeout=1)
        try:
            state = self.settled_cohort(base)
            self.assertEqual(state["cohort"]["timed_out"], 1)
            self.assertEqual(state["cohort"]["succeeded"], 1)
            self.assertEqual(state["cohort"]["completed"], 2)
            self.assertEqual(state["cohort"]["stop_reason"], "all-roots-attempted")
        finally:
            self.stop(proc)
        self.db = self.root / "budget.duckdb"
        _, (proc, base) = self.cohort(["slow", "shared"], budget=1)
        try:
            state = self.settled_cohort(base)
            self.assertEqual(state["cohort"]["completed"], 1)
            self.assertEqual(state["cohort"]["timed_out"], 1)
            self.assertEqual(state["cohort"]["unattempted"], 1)
            self.assertEqual(state["cohort"]["stop_reason"], "budget-exhausted")
            self.assertFalse(state["live"])
            self.assertEqual(len(state["sessions"]), 1)
        finally:
            self.stop(proc)
        with duckdb.connect(str(self.db), read_only=True) as db:
            events = db.execute("select seq,kind from events order by seq").fetchall()
        self.assertEqual([e[0] for e in events], list(range(1, len(events) + 1)))
        self.assertEqual(events[-2][1], "run.finished")
        self.assertEqual(events[-1][1], "cohort.finished")

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
        self.assertEqual(manifest["schema_version"], 1)
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
