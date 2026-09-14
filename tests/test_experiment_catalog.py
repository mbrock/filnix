"""Complete inventory, honest evidence/timing, and resumable worker observations."""

import gzip
import json
import sys
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from experiment.attempt import build
from experiment.catalog import catalog, source_link
from experiment.model import connect, import_campaign, encode, atomic_json
from experiment.nix import DEFAULT_POLICY
from experiment.timing import BuildTimes, ingest_times
from experiment.web import application, detail

DRV = "/nix/store/" + "a" * 32 + "-library.drv"


class CatalogTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.state = Path(self.tmp.name)
        self.db = connect(self.state)
        self.manifest = dict(
            attrPaths=[[f"package{i:03}"] for i in range(150)],
            nixpkgs=dict(type="github", owner="owner", repo="fork", rev="abc123"),
        )
        self.cid = import_campaign(
            self.db,
            "main",
            self.manifest,
            "/source",
            "revision",
            DEFAULT_POLICY,
            "test",
        )
        self.other = import_campaign(
            self.db,
            "other",
            dict(attrPaths=[["outside"]]),
            "/other",
            "revision",
            DEFAULT_POLICY,
            "test",
        )
        self.db.execute(
            "INSERT INTO derivations(drv,name,outputs) VALUES(?, 'lib','{}')", (DRV,)
        )
        self.db.execute(
            "UPDATE candidates SET drv=?,state='available' WHERE campaign=? AND label IN ('package000','package001')",
            (DRV, self.cid),
        )
        self.selection = dict(
            sourceFile="pkgs/by-name/li/library/package.nix",
            metadata=dict(
                description="A library <script>alert(1)</script>",
                version="1.2",
                position="/nix/store/source/pkgs/by-name/li/library/package.nix:12",
            ),
        )
        self.db.execute(
            "UPDATE candidates SET selection=? WHERE campaign=?",
            (encode(self.selection), self.cid),
        )
        self.db.commit()

    def tearDown(self):
        self.db.close()
        self.tmp.cleanup()

    def attempt(
        self,
        aid="old",
        created=100,
        finished=1000,
        kind="build",
        campaign=None,
        targets=None,
    ):
        self.db.execute(
            "INSERT INTO attempts(id,campaign,kind,targets,state,created,finished,spec) VALUES(?,?,?,?,?,?,?,'{}')",
            (
                aid,
                campaign or self.cid,
                kind,
                encode(targets if targets is not None else [DRV]),
                "finished" if finished is not None else "running",
                created,
                finished,
            ),
        )
        return aid

    def activity(self, aid="old", key="1", stopped=1):
        self.db.execute(
            "INSERT INTO activities(attempt,activity,drv,kind,phase,stopped) VALUES(?,?,?,'build','checkPhase',?)",
            (aid, key, DRV, stopped),
        )

    def test_all_rows_metadata_aliases_and_unknown_times(self):
        c = catalog(self.db, self.cid)
        self.assertEqual(len(c["rows"]), 150)
        p = c["rows"][0]
        self.assertEqual(p["description"], self.selection["metadata"]["description"])
        self.assertEqual(
            p["source_url"],
            "https://github.com/owner/fork/blob/abc123/pkgs/by-name/li/library/package.nix#L12",
        )
        self.assertEqual(p["version"], "1.2")
        self.assertIsNone(p["duration"])
        self.assertEqual(p["checks"], [])
        self.assertEqual(p["drv"], c["rows"][1]["drv"])
        with self.assertRaises(ValueError):
            catalog(self.db, "absent")

    def test_batch_time_is_not_build_time_and_test_phases_are_not_passes(self):
        self.attempt()
        self.activity()
        p = catalog(self.db, self.cid)["rows"][0]
        self.assertEqual((p["duration"], p["timing"]), (900, "batch"))
        self.assertEqual(p["checks"], [])
        self.db.execute("INSERT INTO build_times VALUES('old','1',110,130)")
        self.db.execute(
            "INSERT INTO tests VALUES('old',?,'checkPhase','observed')", (DRV,)
        )
        for p in catalog(self.db, self.cid)["rows"][:2]:
            self.assertEqual((p["duration"], p["timing"]), (20, "build"))
            self.assertEqual(p["checks"], ["checkPhase"])

    def test_planned_version_takes_precedence_without_rewriting_inventory(self):
        self.db.execute(
            "UPDATE candidates SET recipe=? WHERE campaign=? AND label='package000'",
            (encode({"version": "2.0", "revision": "new"}), self.cid),
        )
        rows = catalog(self.db, self.cid)["rows"]
        self.assertEqual(rows[0]["version"], "2.0")
        self.assertEqual(rows[1]["version"], "1.2")
        selection = json.loads(
            self.db.execute(
                "SELECT selection FROM candidates WHERE campaign=? AND label='package000'",
                (self.cid,),
            ).fetchone()[0]
        )
        self.assertEqual(selection, self.selection)

    def test_campaign_isolation_exclusions_and_cached_retry(self):
        self.attempt()
        self.activity()
        self.db.execute("INSERT INTO build_times VALUES('old','1',110,130)")
        self.attempt("cached", created=2000, finished=2001)
        self.attempt("outsider", created=3000, finished=4000, campaign=self.other)
        self.activity("outsider")
        self.db.execute(
            "INSERT INTO tests VALUES('outsider',?,'checkPhase','observed')", (DRV,)
        )
        self.db.execute(
            "UPDATE candidates SET state='excluded' WHERE label='package001'"
        )
        p = catalog(self.db, self.cid)["rows"][0]
        self.assertEqual(p["attempt"], "cached")
        self.assertEqual(
            (p["time_attempt"], p["duration"], p["timing"]), ("old", 20, "build")
        )
        self.assertIsNone(p["log_drv"])
        self.assertEqual(p["checks"], [])
        self.db.execute(
            "INSERT INTO tests VALUES('old',?,'checkPhase','observed')", (DRV,)
        )
        self.assertEqual(catalog(self.db, self.cid)["rows"][1]["checks"], [])

    def test_running_and_interrupted_times_and_evaluation_errors(self):
        self.attempt(finished=None)
        self.activity(stopped=0)
        self.db.execute("INSERT INTO build_times VALUES('old','1',110,NULL)")
        with patch("experiment.catalog.stamp", return_value=150):
            p = catalog(self.db, self.cid)["rows"][0]
        self.assertEqual((p["duration"], p["timing"]), (40, "building"))
        self.db.execute(
            "UPDATE attempts SET state='finished',finished=200 WHERE id='old'"
        )
        p = catalog(self.db, self.cid)["rows"][0]
        self.assertEqual((p["duration"], p["timing"]), (100, "batch"))
        cid = self.db.execute(
            "SELECT id FROM candidates WHERE campaign=? AND label='package002'",
            (self.cid,),
        ).fetchone()[0]
        self.attempt("eval", kind="plan", targets=[dict(id=cid, attr=["package002"])])
        self.db.execute(
            "UPDATE candidates SET state='evaluation-error',error=? WHERE id=?",
            ("error " * 1000, cid),
        )
        p = catalog(self.db, self.cid)["rows"][2]
        self.assertEqual(
            (p["timing"], p["attempt"], len(p["reason"])), ("eval-batch", "eval", 500)
        )

    def test_source_links_fail_closed(self):
        self.assertIsNone(source_link({}, self.selection))
        for path in ("../evil", "pkgs/../../evil", "/etc/passwd"):
            self.assertIsNone(source_link(self.manifest, dict(sourceFile=path)))
        self.assertIsNone(
            source_link(
                dict(nixpkgs=dict(type="github", owner="x/y", repo="foo", rev="abc")),
                self.selection,
            )
        )

    def test_evaluation_summary_preserves_the_full_observation(self):
        raw = "GC Warning: Failed to expand heap by 4194304 KiB\nerror:\n … while evaluating 'drv'\n\nerror: cannot coerce null to a string: null\n"
        self.db.execute(
            "UPDATE candidates SET state='evaluation-error',error=? WHERE campaign=? AND label='package002'",
            (raw, self.cid),
        )
        p = catalog(self.db, self.cid)["rows"][2]
        self.assertEqual(p["reason"], "cannot coerce null to a string: null")
        d = detail(self.db, p["id"])
        self.assertEqual(d["error_summary"], p["reason"])
        self.assertEqual(d["error"], raw)

    def test_full_read_only_api(self):
        seen = []
        payload = b"".join(
            application(self.state)(
                dict(
                    REQUEST_METHOD="GET",
                    PATH_INFO="/api/packages",
                    QUERY_STRING="campaign=" + self.cid,
                ),
                lambda status, headers: seen.append(status),
            )
        )
        self.assertEqual(seen, ["200 OK"])
        self.assertEqual(len(json.loads(payload)["rows"]), 150)

    def test_compressed_catalog_and_explicit_encoding_opt_out(self):
        for encoding, compressed in (
            ("gzip, br", True),
            ("gzip;q=0", False),
            ("gzip; q = 0", False),
            ("gzip;q=0.5", True),
        ):
            headers = []
            raw = b"".join(
                application(self.state)(
                    dict(
                        REQUEST_METHOD="GET",
                        PATH_INFO="/api/packages",
                        QUERY_STRING="campaign=" + self.cid,
                        HTTP_ACCEPT_ENCODING=encoding,
                    ),
                    lambda status, h: headers.extend(h),
                )
            )
            self.assertEqual(
                dict(headers).get("Content-Encoding") == "gzip", compressed
            )
            self.assertEqual(
                len(json.loads(gzip.decompress(raw) if compressed else raw)["rows"]),
                150,
            )

    def test_build_worker_captures_real_pipe_events_without_altering_raw_log(self):
        start = (
            "@nix " + encode(dict(action="start", id=1, type=105, fields=[DRV])) + "\n"
        )
        stop = '@nix {"action":"stop","id":1}\n'
        command = [
            sys.executable,
            "-c",
            f"import sys,time;sys.stderr.write({start!r});sys.stderr.flush();time.sleep(0.05);sys.stderr.write({stop!r})",
        ]
        with (
            patch("experiment.attempt.nix.resources", return_value=dict(verified=True)),
            patch("experiment.attempt.nix.command", return_value=command),
            patch("experiment.attempt.nix.valid", return_value=set()),
        ):
            result = build(
                self.state, dict(policy=DEFAULT_POLICY, targets=[DRV], output_paths=[])
            )
        self.assertEqual(result["exit_code"], 0)
        self.assertEqual((self.state / "stderr.log").read_text(), start + stop)
        times = json.loads((self.state / "build-times.json").read_text())["1"]
        self.assertGreater(times["finished"] - times["started"], 0)
        self.attempt()
        self.activity()
        ingest_times(self.db, self.state, "old")
        self.assertEqual(
            self.db.execute("SELECT finished-started FROM build_times").fetchone()[0],
            times["finished"] - times["started"],
        )

    def test_download_progress_does_not_consume_build_log_budget(self):
        progress = '@nix {"action":"result","type":105,"fields":[0,0,0,0]}\n'
        evidence = 'compiler output\n@nix {"action":"stop","id":1}\ntrailing'
        command = [
            sys.executable,
            "-c",
            f"import sys; sys.stderr.write({progress!r} * 10000 + {evidence!r})",
        ]
        with (
            patch("experiment.attempt.nix.resources", return_value=dict(verified=True)),
            patch("experiment.attempt.nix.command", return_value=command),
            patch("experiment.attempt.nix.valid", return_value=set()),
        ):
            result = build(
                self.state,
                dict(
                    policy=DEFAULT_POLICY | {"log_bytes": 1024},
                    targets=[DRV],
                    output_paths=[],
                ),
            )
        self.assertEqual(result["reason"], "completed")
        self.assertEqual(result["exit_code"], 0)
        self.assertFalse(result["truncated"])
        self.assertEqual(result["omitted_progress_records"], 10000)
        self.assertEqual((self.state / "stderr.log").read_text(), evidence)

    def test_worker_times_chunking_recovery_and_malformed_records(self):
        self.attempt()
        self.activity()
        times = BuildTimes(self.state)
        start = (
            b"@nix "
            + encode(dict(action="start", id=1, type=105, fields=[DRV])).encode()
            + b"\n"
        )
        stop = b"@nix " + encode(dict(action="stop", id=1)).encode() + b"\n"
        with patch("experiment.timing.stamp", return_value=120):
            times.feed(start[:12])
            times.feed(start[12:])
        ingest_times(self.db, self.state, "old")
        self.assertEqual(
            tuple(
                self.db.execute("SELECT started,finished FROM build_times").fetchone()
            ),
            (120, None),
        )
        with patch("experiment.timing.stamp", return_value=140):
            times.feed(stop)
        with patch("experiment.timing.stamp", return_value=999):
            times.feed(start + stop)
        ingest_times(self.db, self.state, "old")
        ingest_times(self.db, self.state, "old")
        self.assertEqual(
            tuple(
                self.db.execute("SELECT started,finished FROM build_times").fetchone()
            ),
            (120, 140),
        )
        self.assertEqual(
            self.db.execute("SELECT count(*) FROM build_times").fetchone()[0], 1
        )
        times.feed(b"@nix []\n@nix invalid\n" + b"x" * (1024**2 + 1))
        times.feed(b"\n" + start)
        atomic_json(
            self.state / "build-times.json",
            {
                "unobserved": dict(drv=DRV, started=100, finished=200),
                "1": dict(drv=DRV, started="bad", finished=200),
            },
        )
        ingest_times(self.db, self.state, "old")
        self.assertEqual(
            self.db.execute("SELECT count(*) FROM build_times").fetchone()[0], 1
        )

    def test_v2_migration_preserves_observations(self):
        self.attempt()
        self.activity()
        self.db.execute("DROP TABLE build_times")
        self.db.execute("PRAGMA user_version=2")
        self.db.commit()
        migrated = connect(self.state)
        self.assertEqual(migrated.execute("PRAGMA user_version").fetchone()[0], 4)
        self.assertEqual(
            migrated.execute("SELECT count(*) FROM activities").fetchone()[0], 1
        )
        self.assertEqual(
            migrated.execute("SELECT count(*) FROM build_times").fetchone()[0], 0
        )
        migrated.close()
