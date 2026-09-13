"""Recovery and evidence invariants, independent of a running Nix daemon."""

import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from experiment import nix
from experiment.controller import Controller
from experiment.model import (
    atomic_json,
    blockers,
    connect,
    encode,
    import_campaign,
    refresh_candidates,
    stamp,
    writer_lock,
)
from experiment.web import application

A = "/nix/store/" + "a" * 32 + "-library.drv"
B = "/nix/store/" + "b" * 32 + "-program.drv"
C = "/nix/store/" + "c" * 32 + "-other.drv"
OUTPUT = "/nix/store/" + "d" * 32 + "-output"


class Units:
    def __init__(self):
        self.live, self.starts = set(), []

    def active(self, aid):
        return aid in self.live

    def start(self, aid):
        self.starts.append(aid)
        self.live.add(aid)

    def stop(self, aid):
        self.live.discard(aid)


class ExperimentTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.state = Path(self.tmp.name)
        self.db = connect(self.state)
        self.cid = import_campaign(
            self.db,
            "<script>bad</script>",
            {"attrPaths": [["a"], ["b"], ["alias"]]},
            "/nix/store/source",
            "abc",
            nix.DEFAULT_POLICY,
            "Nix test",
        )
        self.units = Units()
        self.controller = Controller(self.db, self.state, self.units)

    def tearDown(self):
        self.db.close()
        self.tmp.cleanup()

    def sql(self, statement, args=()):
        return self.db.execute(statement, args)

    def attempt(self, kind="plan"):
        return self.controller.intent(
            self.controller.campaign(self.cid),
            kind,
            [{"id": 1, "attr": ["a"]}] if kind == "plan" else [A],
            output_paths=[OUTPUT],
            derivations=[A],
        )

    def folder(self, aid):
        return self.state / "attempts" / aid

    def graph(self):
        for d in (A, B, C):
            self.sql(
                "INSERT INTO derivations(drv,name,outputs) VALUES(?,?,?)",
                (d, d, encode({"out": OUTPUT})),
            )
        self.sql("INSERT INTO edges VALUES(?,?,?)", (B, A, '["out"]'))
        self.sql("INSERT INTO edges VALUES(?,?,?)", (C, A, '["out"]'))
        for i, d in enumerate((A, B, B), 1):
            self.sql("UPDATE candidates SET drv=?,state='queued' WHERE id=?", (d, i))
        self.db.commit()

    def log(self, aid, record):
        with (self.folder(aid) / "stderr.log").open("ab") as f:
            f.write(b"@nix " + json.dumps(record).encode() + b"\n")

    def finish(self, aid, reason="completed"):
        atomic_json(
            self.folder(aid) / "exit.json",
            {
                "reason": reason,
                "exit_code": 0 if reason == "completed" else 1,
                "finished": stamp(),
            },
        )

    def test_import_is_paused(self):
        self.assertEqual(self.controller.campaign(self.cid)["mode"], "paused")
        self.controller.tick()
        self.assertEqual(self.units.starts, [])

    def test_exclusive_writer(self):
        with writer_lock(self.state):
            with self.assertRaises(ValueError):
                with writer_lock(self.state):
                    pass

    def test_intent_recovers_crash_before_launch(self):
        aid = self.attempt()
        self.controller.reconcile()
        self.assertEqual(self.units.starts, [aid])

    def test_restart_does_not_duplicate_launch(self):
        aid = self.attempt()
        self.controller.reconcile()
        Controller(self.db, self.state, self.units).reconcile()
        self.assertEqual(self.units.starts, [aid])

    def test_missing_exit_is_interruption(self):
        aid = self.attempt()
        atomic_json(self.folder(aid) / "started.json", {"pid": 100})
        self.controller.reconcile()
        result = json.loads(self.sql("SELECT result FROM attempts").fetchone()[0])
        self.assertEqual(result["reason"], "interrupted")

    def test_recreate_missing_spec_from_committed_intent(self):
        aid = self.attempt()
        (self.folder(aid) / "spec.json").unlink()
        self.controller.reconcile()
        self.assertTrue((self.folder(aid) / "spec.json").exists())

    def test_cancel_before_launch_stays_stopped(self):
        aid = self.attempt()
        self.controller.dispatch({"op": "cancel", "attempt": aid})
        self.controller.reconcile()
        self.assertEqual(self.units.starts, [])
        self.assertEqual(self.controller.campaign(self.cid)["mode"], "paused")

    def test_torn_log_and_replay_are_idempotent(self):
        aid = self.attempt()
        record = (
            b'@nix {"action":"start","type":105,"id":1,"fields":["'
            + A.encode()
            + b'"]}'
        )
        (self.folder(aid) / "stderr.log").write_bytes(record)
        row = self.sql("SELECT * FROM attempts").fetchone()
        self.controller.ingest(row)
        self.assertEqual(self.sql("SELECT count(*) FROM activities").fetchone()[0], 0)
        with (self.folder(aid) / "stderr.log").open("ab") as f:
            f.write(b"\n")
        self.controller.ingest(row)
        self.controller.ingest(row)
        self.assertEqual(self.sql("SELECT count(*) FROM activities").fetchone()[0], 1)

    def test_unknown_events_are_safe(self):
        aid = self.attempt()
        for record in [
            [],
            {"action": "future", "type": 999},
            {"action": "result", "fields": None},
        ]:
            self.log(aid, record)
        self.controller.ingest(self.sql("SELECT * FROM attempts").fetchone())
        self.assertEqual(self.sql("SELECT count(*) FROM tests").fetchone()[0], 0)

    def test_oversized_line_does_not_wedge_recovery(self):
        aid = self.attempt()
        (self.folder(aid) / "stderr.log").write_bytes(b"x" * (5 * 1024**2) + b"\n")
        self.controller.ingest(self.sql("SELECT * FROM attempts").fetchone())
        self.assertEqual(
            self.sql("SELECT offset FROM attempts").fetchone()[0], 5 * 1024**2 + 1
        )

    def test_dependency_failures_not_independent_root_failures(self):
        self.graph()
        self.sql("UPDATE derivations SET failure='configure' WHERE drv=?", (A,))
        refresh_candidates(self.db, self.cid)
        self.assertEqual(
            [r[0] for r in self.sql("SELECT state FROM candidates ORDER BY id")],
            ["failed", "blocked", "blocked"],
        )
        self.assertEqual(blockers(self.db, B)[0]["chain"], [B, A])

    def test_inconclusive_does_not_retry_implicitly(self):
        self.graph()
        self.sql("UPDATE candidates SET state='inconclusive' WHERE id=1")
        refresh_candidates(self.db, self.cid)
        self.assertEqual(
            self.sql("SELECT state FROM candidates WHERE id=1").fetchone()[0],
            "inconclusive",
        )

    def test_real_partial_batch_fixture(self):
        aid = self.attempt()
        raw = (
            Path(__file__).parent / "experiment-fixtures/nix-2.32.1-partial-batch.jsonl"
        ).read_bytes()
        for line in raw.splitlines():
            nix.observe(self.db, aid, line)
        failures = nix.failure_messages(raw)
        self.assertEqual(len(failures), 1)
        self.assertIn("bad-library", next(iter(failures)))
        phases = list(self.sql("SELECT checks FROM activities WHERE attempt=?", (aid,)))
        self.assertEqual(sum("checkPhase" in json.loads(r[0]) for r in phases), 1)

    def test_shared_root_only_submitted_once(self):
        self.graph()
        with patch(
            "experiment.nix.resources", return_value={"verified": True, "reason": ""}
        ):
            aid = self.controller.dispatch(
                {"op": "build-once", "campaign": self.cid, "ids": [2, 3]}
            )
        self.assertEqual(
            json.loads(
                self.sql("SELECT targets FROM attempts WHERE id=?", (aid,)).fetchone()[
                    0
                ]
            ),
            [B],
        )

    def test_cached_outputs_do_not_invent_checks(self):
        self.graph()
        aid = self.attempt("build")
        atomic_json(self.folder(aid) / "before.json", [OUTPUT])
        self.finish(aid)
        with patch("experiment.nix.valid", return_value={OUTPUT}):
            self.controller.reconcile()
        self.assertEqual(
            self.sql("SELECT origin FROM derivations WHERE drv=?", (A,)).fetchone()[0],
            "pre-existing",
        )
        self.assertEqual(self.sql("SELECT count(*) FROM tests").fetchone()[0], 0)

    def test_observed_checks_require_successful_realization(self):
        self.graph()
        aid = self.attempt("build")
        atomic_json(self.folder(aid) / "before.json", [])
        self.log(aid, dict(action="start", type=105, id=3, fields=[A]))
        self.log(aid, dict(action="result", type=104, id=3, fields=["checkPhase"]))
        self.finish(aid, "build-error")
        with patch("experiment.nix.valid", return_value={OUTPUT}):
            self.controller.reconcile()
        self.assertEqual(
            self.sql("SELECT phase FROM tests").fetchone()[0], "checkPhase"
        )

    def test_stop_event_does_not_prove_success(self):
        self.graph()
        aid = self.attempt("build")
        self.log(aid, dict(action="start", type=105, id=3, fields=[A]))
        self.log(aid, dict(action="result", type=104, id=3, fields=["checkPhase"]))
        self.log(aid, dict(action="stop", id=3))
        self.finish(aid, "build-error")
        with patch("experiment.nix.valid", return_value=set()):
            self.controller.reconcile()
        self.assertEqual(self.sql("SELECT count(*) FROM tests").fetchone()[0], 0)
        self.assertEqual(
            self.sql("SELECT state FROM candidates WHERE id=1").fetchone()[0],
            "inconclusive",
        )

    def test_oom_does_not_blame_recipe(self):
        self.graph()
        aid = self.attempt("build")
        self.log(
            aid, dict(action="msg", msg=f"builder for '{A}' failed with exit code 1")
        )
        self.finish(aid, "resource-interruption")
        with patch("experiment.nix.valid", return_value=set()):
            self.controller.reconcile()
        self.assertIsNone(
            self.sql("SELECT failure FROM derivations WHERE drv=?", (A,)).fetchone()[0]
        )

    def test_admission_requires_limits(self):
        self.graph()
        with patch(
            "experiment.nix.resources",
            return_value={"verified": False, "reason": "absent"},
        ):
            self.controller.admit(self.controller.campaign(self.cid))
        self.assertEqual(self.sql("SELECT count(*) FROM attempts").fetchone()[0], 0)

    def test_new_nix_relative_store_schema(self):
        data = {
            Path(A).name: {
                "outputs": {"out": {"path": Path(OUTPUT).name}},
                "inputDrvs": {Path(B).name: {"outputs": ["out"], "dynamicOutputs": {}}},
            }
        }
        fixed = nix.normalize_graph(data)
        self.assertEqual(fixed[A]["outputs"]["out"]["path"], OUTPUT)
        self.assertIn(B, fixed[A]["inputDrvs"])

    def request(self, path, query="", method="GET"):
        status = []
        payload = b"".join(
            application(self.state)(
                {"PATH_INFO": path, "QUERY_STRING": query, "REQUEST_METHOD": method},
                lambda s, h: status.append(s),
            )
        )
        return status[0], payload

    def test_web_has_no_mutation_endpoint(self):
        self.assertTrue(self.request("/api/run", method="POST")[0].startswith("405"))
        self.assertTrue(self.request("/api/run")[0].startswith("404"))

    def test_web_escapes_embedded_json(self):
        status, body = self.request("/")
        self.assertEqual(status, "200 OK")
        self.assertNotIn(b"<script>bad</script>", body)
        self.assertIn(b"\\u003cscript>", body)

    def test_log_path_traversal_rejected(self):
        self.assertTrue(
            self.request("/api/log", "attempt=../../etc/passwd")[0].startswith("400")
        )

    def test_stale_heartbeat_is_unhealthy(self):
        self.assertTrue(self.request("/healthz")[0].startswith("503"))
        self.controller.tick()
        self.assertTrue(self.request("/healthz")[0].startswith("200"))


if __name__ == "__main__":
    unittest.main()
