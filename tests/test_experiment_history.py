"""Historical evidence, stable cursors, and bounded campaign-wide timelines."""

from contextlib import closing
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from experiment.history import (
    BUCKETS,
    PAGE_SIZE,
    TIMELINE_LIMIT,
    attempt_detail,
    history,
)
from experiment.model import connect, encode, import_campaign
from experiment.nix import DEFAULT_POLICY

DRV = "/nix/store/" + "a" * 32 + "-program.drv"


class HistoryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.state = Path(self.tmp.name)
        self.db = connect(self.state)
        self.cid = self.campaign("main")
        self.other = self.campaign("other")
        self.db.execute("UPDATE campaigns SET created=1000")
        self.db.execute("UPDATE candidates SET drv=? WHERE label='program'", (DRV,))
        self.db.execute(
            "INSERT INTO derivations(drv,name,outputs) VALUES(?, 'program', '{}')",
            (DRV,),
        )
        self.db.commit()
        self.clock = patch("experiment.history.stamp", return_value=10000)
        self.clock.start()

    def tearDown(self):
        self.clock.stop()
        self.db.close()
        self.tmp.cleanup()

    def campaign(self, name):
        return import_campaign(
            self.db,
            name,
            {"attrPaths": [["program"], ["pythonPackages", "extension"]]},
            "/source",
            "rev",
            DEFAULT_POLICY,
            "test",
        )

    def attempt(
        self,
        n,
        campaign=None,
        kind="build",
        state="finished",
        reason="completed",
        created=None,
        finished=None,
        targets=None,
    ):
        aid = f"attempt-{n:04d}"
        start = created if created is not None else 1000 + n * 10
        self.db.execute(
            "INSERT INTO attempts(id,campaign,kind,targets,state,created,finished,spec,result) VALUES(?,?,?,?,?,?,?,?,?)",
            (
                aid,
                campaign or self.cid,
                kind,
                encode(targets or [DRV]),
                state,
                start,
                (finished if finished is not None else start + 5)
                if state == "finished"
                else None,
                "{}",
                encode(
                    {"reason": reason, "exit_code": 0 if reason == "completed" else 1}
                )
                if state == "finished"
                else None,
            ),
        )
        return aid

    def test_stable_pages_with_tied_times_and_new_admissions(self):
        ids = [self.attempt(n, created=1500) for n in range(PAGE_SIZE + 4)]
        first = history(self.db, self.cid)
        self.assertEqual(
            [r["id"] for r in first["rows"]], list(reversed(ids))[:PAGE_SIZE]
        )
        self.attempt(100)
        second = history(
            self.db, self.cid, anchor=first["anchor"], before=first["rows"][-1]["id"]
        )
        self.assertEqual([r["id"] for r in second["rows"]], list(reversed(ids))[-4:])
        self.assertEqual(second["total"], PAGE_SIZE + 4)
        self.assertEqual(second["newer"], 1)
        self.assertFalse(second["more"])
        self.assertEqual(history(self.db, self.cid)["anchor"], "attempt-0100")

    def test_history_never_rewrites_old_evidence_from_current_outputs(self):
        old = self.attempt(1, reason="build-error")
        self.db.execute(
            "INSERT INTO activities(attempt,activity,drv,kind,phase,stopped) VALUES(?,'1',?,'build','checkPhase',1)",
            (old, DRV),
        )
        self.db.execute("INSERT INTO tests VALUES(?,?, 'checkPhase', '{}')", (old, DRV))
        before = attempt_detail(self.db, self.cid, old)
        new = self.attempt(2)
        self.db.execute(
            "UPDATE derivations SET available=1,failure=NULL,evidence_attempt=?", (new,)
        )
        self.assertEqual(attempt_detail(self.db, self.cid, old), before)
        self.assertEqual(before["reason"], "build-error")
        self.assertEqual((before["builds"], before["checks"]), (1, 1))
        self.assertTrue(before["activities"][0]["checked"])
        self.assertNotIn("available", before)

    def test_stopped_activity_without_success_is_not_checked(self):
        aid = self.attempt(1)
        self.db.execute(
            "INSERT INTO activities(attempt,activity,drv,kind,phase,stopped) VALUES(?,'1',?,'build','checkPhase',1)",
            (aid, DRV),
        )
        a = attempt_detail(self.db, self.cid, aid)
        self.assertEqual(a["builds"], 1)
        self.assertEqual(a["checks"], 0)
        self.assertFalse(a["activities"][0]["checked"])

    def test_campaign_scopes_rows_targets_and_cursors(self):
        self.attempt(1)
        outsider = self.attempt(2, campaign=self.other)
        h = history(self.db, self.cid)
        self.assertEqual(h["total"], 1)
        self.assertEqual(len(h["overview"]["intervals"]), 1)
        self.assertEqual(len(h["rows"][0]["targets"][0]["aliases"]), 1)
        for kw in ({"anchor": outsider}, {"before": outsider}):
            with self.assertRaises(ValueError):
                history(self.db, self.cid, **kw)
        with self.assertRaises(ValueError):
            attempt_detail(self.db, self.cid, outsider)

    def test_search_nested_attributes_and_filter_outcomes(self):
        cid = self.db.execute(
            "SELECT id FROM candidates WHERE campaign=? AND label='pythonPackages.extension'",
            (self.cid,),
        ).fetchone()[0]
        plan = self.attempt(
            1,
            kind="plan",
            targets=[{"id": cid, "attr": ["pythonPackages", "extension"]}],
        )
        failed = self.attempt(2, reason="build-error")
        self.attempt(3, state="running")
        self.assertEqual(
            [
                r["id"]
                for r in history(self.db, self.cid, search="PythonPackages.Ext")["rows"]
            ],
            [plan],
        )
        self.assertEqual(
            [r["id"] for r in history(self.db, self.cid, outcome="error")["rows"]],
            [failed],
        )
        self.assertEqual(history(self.db, self.cid, search="%")["total"], 0)
        self.assertEqual(
            history(self.db, self.cid, kind="plan", outcome="complete")["total"], 1
        )
        self.assertEqual(
            history(self.db, self.cid, kind="build", outcome="active")["total"], 1
        )
        self.assertEqual(history(self.db, self.cid, search="attempt-0002")["total"], 1)

    def test_read_only_connection(self):
        self.attempt(1)
        self.db.commit()
        with closing(connect(self.state, readonly=True)) as reader:
            before = reader.total_changes
            history(reader, self.cid)
            attempt_detail(reader, self.cid, "attempt-0001")
            self.assertEqual(reader.total_changes, before)
            with self.assertRaises(Exception):
                reader.execute("DELETE FROM attempts")

    def test_window_includes_long_running_attempt_starting_before_it(self):
        aid = self.attempt(1, state="running", created=1200)
        self.attempt(2, created=1300)
        o = history(self.db, self.cid, window=3600)["overview"]
        self.assertEqual((o["start"], o["end"]), (6400, 10000))
        self.assertEqual([r["id"] for r in o["intervals"]], [aid])
        self.assertEqual(o["totals"], {"active": 1, "complete": 1})

    def test_large_timeline_covers_full_duration_without_unbounded_response(self):
        for n in range(TIMELINE_LIMIT + 5):
            self.attempt(n, created=1000 + n, finished=1002 + n)
        self.attempt(900, state="running", created=1100)
        o = history(self.db, self.cid)["overview"]
        self.assertEqual(o["intervals"], [])
        self.assertEqual(sum(o["totals"].values()), TIMELINE_LIMIT + 6)
        self.assertLessEqual(len(o["buckets"]), BUCKETS * 2)
        active = [b for b in o["buckets"] if b["outcome"] == "active"]
        self.assertGreater(len(active), 140)
        self.assertEqual(active[-1]["n"], BUCKETS - 1)
        self.assertEqual(active[-1]["count"], 1)

    def test_empty_campaign_and_invalid_filters(self):
        h = history(self.db, self.cid)
        self.assertEqual(h["rows"], [])
        self.assertEqual(h["overview"]["intervals"], [])
        self.assertEqual(h["total"], 0)
        for kw in ({"kind": "invalid"}, {"outcome": "invalid"}, {"anchor": "missing"}):
            with self.assertRaises(ValueError):
                history(self.db, self.cid, **kw)
        with self.assertRaises(ValueError):
            history(self.db, "missing")
