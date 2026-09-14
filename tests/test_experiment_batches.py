"""Batch wall times, observed dependency names, and historical outcomes."""

import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from experiment.batches import batches
from experiment.model import connect, encode, import_campaign
from experiment.nix import DEFAULT_POLICY
from experiment.web import application


class BatchTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.state = Path(self.tmp.name)
        self.db = connect(self.state)
        self.cid = self.campaign("main")
        self.other = self.campaign("other")
        self.root = "/nix/store/" + "a" * 32 + "-library.drv"
        self.dep = "/nix/store/" + "b" * 32 + "-dependency.drv"
        self.db.execute(
            "UPDATE candidates SET drv=? WHERE campaign=?", (self.root, self.cid)
        )
        self.db.execute(
            "INSERT INTO derivations(drv,name,outputs) VALUES(?,?,'{}')",
            (self.dep, "slow-sdk-1.2"),
        )

    def campaign(self, name):
        return import_campaign(
            self.db,
            name,
            dict(attrPaths=[["lib"], ["libAlias"]]),
            "/source",
            "rev",
            DEFAULT_POLICY,
            "test",
        )

    def tearDown(self):
        self.db.close()
        self.tmp.cleanup()

    def attempt(
        self,
        aid,
        end=160,
        state="finished",
        reason="completed",
        campaign=None,
        kind="build",
        targets=None,
    ):
        self.db.execute(
            "INSERT INTO attempts(id,campaign,kind,targets,state,created,finished,spec,result) VALUES(?,?,?,?,?,100,?,'{}',?)",
            (
                aid,
                campaign or self.cid,
                kind,
                encode(targets if targets is not None else [self.root]),
                state,
                end,
                encode(dict(reason=reason)) if reason else None,
            ),
        )

    def test_complete_catalog_and_known_unknown_elapsed_times(self):
        for n in range(450):
            self.attempt(f"done-{n:03}")
        self.attempt("running", end=None, state="running", reason=None)
        self.attempt("missing", end=None, reason=None)
        self.attempt("outsider", campaign=self.other)
        with patch("experiment.batches.stamp", return_value=200):
            result = batches(self.db, self.cid)
        rows = {r["id"]: r for r in result["rows"]}
        self.assertEqual(len(rows), 452)
        self.assertEqual(rows["done-001"]["duration"], 60)
        self.assertEqual(rows["running"]["duration"], 100)
        self.assertEqual(rows["running"]["outcome"], "active")
        self.assertIsNone(rows["missing"]["duration"])
        self.assertEqual(rows["missing"]["outcome"], "unknown")
        self.assertNotIn("outsider", rows)
        with self.assertRaises(ValueError):
            batches(self.db, "missing-campaign")

    def test_aliases_transitive_names_checks_and_attempt_outcome(self):
        self.attempt("failed", reason="build-failed")
        self.attempt("outsider", campaign=self.other)
        for aid in ("failed", "outsider"):
            for activity in ("1", "2"):
                self.db.execute(
                    "INSERT INTO activities(attempt,activity,drv,kind) VALUES(?,?,?,'build')",
                    (aid, activity, self.dep),
                )
        self.db.execute(
            "INSERT INTO tests VALUES('outsider',?,'checkPhase','observed')",
            (self.dep,),
        )
        r = batches(self.db, self.cid)["rows"][0]
        self.assertEqual(r["roots"], ["lib"])
        self.assertEqual(r["names"], ["lib", "libAlias", "slow-sdk-1.2"])
        self.assertEqual((r["builds"], r["tested"]), (1, 0))
        self.db.execute(
            "INSERT INTO tests VALUES('failed',?,'checkPhase','observed')", (self.dep,)
        )
        self.db.execute(
            "INSERT INTO tests VALUES('failed',?,'installCheckPhase','observed')",
            (self.dep,),
        )
        self.db.execute("UPDATE candidates SET state='available'")
        self.db.execute("UPDATE derivations SET available=1")
        r = batches(self.db, self.cid)["rows"][0]
        self.assertEqual(r["outcome"], "error")
        self.assertEqual(r["tested"], 1)

    def test_planning_names_and_read_only_endpoint(self):
        self.attempt(
            "plan", kind="plan", targets=[dict(id=1, attr=["pythonPackages", "foo"])]
        )
        self.db.commit()
        response = []
        raw = b"".join(
            application(self.state)(
                dict(
                    REQUEST_METHOD="GET",
                    PATH_INFO="/api/batches",
                    QUERY_STRING="campaign=" + self.cid,
                ),
                lambda status, headers: response.append(status),
            )
        )
        self.assertEqual(response, ["200 OK"])
        r = json.loads(raw)["rows"][0]
        self.assertEqual(r["roots"], ["pythonPackages.foo"])
        self.assertEqual(r["builds"], 0)
        self.assertNotIn("spec", r)
