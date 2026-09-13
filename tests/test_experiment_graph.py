"""Live graph semantics: scope, output requirements, and observed activity."""

from pathlib import Path
import tempfile
import unittest

from experiment.controller import Controller
from experiment.graph import live_graph
from experiment.model import atomic_json, connect, encode, import_campaign
from experiment.nix import DEFAULT_POLICY

A = "/nix/store/" + "a" * 32 + "-library.drv"
B = "/nix/store/" + "b" * 32 + "-program.drv"
C = "/nix/store/" + "c" * 32 + "-other.drv"
D = "/nix/store/" + "d" * 32 + "-native.drv"
OUT = "/nix/store/" + "e" * 32 + "-library"
DEV = "/nix/store/" + "f" * 32 + "-library-dev"


class LiveGraphTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.state = Path(self.tmp.name)
        self.db = connect(self.state)
        self.cid = import_campaign(
            self.db,
            "graph",
            {"attrPaths": [["program"], ["alias"], ["other"]]},
            "/source",
            "test",
            DEFAULT_POLICY,
            "test",
        )
        for drv, name in ((A, "library"), (B, "program"), (C, "other"), (D, "native")):
            self.db.execute(
                "INSERT INTO derivations(drv,name,outputs) VALUES(?,?,?)",
                (
                    drv,
                    name,
                    encode({"out": OUT, "dev": DEV} if drv == A else {"out": drv[:-4]}),
                ),
            )
        for parent, child, outputs in (
            (B, A, ["dev"]),
            (C, A, ["out"]),
            (A, D, ["out"]),
        ):
            self.db.execute(
                "INSERT INTO edges VALUES(?,?,?)",
                (parent, child, encode({"outputs": outputs, "dynamicOutputs": {}})),
            )
        for label, drv in (("program", B), ("alias", B), ("other", C)):
            self.db.execute(
                "UPDATE candidates SET drv=?,state='queued' WHERE campaign=? AND label=?",
                (drv, self.cid, label),
            )
        self.db.commit()
        self.ctl = Controller(self.db, self.state)

    def tearDown(self):
        self.db.close()
        self.tmp.cleanup()

    def build(self):
        return self.ctl.intent(
            self.ctl.campaign(self.cid),
            "build",
            [B, C],
            derivations=[A, B, C, D],
            output_paths=[OUT, DEV, B[:-4], C[:-4], D[:-4]],
        )

    def view(self, **kw):
        return live_graph(self.db, self.state, self.cid, **kw)

    def test_running_dependency_focus_and_shared_consumers(self):
        aid = self.build()
        self.db.execute(
            "INSERT INTO activities(attempt,activity,drv,kind,phase) VALUES(?,'1',?,'build','buildPhase')",
            (aid, A),
        )
        g = self.view(show_available=True)
        self.assertEqual(g["focus"]["drv"], A)
        self.assertEqual(g["focus"]["state"], "building")
        self.assertEqual(g["selected_dependents"], 3)
        self.assertEqual({n["drv"] for n in g["consumers"]}, {B, C})
        self.assertEqual(
            {(e["source"], e["target"]) for e in g["edges"]}, {(D, A), (A, B), (A, C)}
        )

    def test_required_output_is_enough_for_input_edge(self):
        aid = self.build()
        atomic_json(self.state / "attempts" / aid / "before.json", [DEV])
        g = self.view(focus=B)
        self.assertEqual(g["totals"]["hidden_available"], 1)
        self.assertEqual(g["inputs"], [])
        g = self.view(focus=B, show_available=True)
        self.assertEqual(g["inputs"][0]["state"], "available")
        self.assertEqual(g["inputs"][0]["required_outputs"], ["dev"])
        self.assertEqual(self.view(focus=A)["focus"]["state"], "waiting")
        self.assertEqual(self.db.execute("SELECT count(*) FROM tests").fetchone()[0], 0)

    def test_stop_is_awaiting_result_not_success(self):
        aid = self.build()
        self.db.execute(
            "INSERT INTO activities(attempt,activity,drv,kind,phase,stopped) VALUES(?,'1',?,'build','checkPhase',1)",
            (aid, A),
        )
        self.assertEqual(self.view(focus=A)["focus"]["state"], "settling")

    def test_consumer_phase_supplies_required_inputs_without_test_claim(self):
        aid = self.build()
        self.db.execute(
            "INSERT INTO activities(attempt,activity,drv,kind,phase) VALUES(?,'1',?,'build','configurePhase')",
            (aid, B),
        )
        g = self.view(focus=B, show_available=True)
        self.assertEqual(g["inputs"][0]["state"], "available")
        self.assertEqual(g["inputs"][0]["availability_evidence"], "consumer-phase")
        self.assertEqual(g["inputs"][0]["origin"], "unknown")
        self.assertEqual(self.view(focus=A)["focus"]["state"], "waiting")
        self.assertEqual(self.db.execute("SELECT count(*) FROM tests").fetchone()[0], 0)

    def test_old_cancelled_activity_is_not_live(self):
        aid = self.build()
        self.db.execute(
            "INSERT INTO activities(attempt,activity,drv,kind) VALUES(?,'1',?,'build')",
            (aid, A),
        )
        self.db.execute("UPDATE attempts SET state='finished' WHERE id=?", (aid,))
        self.assertEqual(self.view()["building"], [])
        self.assertEqual(self.view(focus=A)["focus"]["state"], "unknown")

    def test_failure_blocks_consumers(self):
        self.build()
        self.db.execute("UPDATE derivations SET failure='configure' WHERE drv=?", (A,))
        g = self.view(focus=A)
        self.assertEqual(g["focus"]["state"], "failed")
        self.assertEqual({n["state"] for n in g["consumers"]}, {"blocked"})

    def test_other_campaign_consumer_is_excluded(self):
        x = "/nix/store/" + "x" * 32 + "-outside.drv"
        self.db.execute(
            "INSERT INTO derivations(drv,name,outputs) VALUES(?,?,?)",
            (x, "outside", "{}"),
        )
        self.db.execute("INSERT INTO edges VALUES(?,?,?)", (x, A, '["out"]'))
        self.assertNotIn(x, {n["drv"] for n in self.view(focus=A)["consumers"]})
        with self.assertRaises(ValueError):
            self.view(focus=x)

    def test_concurrent_planner_does_not_replace_build_focus(self):
        self.ctl.dispatch({"op": "schedule", "campaign": self.cid, "plan_ahead": 128})
        build = self.build()
        plan = self.ctl.intent(
            self.ctl.campaign(self.cid), "plan", [{"id": 99, "attr": ["next"]}]
        )
        (self.state / "attempts" / plan / "plan.jsonl").write_text("{}\n")
        view = self.view()
        self.assertEqual(view["work"]["kind"], "build")
        self.assertEqual(view["work"]["attempt"], build)
        self.assertEqual(view["planning"], dict(attempt=plan, completed=1, total=1))

    def test_both_build_lanes_keep_live_nodes_and_their_log_owners(self):
        self.ctl.dispatch(
            {
                "op": "schedule",
                "campaign": self.cid,
                "plan_ahead": 128,
                "build_lanes": 2,
            }
        )
        self.db.execute("UPDATE derivations SET available=1 WHERE drv=?", (A,))
        first = self.ctl.build_targets(self.ctl.campaign(self.cid), [B])
        second = self.ctl.build_targets(self.ctl.campaign(self.cid), [C])
        for aid, drv in ((first, B), (second, C)):
            self.db.execute(
                "INSERT INTO activities(attempt,activity,drv,kind,phase) VALUES(?,'1',?,'build','buildPhase')",
                (aid, drv),
            )
        view = self.view(focus=B)
        self.assertEqual({n["drv"] for n in view["building"]}, {B, C})
        self.assertEqual({n["drv"] for n in view["roots"]}, {B, C})
        self.assertEqual(view["focus"]["attempt"], first)
        self.assertEqual(self.view(focus=C)["focus"]["attempt"], second)
        self.db.execute("UPDATE attempts SET state='finished' WHERE id=?", (second,))
        view = self.view(focus=B)
        self.assertEqual(view["batch"]["id"], first)
        self.assertEqual(view["focus"]["state"], "building")
        self.assertEqual({n["drv"] for n in view["building"]}, {B})

    def test_planning_reports_completed_rows_without_build_activity(self):
        aid = self.ctl.intent(
            self.ctl.campaign(self.cid),
            "plan",
            [{"id": 1, "attr": ["program"]}, {"id": 2, "attr": ["alias"]}],
        )
        (self.state / "attempts" / aid / "plan.jsonl").write_text('{}\n{"torn":')
        work = self.view()["work"]
        self.assertEqual(
            (work["kind"], work["completed"], work["total"]), ("plan", 1, 2)
        )

    def test_neighbors_are_paginated(self):
        for i in range(20):
            drv = f"/nix/store/{i:032d}-input.drv"
            self.db.execute(
                "INSERT INTO derivations(drv,name,outputs) VALUES(?,?,?)",
                (drv, f"input-{i:02d}", "{}"),
            )
            self.db.execute("INSERT INTO edges VALUES(?,?,?)", (B, drv, '["out"]'))
        first = self.view(focus=B)
        second = self.view(focus=B, page=1)
        self.assertEqual(len(first["inputs"]), 6)
        self.assertTrue(first["totals"]["more"])
        self.assertTrue(
            {n["drv"] for n in first["inputs"]}.isdisjoint(
                n["drv"] for n in second["inputs"]
            )
        )


if __name__ == "__main__":
    unittest.main()
