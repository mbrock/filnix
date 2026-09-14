"""Recovery and evidence invariants, independent of a running Nix daemon."""

import json
from pathlib import Path
import subprocess
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

    def scheduling(self, **settings):
        return self.controller.dispatch(
            {"op": "schedule", "campaign": self.cid, **settings}
        )

    def test_schedule_is_audited_without_rewriting_active_attempt(self):
        aid = self.attempt("build")
        before = self.sql("SELECT spec FROM attempts WHERE id=?", (aid,)).fetchone()[0]
        self.scheduling(batch_size=32, plan_ahead=128)
        self.assertEqual(
            self.sql("SELECT spec FROM attempts WHERE id=?", (aid,)).fetchone()[0],
            before,
        )
        policy = json.loads(self.controller.campaign(self.cid)["policy"])
        self.assertEqual(policy["max_jobs"], 4)
        self.assertEqual(policy["cores"], 6)
        record = json.loads(
            self.sql(
                "SELECT payload FROM events WHERE kind='scheduling-updated'"
            ).fetchone()[0]
        )
        self.assertEqual(
            record["before"], {"batch_size": 8, "plan_ahead": 0, "build_lanes": 1}
        )
        self.assertEqual(
            record["after"], {"batch_size": 32, "plan_ahead": 128, "build_lanes": 1}
        )
        self.assertEqual(self.controller.campaign(self.cid)["mode"], "paused")
        with self.assertRaises(ValueError):
            self.scheduling(batch_size=64, plan_ahead=257)
        self.assertEqual(self.scheduling(), record["after"])

    def test_serial_policy_and_kind_limits(self):
        self.attempt("build")
        with self.assertRaises(ValueError):
            self.attempt("plan")
        self.scheduling(plan_ahead=128)
        self.attempt("plan")
        for kind in ("build", "plan"):
            with self.assertRaises(ValueError):
                self.attempt(kind)

    def test_other_campaign_cannot_take_spare_lane(self):
        self.scheduling(plan_ahead=128)
        self.attempt("build")
        other = import_campaign(
            self.db,
            "other",
            {"attrPaths": [["x"]]},
            "/source",
            "abc",
            dict(nix.DEFAULT_POLICY, plan_ahead=128),
            "test",
        )
        with self.assertRaises(ValueError):
            self.controller.plan(other, [4])

    def test_overlap_recovers_without_duplicate_launch(self):
        self.scheduling(plan_ahead=128)
        build = self.attempt("build")
        plan = self.attempt("plan")
        self.controller.reconcile()
        Controller(self.db, self.state, self.units).reconcile()
        self.assertEqual(self.units.starts, [build, plan])
        self.assertEqual(len(self.controller.active_attempts()), 2)

    def test_cancel_planner_leaves_build_running_and_pauses_admission(self):
        self.scheduling(plan_ahead=128)
        build = self.attempt("build")
        plan = self.attempt("plan")
        self.controller.reconcile()
        atomic_json(self.folder(plan) / "started.json", {"pid": 42})
        self.controller.dispatch({"op": "cancel", "attempt": plan})
        self.controller.tick()
        self.assertTrue(self.units.active(build))
        self.assertEqual(self.units.starts, [build, plan])
        self.assertEqual(self.controller.campaign(self.cid)["mode"], "paused")
        self.assertEqual(
            self.sql("SELECT state FROM attempts WHERE id=?", (plan,)).fetchone()[0],
            "finished",
        )

    def test_pause_drains_both_lanes_without_new_admission(self):
        self.scheduling(plan_ahead=128)
        build = self.attempt("build")
        plan = self.attempt("plan")
        self.controller.reconcile()
        self.controller.dispatch({"op": "pause", "campaign": self.cid})
        self.controller.tick()
        self.assertEqual(self.units.live, {build, plan})
        self.assertEqual(self.units.starts, [build, plan])

    def test_plan_ahead_while_build_is_active(self):
        self.scheduling(plan_ahead=128)
        build = self.attempt("build")
        with patch.object(self.controller, "admission_reason", return_value=""):
            self.controller.admit(self.controller.campaign(self.cid))
        active = self.controller.active_attempts()
        self.assertEqual([r["kind"] for r in active], ["build", "plan"])
        self.assertEqual(active[0]["id"], build)
        self.assertEqual(len(json.loads(active[1]["targets"])), 3)

    def test_memory_pressure_blocks_planning_ahead(self):
        self.scheduling(plan_ahead=128)
        build = self.attempt("build")
        with patch.object(
            self.controller, "admission_reason", return_value="memory pressure"
        ):
            self.controller.admit(self.controller.campaign(self.cid))
        self.assertEqual([r["id"] for r in self.controller.active_attempts()], [build])
        self.assertEqual(self.controller.campaign(self.cid)["hold"], "memory pressure")

    def test_ready_buffer_is_counted_by_derivation_and_bounded(self):
        self.graph()  # Three attributes, two distinct ready derivations.
        with self.db:
            self.sql(
                "INSERT INTO candidates(campaign,attr,label,selection) VALUES(?,?,?,?)",
                (self.cid, '["extra"]', "extra", "{}"),
            )
        self.scheduling(plan_ahead=1)
        self.attempt("build")  # Marks A running, leaves two aliases of B queued.
        with patch.object(self.controller, "admission_reason", return_value=""):
            self.controller.admit(self.controller.campaign(self.cid))
            self.assertEqual(len(self.controller.active_attempts()), 1)
            self.scheduling(plan_ahead=2)
            self.controller.admit(self.controller.campaign(self.cid))
        plan = self.sql("SELECT targets FROM attempts WHERE kind='plan'").fetchone()
        self.assertEqual(len(json.loads(plan[0])), 1)

    def test_larger_batch_deduplicates_roots_and_overlaps_planner(self):
        self.scheduling(batch_size=32, plan_ahead=128)
        with self.db:
            self.sql("DELETE FROM candidates")
            for i in range(40):
                drv = f"/nix/store/{i:032x}-package.drv"
                self.sql(
                    "INSERT INTO derivations(drv,name,outputs) VALUES(?,?,?)",
                    (drv, str(i), "{}"),
                )
                for alias in ("a", "b"):
                    self.sql(
                        "INSERT INTO candidates(campaign,attr,label,selection,state,drv) VALUES(?,?,?,?,'queued',?)",
                        (
                            self.cid,
                            encode([str(i), alias]),
                            f"{i:02}-{alias}",
                            "{}",
                            drv,
                        ),
                    )
            self.sql(
                "INSERT INTO candidates(campaign,attr,label,selection) VALUES(?,?,?,?)",
                (self.cid, '["extra"]', "extra", "{}"),
            )
        with patch.object(self.controller, "admission_reason", return_value=""):
            self.controller.admit(self.controller.campaign(self.cid))
        build, plan = self.controller.active_attempts()
        self.assertEqual((build["kind"], plan["kind"]), ("build", "plan"))
        targets = json.loads(build["targets"])
        self.assertEqual(len(targets), 32)
        self.assertEqual(len(set(targets)), 32)
        self.assertEqual(
            self.sql(
                "SELECT count(*) FROM candidates WHERE state='running'"
            ).fetchone()[0],
            64,
        )

    def test_kernel_builder_is_excluded_even_as_a_renamed_dependency(self):
        self.graph()
        nix.add_graph(
            self.db,
            {
                A: {
                    "env": {
                        "buildFlags": "KBUILD_BUILD_VERSION=1-NixOS bzImage vmlinux modules"
                    },
                    "outputs": {"out": {"path": OUTPUT}},
                    "inputDrvs": {},
                }
            },
        )
        refresh_candidates(self.db, self.cid)
        self.assertEqual(
            [r[0] for r in self.sql("SELECT state FROM candidates ORDER BY id")],
            ["excluded"] * 3,
        )
        self.db.commit()
        with self.assertRaisesRegex(ValueError, "excluded"):
            self.controller.build_targets(self.controller.campaign(self.cid), [B])
        with self.assertRaises(ValueError):
            self.controller.dispatch({"op": "retry", "campaign": self.cid, "ids": [1]})
        with self.assertRaises(ValueError):
            self.controller.dispatch(
                {"op": "retry-derivation", "campaign": self.cid, "drv": A}
            )
        self.sql("UPDATE candidates SET state='queued' WHERE id=1")
        with self.assertRaises(ValueError):
            self.controller.intent(self.controller.campaign(self.cid), "build", [A])

    def test_kernel_exclusion_keeps_outputs_and_checks_without_claiming_success(self):
        self.graph()
        self.sql(
            "UPDATE derivations SET available=1,origin='local',exclusion='kernel' WHERE drv=?",
            (A,),
        )
        self.sql("INSERT INTO tests VALUES('old',?,'checkPhase','observed')", (A,))
        refresh_candidates(self.db, self.cid)
        self.assertEqual(
            self.sql("SELECT state FROM candidates WHERE id=1").fetchone()[0],
            "excluded",
        )
        self.assertEqual(
            self.sql("SELECT available FROM derivations WHERE drv=?", (A,)).fetchone()[
                0
            ],
            1,
        )
        self.assertEqual(self.sql("SELECT count(*) FROM tests").fetchone()[0], 1)

    def test_explicit_kernel_stop_requeues_only_its_collateral(self):
        from experiment.scope import REASON

        self.lane_graph()
        self.sql(
            "UPDATE candidates SET selection=? WHERE id=1",
            (
                encode(
                    {
                        "metadata": {"pname": "linux-hardened"},
                        "sourceFile": "pkgs/top-level/linux-kernels.nix",
                    }
                ),
            ),
        )
        aid = self.controller.build_targets(self.controller.campaign(self.cid), [A, C])
        original_spec = (self.folder(aid) / "spec.json").read_bytes()
        self.finish(aid, "cancelled")
        with patch("experiment.nix.valid", return_value=set()):
            self.controller.reconcile()
        self.sql(
            "UPDATE candidates SET state='inconclusive',error='timeout' WHERE id=2"
        )
        definition = {
            A: {
                "env": {"buildFlags": "KBUILD_BUILD_VERSION=1 vmlinux"},
                "outputs": {"out": {"path": A[:-4]}},
                "inputDrvs": {},
            }
        }
        with patch("experiment.nix.query", return_value=definition):
            report = self.controller.dispatch(
                {"op": "exclude-kernels", "campaign": self.cid, "attempt": aid}
            )
        self.assertEqual(len(report["excluded"]), 1)
        self.assertEqual(
            [r[0] for r in self.sql("SELECT state FROM candidates ORDER BY id")],
            ["excluded", "inconclusive", "queued"],
        )
        result = json.loads(
            self.sql("SELECT result FROM attempts WHERE id=?", (aid,)).fetchone()[0]
        )
        self.assertEqual(
            (result["reason"], result["worker_reason"]), ("excluded", "cancelled")
        )
        self.assertEqual(result["error"], REASON)
        self.assertEqual((self.folder(aid) / "spec.json").read_bytes(), original_spec)
        self.assertEqual(
            json.loads((self.folder(aid) / "exit.json").read_text())["reason"],
            "cancelled",
        )
        self.assertEqual(
            self.sql(
                "SELECT count(*) FROM events WHERE kind='kernels-excluded'"
            ).fetchone()[0],
            1,
        )

    def test_headers_and_userspace_are_not_kernel_builders(self):
        from experiment.scope import kernel_derivation

        for flags in ("headers_install", "modules", "", "vmlinux"):
            self.assertFalse(kernel_derivation({"env": {"buildFlags": flags}}))

    def test_kernel_selection_is_excluded_before_evaluation(self):
        cid = import_campaign(
            self.db,
            "scope",
            {"attrPaths": [["linux_hardened"]]},
            "/source",
            "rev",
            nix.DEFAULT_POLICY,
            "test",
            [{"attrPath": ["linux_hardened"], "metadata": {"isLinuxKernel": True}}],
        )
        row = self.sql(
            "SELECT id,state FROM candidates WHERE campaign=?", (cid,)
        ).fetchone()
        self.assertEqual(row["state"], "excluded")
        with self.assertRaises(ValueError):
            self.controller.plan(cid, [row["id"]])
        refresh_candidates(self.db, cid)
        self.assertEqual(
            self.sql(
                "SELECT state FROM candidates WHERE campaign=?", (cid,)
            ).fetchone()[0],
            "excluded",
        )

    def test_schema_one_migrates_without_losing_facts(self):
        self.graph()
        self.db.commit()
        self.db.execute("ALTER TABLE derivations DROP COLUMN exclusion")
        self.db.execute("PRAGMA user_version=1")
        self.db.close()
        self.db = connect(self.state)
        self.assertEqual(self.db.execute("PRAGMA user_version").fetchone()[0], 4)
        self.assertEqual(self.sql("SELECT count(*) FROM derivations").fetchone()[0], 3)
        self.assertIsNone(
            self.sql("SELECT exclusion FROM derivations LIMIT 1").fetchone()[0]
        )

    def lane_graph(self):
        self.graph()
        self.sql("DELETE FROM edges WHERE parent=?", (C,))
        for drv in (A, B, C):
            self.sql(
                "UPDATE derivations SET outputs=? WHERE drv=?",
                (encode({"out": drv[:-4]}), drv),
            )
        self.sql("UPDATE candidates SET drv=? WHERE id=3", (C,))
        self.db.commit()

    def test_second_lane_skips_dependency_owner_and_preserves_legacy_limits(self):
        self.lane_graph()
        first = self.controller.build_targets(self.controller.campaign(self.cid), [A])
        original = (self.folder(first) / "spec.json").read_bytes()
        self.scheduling(build_lanes=2, plan_ahead=128)
        with patch.object(self.controller, "admission_reason", return_value=""):
            self.controller.admit(self.controller.campaign(self.cid))
        active = self.controller.active_attempts()
        self.assertEqual(len(active), 2)
        self.assertEqual(json.loads(active[1]["targets"]), [C])
        policy = json.loads(active[1]["spec"])["policy"]
        self.assertEqual((policy["max_jobs"], policy["cores"]), (1, 4))
        self.assertEqual((self.folder(first) / "spec.json").read_bytes(), original)
        with self.assertRaises(ValueError):
            self.controller.build_targets(self.controller.campaign(self.cid), [B])
        self.controller.reconcile()
        Controller(self.db, self.state, self.units).reconcile()
        self.assertEqual(self.units.starts, [r["id"] for r in active])

    def test_lanes_split_jobs_and_reject_shared_missing_dependency(self):
        self.lane_graph()
        self.scheduling(build_lanes=2, plan_ahead=128)
        self.controller.build_targets(self.controller.campaign(self.cid), [B])
        with self.assertRaisesRegex(ValueError, "dependencies"):
            self.controller.build_targets(self.controller.campaign(self.cid), [A])
        self.controller.build_targets(self.controller.campaign(self.cid), [C])
        policies = [
            json.loads(r["spec"])["policy"] for r in self.controller.active_attempts()
        ]
        self.assertEqual(
            [(p["max_jobs"], p["cores"]) for p in policies], [(2, 6), (2, 6)]
        )

    def test_cached_dependency_can_be_shared_without_erasing_its_evidence(self):
        self.lane_graph()
        self.sql("INSERT INTO edges VALUES(?,?,?)", (C, A, '["out"]'))
        self.sql(
            "UPDATE derivations SET available=1,origin='local',evidence_attempt='original' WHERE drv=?",
            (A,),
        )
        self.scheduling(build_lanes=2, plan_ahead=128)
        first = self.controller.build_targets(self.controller.campaign(self.cid), [B])
        second = self.controller.build_targets(self.controller.campaign(self.cid), [C])
        atomic_json(self.folder(second) / "before.json", [A[:-4]])
        self.finish(second)
        with patch("experiment.nix.valid", return_value={A[:-4], C[:-4]}):
            self.controller.reconcile()
        self.assertEqual(
            self.sql("SELECT state FROM candidates WHERE drv=?", (B,)).fetchone()[0],
            "running",
        )
        self.assertEqual(
            self.sql("SELECT state FROM candidates WHERE drv=?", (C,)).fetchone()[0],
            "available",
        )
        self.assertEqual(
            self.sql(
                "SELECT evidence_attempt FROM derivations WHERE drv=?", (A,)
            ).fetchone()[0],
            "original",
        )
        self.assertTrue(self.units.active(first))
        self.assertEqual(self.sql("SELECT count(*) FROM tests").fetchone()[0], 0)

    def test_cancel_one_build_leaves_other_running(self):
        self.lane_graph()
        self.scheduling(build_lanes=2, plan_ahead=128)
        first = self.controller.build_targets(self.controller.campaign(self.cid), [B])
        second = self.controller.build_targets(self.controller.campaign(self.cid), [C])
        self.controller.reconcile()
        atomic_json(self.folder(second) / "started.json", {"pid": 42})
        self.controller.dispatch({"op": "cancel", "attempt": second})
        with patch("experiment.nix.valid", return_value=set()):
            self.controller.tick()
        self.assertTrue(self.units.active(first))
        self.assertEqual(
            self.sql("SELECT state FROM candidates WHERE drv=?", (B,)).fetchone()[0],
            "running",
        )
        self.assertEqual(
            self.sql("SELECT state FROM candidates WHERE drv=?", (C,)).fetchone()[0],
            "inconclusive",
        )
        self.assertEqual(self.controller.campaign(self.cid)["mode"], "paused")

    def test_requested_cpu_budget_never_uses_observed_idle_slots(self):
        from experiment.scheduling import build_policy

        policy = dict(nix.DEFAULT_POLICY, build_lanes=2, plan_ahead=128, cpus="0-23")
        legacy = {"spec": encode({"policy": nix.DEFAULT_POLICY})}
        self.assertIsNone(build_policy(policy, [legacy]))
        policy["cpus"] = "0-27"
        self.assertEqual(build_policy(policy, [legacy])["cores"], 4)
        with self.assertRaises(ValueError):
            self.scheduling(build_lanes=3)

    def test_cached_required_output_prunes_unbuilt_ancestors(self):
        from experiment.scheduling import BuildGraph

        self.lane_graph()
        self.sql(
            "UPDATE derivations SET outputs=? WHERE drv=?",
            (encode({"out": A[:-4], "dev": OUTPUT}), A),
        )
        self.sql("UPDATE edges SET outputs=? WHERE parent=?", ('["dev"]', B))
        self.sql("INSERT INTO edges VALUES(?,?,?)", (A, C, '["out"]'))
        graph = BuildGraph(self.db)
        self.assertEqual(graph.needed([B], {OUTPUT}), {B})
        self.assertEqual(graph.needed([B], set()), {A, B, C})
        self.assertEqual(graph.needed([B], {OUTPUT}, held={A}), {A, B, C})

    def plan_record(self, aid, target, drv):
        graph_file = f"graph-{target}.json"
        atomic_json(
            self.folder(aid) / graph_file,
            {drv: {"outputs": {"out": {"path": OUTPUT}}, "inputDrvs": {}}},
        )
        with (self.folder(aid) / "plan.jsonl").open("a") as f:
            f.write(
                encode(
                    {
                        "id": target,
                        "recipe": {"drv": drv, "roles": []},
                        "graph": graph_file,
                    }
                )
                + "\n"
            )

    def test_plan_completion_reuses_facts_and_preserves_live_aliases(self):
        self.graph()
        with self.db:
            self.sql(
                "UPDATE candidates SET drv=NULL,state='unplanned' WHERE id IN (2,3)"
            )
        self.scheduling(plan_ahead=128)
        build = self.attempt("build")
        plan = self.controller.plan(self.cid, [2, 3])
        self.plan_record(plan, 2, A)  # Alias of a root already being built.
        self.plan_record(plan, 3, C)  # Blocked by a previously failed dependency.
        self.sql("UPDATE derivations SET failure='configure' WHERE drv=?", (B,))
        self.sql("INSERT INTO edges VALUES(?,?,?)", (C, B, '["out"]'))
        self.db.commit()
        self.finish(plan)
        self.controller.reconcile()
        self.assertEqual(
            [r[0] for r in self.sql("SELECT state FROM candidates ORDER BY id")],
            ["running", "running", "blocked"],
        )
        self.assertTrue(self.units.active(build))
        self.assertEqual(self.sql("SELECT count(*) FROM tests").fetchone()[0], 0)

    def test_targeted_revision_preserves_other_failures_and_historical_attempts(self):
        source = "/nix/store/" + "e" * 32 + "-filnix-campaign-source"
        revision = "f" * 40
        old = self.controller.plan(self.cid, [1, 2])
        (self.folder(old) / "plan.jsonl").write_text(
            encode({"id": 1, "error": "old exclusion"})
            + "\n"
            + encode({"id": 2, "error": "downstream exclusion"})
            + "\n"
        )
        self.finish(old)
        self.controller.reconcile()
        history = dict(self.sql("SELECT * FROM attempts WHERE id=?", (old,)).fetchone())
        campaign = dict(self.controller.campaign(self.cid))
        untouched = dict(self.sql("SELECT * FROM candidates WHERE id=2").fetchone())
        with patch("experiment.controller.Path.is_file", return_value=True):
            new = self.controller.dispatch(
                dict(
                    op="plan",
                    campaign=self.cid,
                    ids=[1],
                    source=source,
                    revision=revision,
                )
            )
        spec = json.loads((self.folder(new) / "spec.json").read_text())
        self.assertEqual((spec["source"], spec["revision"]), (source, revision))
        self.assertEqual(spec["previous_candidates"][0]["error"], "old exclusion")
        self.assertEqual(len(spec["previous_candidates"]), 1)
        self.plan_record(new, 1, A)
        self.finish(new)
        Controller(self.db, self.state, self.units).reconcile()
        self.assertEqual(dict(self.controller.campaign(self.cid)), campaign)
        self.assertEqual(
            dict(self.sql("SELECT * FROM attempts WHERE id=?", (old,)).fetchone()),
            history,
        )
        self.assertEqual(
            dict(self.sql("SELECT * FROM candidates WHERE id=2").fetchone()), untouched
        )
        row = self.sql("SELECT state,recipe FROM candidates WHERE id=1").fetchone()
        recipe = json.loads(row["recipe"])
        self.assertEqual(row["state"], "queued")
        self.assertEqual(
            (recipe["source"], recipe["revision"], recipe["plan_attempt"]),
            (source, revision, new),
        )
        # Fixed derivations from both revisions can share a resource-bounded batch.
        with self.db:
            self.sql(
                "INSERT INTO derivations(drv,name,outputs) VALUES(?,?,?)", (B, B, "{}")
            )
            self.sql("UPDATE candidates SET drv=?,state='queued' WHERE id=3", (B,))
        build = self.controller.build_targets(
            self.controller.campaign(self.cid), [A, B]
        )
        spec = json.loads((self.folder(build) / "spec.json").read_text())
        self.assertEqual(
            spec["recipe_sources"][A], [dict(source=source, revision=revision)]
        )
        self.assertEqual(
            spec["recipe_sources"][B],
            [dict(source=campaign["source"], revision=campaign["revision"])],
        )

    def test_revision_plan_rejects_mutable_sources_and_successful_candidates(self):
        for source, revision in (
            ("/home/worktree", "f" * 40),
            ("/nix/store/source", None),
        ):
            with self.assertRaisesRegex(ValueError, "frozen committed flake"):
                self.controller.plan(self.cid, [1], source, revision)
        with self.assertRaises(ValueError):
            self.controller.plan(self.cid, [1, 1])
        self.graph()
        self.sql("UPDATE candidates SET state='available' WHERE id=1")
        source = "/nix/store/" + "e" * 32 + "-filnix-campaign-source"
        with patch("experiment.controller.Path.is_file", return_value=True):
            with self.assertRaisesRegex(ValueError, "already planned"):
                self.controller.plan(self.cid, [1], source, "f" * 40)
        self.assertEqual(self.sql("SELECT count(*) FROM attempts").fetchone()[0], 0)

    def test_revision_detaches_queued_recipe_before_admission(self):
        self.graph()
        previous = dict(self.sql("SELECT * FROM candidates WHERE id=1").fetchone())
        source = "/nix/store/" + "e" * 32 + "-filnix-campaign-source"
        with self.assertRaisesRegex(ValueError, "already planned"):
            self.controller.plan(self.cid, [1])
        with patch("experiment.controller.Path.is_file", return_value=True):
            aid = self.controller.plan(self.cid, [1], source, "f" * 40)
        spec = json.loads((self.folder(aid) / "spec.json").read_text())
        self.assertEqual(spec["previous_candidates"][0]["drv"], previous["drv"])
        self.assertEqual(spec["previous_candidates"][0]["state"], "queued")
        Controller(self.db, self.state, self.units).reconcile()
        refresh_candidates(self.db, self.cid)
        self.assertEqual(
            tuple(self.sql("SELECT drv,state FROM candidates WHERE id=1").fetchone()),
            (None, "unplanned"),
        )

    def test_revision_replaces_failed_recipe_without_requeueing_old_build(self):
        self.graph()
        self.sql("UPDATE derivations SET failure='compile' WHERE drv=?", (A,))
        self.sql("UPDATE candidates SET recipe=? WHERE id=1", (encode({"drv": A}),))
        refresh_candidates(self.db, self.cid)
        self.db.commit()
        source = "/nix/store/" + "e" * 32 + "-filnix-campaign-source"
        with patch("experiment.controller.Path.is_file", return_value=True):
            new = self.controller.plan(self.cid, [1], source, "f" * 40)
        spec = json.loads((self.folder(new) / "spec.json").read_text())
        previous = spec["previous_candidates"][0]
        self.assertEqual((previous["drv"], previous["state"]), (A, "failed"))
        self.assertEqual(json.loads(previous["recipe"]), {"drv": A})
        # Reconciliation/restart cannot resurrect the old recipe while planning.
        Controller(self.db, self.state, self.units).reconcile()
        refresh_candidates(self.db, self.cid)
        pending = self.sql(
            "SELECT drv,recipe,state FROM candidates WHERE id=1"
        ).fetchone()
        self.assertEqual(tuple(pending), (None, None, "unplanned"))
        self.assertEqual(
            self.sql("SELECT state FROM candidates WHERE id=2").fetchone()[0], "blocked"
        )
        self.plan_record(new, 1, C)
        self.finish(new)
        self.controller.reconcile()
        self.assertEqual(
            self.sql("SELECT drv FROM candidates WHERE id=1").fetchone()[0], C
        )
        self.assertEqual(
            self.sql("SELECT failure FROM derivations WHERE drv=?", (A,)).fetchone()[0],
            "compile",
        )

    def test_failed_revision_evaluation_does_not_restore_old_blocked_recipe(self):
        self.graph()
        self.sql("UPDATE derivations SET failure='compile' WHERE drv=?", (A,))
        refresh_candidates(self.db, self.cid)
        self.db.commit()
        source = "/nix/store/" + "e" * 32 + "-filnix-campaign-source"
        with patch("experiment.controller.Path.is_file", return_value=True):
            new = self.controller.plan(self.cid, [2], source, "f" * 40)
        (self.folder(new) / "plan.jsonl").write_text(
            encode({"id": 2, "error": "new error"}) + "\n"
        )
        self.finish(new)
        self.controller.reconcile()
        self.assertEqual(
            tuple(
                self.sql("SELECT drv,state,error FROM candidates WHERE id=2").fetchone()
            ),
            (None, "evaluation-error", "new error"),
        )

    def test_revision_refuses_dependency_owned_by_active_build(self):
        self.graph()
        build = self.controller.build_targets(self.controller.campaign(self.cid), [B])
        self.sql("UPDATE candidates SET state='queued' WHERE id=1")
        self.db.commit()
        previous = dict(self.sql("SELECT * FROM candidates WHERE id=1").fetchone())
        source = "/nix/store/" + "e" * 32 + "-filnix-campaign-source"
        with patch("experiment.controller.Path.is_file", return_value=True):
            with self.assertRaisesRegex(ValueError, "active build"):
                self.controller.plan(self.cid, [1], source, "f" * 40)
        self.assertEqual(
            dict(self.sql("SELECT * FROM candidates WHERE id=1").fetchone()), previous
        )
        self.assertEqual(len(self.controller.active_attempts()), 1)
        self.assertEqual(self.controller.active_attempts()[0]["id"], build)

    def test_source_snapshot_excludes_worktree_edits(self):
        from experiment.__main__ import committed_source

        repo = self.state / "repo"
        repo.mkdir()

        def git(*args):
            return subprocess.check_output(
                ["git", "-C", str(repo), *args], text=True
            ).strip()

        git("init", "-q")
        (repo / "flake.nix").write_text("committed")
        (repo / "flake.lock").write_text("{}")
        git("add", ".")
        git(
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@example.invalid",
            "-c",
            "core.hooksPath=/dev/null",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "-qm",
            "source",
        )
        revision = git("rev-parse", "HEAD")
        (repo / "flake.nix").write_text("uncommitted")
        (repo / "untracked").write_text("not included")
        original = subprocess.check_output
        source = "/nix/store/" + "e" * 32 + "-filnix-campaign-source"

        def execute(command, **kwargs):
            if command[0] == "git":
                return original(command, **kwargs)
            snapshot = Path(command[-1])
            self.assertEqual((snapshot / "flake.nix").read_text(), "committed")
            self.assertFalse((snapshot / "untracked").exists())
            self.assertIn("add-path", command)
            return source + "\n"

        with patch("experiment.__main__.subprocess.check_output", side_effect=execute):
            self.assertEqual(committed_source(str(repo), "HEAD"), (source, revision))

    def queue_replan(self, ids, revision="f" * 40):
        with patch("experiment.controller.Path.is_file", return_value=True):
            return self.controller.dispatch(
                dict(
                    op="queue-replan",
                    campaign=self.cid,
                    ids=ids,
                    source="/nix/store/" + "e" * 32 + "-filnix-campaign-source",
                    revision=revision,
                )
            )

    def evaluation_errors(self):
        with self.db:
            self.sql(
                "UPDATE candidates SET state='evaluation-error',error='old exclusion'"
            )

    def test_replan_queue_survives_restart_and_respects_pause(self):
        self.evaluation_errors()
        old = [dict(r) for r in self.sql("SELECT * FROM candidates")]
        campaign = dict(self.controller.campaign(self.cid))
        queued = self.queue_replan([1, 2])
        self.assertEqual(queued["queued"], 2)
        self.assertEqual([dict(r) for r in self.sql("SELECT * FROM candidates")], old)
        self.assertEqual(dict(self.controller.campaign(self.cid)), campaign)
        self.db.close()
        self.db = connect(self.state)
        self.controller = Controller(self.db, self.state, self.units)
        self.controller.tick()
        self.assertEqual(self.sql("SELECT count(*) FROM replans").fetchone()[0], 2)
        self.assertFalse(self.controller.active_attempts())
        self.controller.dispatch(dict(op="run", campaign=self.cid))
        with patch.object(self.controller, "admission_reason", return_value=""), patch(
            "experiment.controller.Path.is_file", return_value=True
        ):
            self.controller.tick()
        attempt = self.controller.active_attempts()[0]
        spec = json.loads(attempt["spec"])
        self.assertEqual(spec["revision"], "f" * 40)
        self.assertEqual([r["id"] for r in spec["previous_candidates"]], [1, 2])
        self.assertTrue(
            all(r["error"] == "old exclusion" for r in spec["previous_candidates"])
        )
        self.assertEqual(spec["replan_requests"][0]["request"], queued["request"])
        self.assertEqual(self.sql("SELECT count(*) FROM replans").fetchone()[0], 0)
        self.assertEqual(
            self.sql("SELECT error FROM candidates WHERE id=3").fetchone()[0],
            "old exclusion",
        )

    def test_replan_queue_failure_is_not_automatically_retried(self):
        self.evaluation_errors()
        self.queue_replan([1])
        with patch.object(self.controller, "admission_reason", return_value=""), patch(
            "experiment.controller.Path.is_file", return_value=True
        ):
            self.controller.admit(self.controller.campaign(self.cid))
            aid = self.controller.active_attempts()[0]["id"]
            (self.folder(aid) / "plan.jsonl").write_text(
                encode({"id": 1, "error": "new failure"}) + "\n"
            )
            self.finish(aid)
            self.controller.reconcile()
            self.controller.admit(self.controller.campaign(self.cid))
        self.assertFalse(self.controller.active_attempts())
        self.assertEqual(self.sql("SELECT count(*) FROM attempts").fetchone()[0], 1)
        self.assertEqual(
            self.sql("SELECT error FROM candidates WHERE id=1").fetchone()[0],
            "new failure",
        )

    def test_replan_queue_validates_whole_request_and_deduplicates(self):
        self.evaluation_errors()
        for ids in ([1, 1], [1, 999], [1, True]):
            with self.assertRaises(ValueError):
                self.queue_replan(ids)
        for state in (
            "unplanned",
            "available",
            "excluded",
            "running",
            "queued",
            "blocked",
        ):
            with self.db:
                self.sql("UPDATE candidates SET state=? WHERE id=2", (state,))
            with self.assertRaisesRegex(ValueError, "inactive evaluation failure"):
                self.queue_replan([1, 2])
        self.assertEqual(self.sql("SELECT count(*) FROM replans").fetchone()[0], 0)
        self.queue_replan([1])
        self.assertEqual(self.queue_replan([1])["already_queued"], 1)
        with self.assertRaisesRegex(ValueError, "different revision"):
            self.queue_replan([3, 1], "a" * 40)
        self.assertEqual(self.sql("SELECT count(*) FROM replans").fetchone()[0], 1)
        self.assertEqual(
            self.sql(
                "SELECT count(*) FROM events WHERE kind='replan-queued'"
            ).fetchone()[0],
            1,
        )

    def test_replan_queue_refuses_active_evaluation_and_mutable_source(self):
        self.evaluation_errors()
        self.controller.plan(self.cid, [1])
        with self.assertRaisesRegex(ValueError, "inactive evaluation failure"):
            self.queue_replan([1])
        with self.assertRaisesRegex(ValueError, "frozen committed flake"):
            self.controller.queue_replan(self.cid, [2], "/home/worktree", "f" * 40)

    def test_replan_queue_respects_resource_and_ready_buffer_limits(self):
        self.graph()
        with self.db:
            self.sql(
                "UPDATE candidates SET drv=NULL,state='evaluation-error' WHERE id=3"
            )
        self.queue_replan([3])
        self.scheduling(plan_ahead=1)
        build = self.attempt("build")  # B fills the single ready slot.
        with patch.object(self.controller, "admission_reason", return_value=""):
            self.controller.admit(self.controller.campaign(self.cid))
        self.assertEqual(len(self.controller.active_attempts()), 1)
        self.scheduling(plan_ahead=128)
        with patch.object(
            self.controller, "admission_reason", return_value="memory pressure"
        ):
            self.controller.admit(self.controller.campaign(self.cid))
        self.assertEqual(len(self.controller.active_attempts()), 1)
        with patch.object(self.controller, "admission_reason", return_value=""), patch(
            "experiment.controller.Path.is_file", return_value=True
        ):
            self.controller.admit(self.controller.campaign(self.cid))
        active = self.controller.active_attempts()
        self.assertEqual([r["kind"] for r in active], ["build", "plan"])
        self.assertEqual(active[0]["id"], build)
        self.assertEqual(json.loads(active[1]["targets"])[0]["id"], 3)

    def test_large_replan_queue_uses_bounded_revision_batches(self):
        self.evaluation_errors()
        with self.db:
            self.db.executemany(
                "INSERT INTO candidates(id,campaign,attr,label,selection,state) VALUES(?,?,?,?,?,'evaluation-error')",
                [(i, self.cid, encode([str(i)]), str(i), "{}") for i in range(4, 1004)],
            )
        self.queue_replan(list(range(1, 1004)))
        with patch.object(self.controller, "admission_reason", return_value=""), patch(
            "experiment.controller.Path.is_file", return_value=True
        ):
            self.controller.admit(self.controller.campaign(self.cid))
        spec = json.loads(self.controller.active_attempts()[0]["spec"])
        self.assertEqual(len(spec["targets"]), 32)
        self.assertEqual(self.sql("SELECT count(*) FROM replans").fetchone()[0], 971)

    def test_replan_queue_and_attempt_commit_atomically(self):
        self.evaluation_errors()
        self.queue_replan([1])
        # Fail after intent insertion, candidate detachment and queue consumption.
        with patch.object(self.controller, "admission_reason", return_value=""), patch(
            "experiment.controller.Path.is_file", return_value=True
        ), patch("experiment.controller.event", side_effect=RuntimeError("crash")):
            with self.assertRaisesRegex(RuntimeError, "crash"):
                self.controller.admit(self.controller.campaign(self.cid))
        self.assertEqual(self.sql("SELECT count(*) FROM replans").fetchone()[0], 1)
        self.assertEqual(self.sql("SELECT count(*) FROM attempts").fetchone()[0], 0)
        self.assertEqual(
            self.sql("SELECT error FROM candidates WHERE id=1").fetchone()[0],
            "old exclusion",
        )
        with patch.object(self.controller, "admission_reason", return_value=""), patch(
            "experiment.controller.Path.is_file", return_value=True
        ):
            self.controller.admit(self.controller.campaign(self.cid))
        self.assertEqual(self.sql("SELECT count(*) FROM replans").fetchone()[0], 0)
        self.controller.reconcile()
        self.controller.reconcile()
        self.assertEqual(len(self.units.starts), 1)

    def test_replan_queue_keeps_revisions_separate(self):
        self.evaluation_errors()
        self.queue_replan([1], "a" * 40)
        self.queue_replan([2, 3], "b" * 40)
        with patch.object(self.controller, "admission_reason", return_value=""), patch(
            "experiment.controller.Path.is_file", return_value=True
        ):
            self.controller.admit(self.controller.campaign(self.cid))
            first = self.controller.active_attempts()[0]
            self.assertEqual(json.loads(first["spec"])["revision"], "a" * 40)
            self.assertEqual(len(json.loads(first["targets"])), 1)
            self.finish(first["id"])
            self.controller.reconcile()
            self.controller.admit(self.controller.campaign(self.cid))
        second = self.controller.active_attempts()[0]
        self.assertEqual(json.loads(second["spec"])["revision"], "b" * 40)
        self.assertEqual([t["id"] for t in json.loads(second["targets"])], [2, 3])

    def test_manual_plan_consumes_pending_request_and_exclusions_win(self):
        self.evaluation_errors()
        self.queue_replan([1, 2])
        with self.assertRaisesRegex(ValueError, "explicit revision"):
            self.controller.plan(self.cid, [1])
        with patch("experiment.controller.Path.is_file", return_value=True):
            aid = self.controller.plan(
                self.cid,
                [1],
                "/nix/store/" + "e" * 32 + "-filnix-campaign-source",
                "a" * 40,
            )
        spec = json.loads(self.controller.active_attempts()[0]["spec"])
        self.assertEqual(spec["revision"], "a" * 40)
        self.assertEqual(spec["replan_requests"][0]["revision"], "f" * 40)
        self.finish(aid)
        self.controller.reconcile()
        with self.db:
            self.sql("UPDATE candidates SET state='excluded' WHERE id=2")
        with patch.object(self.controller, "admission_reason", return_value=""):
            self.controller.admit(self.controller.campaign(self.cid))
        self.assertEqual(self.sql("SELECT count(*) FROM replans").fetchone()[0], 0)
        self.assertFalse(self.controller.active_attempts())
        skipped = json.loads(
            self.sql(
                "SELECT payload FROM events WHERE kind='replan-skipped'"
            ).fetchone()[0]
        )
        self.assertEqual(skipped["candidates"][0]["candidate"], 2)

    def test_alias_planned_after_interruption_requires_explicit_retry(self):
        self.graph()
        with self.db:
            self.sql("UPDATE candidates SET drv=NULL,state='unplanned' WHERE id=3")
        self.scheduling(plan_ahead=128)
        build = self.attempt("build")
        plan = self.controller.plan(self.cid, [3])
        self.controller.reconcile()
        self.finish(build, "timeout")
        with patch("experiment.nix.valid", return_value=set()):
            self.controller.reconcile()
        self.plan_record(plan, 3, A)
        self.finish(plan)
        self.controller.reconcile()
        self.assertEqual(
            self.sql("SELECT state,error FROM candidates WHERE id=3").fetchone()[:],
            ("inconclusive", "timeout"),
        )

    def test_snapshot_keeps_active_build_amid_many_newer_plans(self):
        from experiment.web import snapshot

        build = self.attempt("build")
        original = self.sql("SELECT * FROM attempts WHERE id=?", (build,)).fetchone()
        with self.db:
            for i in range(20):
                self.sql(
                    "INSERT INTO attempts(id,campaign,kind,targets,state,created,spec) VALUES(?,?,'plan','[]','finished',?,'{}')",
                    (f"plan-{i}", self.cid, original["created"] + i + 1),
                )
        data = snapshot(self.db, self.cid)
        self.assertEqual(data["attempts"][0]["id"], build)

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
