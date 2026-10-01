"""Rolling admission, current output ownership and routing resource bounds."""

import json
import unittest
from unittest.mock import patch

import test_experiment as fixtures
from experiment import nix
from experiment.attempt import build
from experiment.controller import Controller
from experiment.model import encode, connect
from experiment.scheduling import BuildGraph, build_policy, reservations

MACHINES = [
    dict(
        uri="ssh-ng://builder",
        systems=["x86_64-linux"],
        max_jobs=6,
        supported=["benchmark"],
        mandatory=[],
    )
]


class SchedulingTests(unittest.TestCase):
    sql = fixtures.ExperimentTests.sql
    folder = fixtures.ExperimentTests.folder
    finish = fixtures.ExperimentTests.finish
    tearDown = fixtures.ExperimentTests.tearDown
    scheduling = fixtures.ExperimentTests.scheduling

    def setUp(self):
        fixtures.ExperimentTests.setUp(self)
        self.sql("DELETE FROM candidates")
        self.drvs = []
        for i in range(12):
            drv = f"/nix/store/{i:032d}-root-{i}.drv"
            self.drvs.append(drv)
            self.sql(
                "INSERT INTO derivations(drv,name,outputs,metadata) VALUES(?,?,?,?)",
                (
                    drv,
                    f"root-{i}",
                    encode({"out": drv[:-4]}),
                    encode(dict(system="x86_64-linux", features=[])),
                ),
            )
            self.sql(
                "INSERT INTO candidates(campaign,attr,label,selection,drv,state) VALUES(?,?,?,?,?,'queued')",
                (self.cid, encode([f"root-{i:02d}"]), f"root-{i:02d}", "{}", drv),
            )
        self.db.commit()
        self.scheduling(scheduling="rolling", plan_ahead=256)
        self.controller.machines = MACHINES
        self.controller.machines_observed = 10**12

    def admit(self):
        with patch.object(self.controller, "admission_reason", return_value=""):
            self.controller.admit(self.controller.campaign(self.cid))

    def test_single_roots_fill_both_pools_and_refill_without_waiting(self):
        self.admit()
        active = self.controller.active_attempts()
        self.assertEqual(len(active), 10)
        specs = [json.loads(a["spec"]) for a in active]
        self.assertEqual(
            [s["build_location"] for s in specs], ["remote"] * 6 + ["local"] * 4
        )
        self.assertTrue(all(len(s["targets"]) == 1 for s in specs))
        self.assertEqual(sum(s["policy"]["max_jobs"] for s in specs), 4)
        self.assertEqual(
            sum(s["policy"]["max_jobs"] * s["policy"]["cores"] for s in specs), 28
        )
        self.admit()
        self.assertEqual(len(self.controller.active_attempts()), 10)
        self.controller.reconcile()
        first = active[0]
        self.finish(first["id"])
        self.valid.return_value = {self.drvs[0][:-4]}
        self.controller.reconcile()
        self.admit()
        now = self.controller.active_attempts()
        self.assertEqual(len(now), 10)
        self.assertTrue({a["id"] for a in active[1:]} <= {a["id"] for a in now})
        last = json.loads(now[-1]["spec"])
        self.assertEqual(last["targets"], [self.drvs[10]])
        self.assertEqual(last["build_location"], "remote")
        Controller(self.db, self.state, self.units).reconcile()
        self.assertEqual(len(self.units.starts), 11)

    def test_required_features_go_local(self):
        self.sql(
            "UPDATE derivations SET metadata=? WHERE drv=?",
            (
                encode(dict(system="x86_64-linux", features=["big-parallel"])),
                self.drvs[0],
            ),
        )
        self.admit()
        specs = [json.loads(r["spec"]) for r in self.controller.active_attempts()]
        self.assertEqual(specs[0]["targets"], [self.drvs[0]])
        self.assertEqual(specs[0]["build_location"], "local")
        self.assertEqual(sum(s["build_location"] == "remote" for s in specs), 6)
        self.assertEqual(sum(s["build_location"] == "local" for s in specs), 4)

    def test_empty_remote_config_still_fills_local_pool(self):
        self.controller.machines = []
        self.admit()
        specs = [json.loads(r["spec"]) for r in self.controller.active_attempts()]
        self.assertEqual(len(specs), 4)
        self.assertTrue(all(s["build_location"] == "local" for s in specs))

    def test_dashboard_renders_every_rolling_request_and_its_log_link(self):
        from starlette.testclient import TestClient
        from bs4 import BeautifulSoup
        from experiment.dashboard.app import create_app

        self.admit()
        self.db.commit()
        response = TestClient(create_app(self.state)).get(
            f"/campaigns/{self.cid}"
        )
        self.assertEqual(response.status_code, 200)
        soup = BeautifulSoup(response.text, "html.parser")
        for attempt in self.controller.active_attempts():
            card = soup.find(id="active-" + attempt["id"])
            self.assertIsNotNone(card)
            self.assertEqual(card["data-roots"], "1")
            self.assertTrue(
                any(
                    a["href"].split("?", 1)[0].endswith(attempt["id"] + "/log")
                    for a in card.find_all("a")
                )
            )

    def test_backfill_stops_at_valid_required_output_not_uncached_ancestors(self):
        dep, target, ancestor = self.drvs[:3]
        dev = dep[:-4] + "-dev"
        self.sql(
            "UPDATE derivations SET outputs=? WHERE drv=?",
            (encode(dict(out=dep[:-4], dev=dev)), dep),
        )
        self.sql(
            "UPDATE derivations SET metadata=NULL WHERE drv IN (?,?)",
            (target, ancestor),
        )
        self.sql("INSERT INTO edges VALUES(?,?,?)", (target, dep, '["dev"]'))
        self.sql("INSERT INTO edges VALUES(?,?,?)", (dep, ancestor, '["out"]'))
        self.valid.return_value = {dev}
        data = {
            target: dict(
                outputs={"out": {"path": target[:-4]}},
                inputDrvs={dep: ["dev"]},
                system="x86_64-linux",
            )
        }
        with (
            patch("experiment.controller.Path.is_file", return_value=True),
            patch("experiment.nix.query", return_value=data) as query,
        ):
            available = self.controller.prepare_graph([target], True)
        self.assertEqual(query.call_args[0], ("derivation", "show", target))
        self.assertIn(dev, available)
        self.assertIsNone(
            self.sql(
                "SELECT metadata FROM derivations WHERE drv=?", (ancestor,)
            ).fetchone()[0]
        )

    def test_legacy_requests_keep_limits_and_rolling_rollback_drains(self):
        self.scheduling(scheduling="batched", build_lanes=2)
        old = self.controller.build_targets(
            self.controller.campaign(self.cid), [self.drvs[0], self.drvs[1]]
        )
        original = (self.folder(old) / "spec.json").read_bytes()
        self.scheduling(scheduling="rolling")
        self.admit()
        specs = [json.loads(r["spec"]) for r in self.controller.active_attempts()]
        self.assertEqual(len(specs), 9)  # old two-job client + six remote + two local
        self.assertEqual(sum(s["policy"]["max_jobs"] for s in specs), 4)
        self.assertEqual((self.folder(old) / "spec.json").read_bytes(), original)
        self.scheduling(scheduling="batched")
        self.admit()
        self.assertEqual(len(self.controller.active_attempts()), 9)

    def test_pause_and_pressure_block_admission(self):
        self.admit()
        self.controller.dispatch(dict(op="pause", campaign=self.cid))
        self.controller.tick()
        self.assertEqual(len(self.controller.active_attempts()), 10)
        with patch.object(
            self.controller, "admission_reason", return_value="memory pressure"
        ):
            self.controller.admit(self.controller.campaign(self.cid))
        self.assertEqual(len(self.controller.active_attempts()), 10)
        with self.assertRaises(ValueError):
            self.scheduling(plan_ahead=0)

    def test_realized_dependency_releases_without_claiming_build_or_checks(self):
        dependency, first, second = self.drvs[:3]
        for drv in (first, second):
            self.sql("INSERT INTO edges VALUES(?,?,?)", (drv, dependency, '["out"]'))
        aid = self.controller.build_targets(self.controller.campaign(self.cid), [first])
        self.valid.return_value = set()
        _, held, _ = reservations(
            self.db, self.state, self.controller.active_attempts()
        )
        self.assertIn(dependency, held)
        with self.assertRaisesRegex(ValueError, "owned"):
            self.controller.build_targets(self.controller.campaign(self.cid), [second])
        self.valid.return_value = {dependency[:-4]}
        self.controller.build_targets(self.controller.campaign(self.cid), [second])
        self.assertEqual(
            self.sql("SELECT state FROM attempts WHERE id=?", (aid,)).fetchone()[0],
            "intended",
        )
        row = self.sql(
            "SELECT available,origin,evidence_attempt FROM derivations WHERE drv=?",
            (dependency,),
        ).fetchone()
        self.assertEqual(tuple(row), (0, "unknown", None))
        self.assertEqual(self.sql("SELECT count(*) FROM tests").fetchone()[0], 0)

    def test_batched_admission_keeps_fresh_partial_cache_observation(self):
        first, dependency, second, cached = self.drvs[:4]
        self.scheduling(scheduling="batched", build_lanes=2)
        self.sql("DELETE FROM candidates WHERE drv NOT IN (?,?)", (first, second))
        for parent, child in ((first, dependency), (second, cached), (cached, dependency)):
            self.sql("INSERT INTO edges VALUES(?,?,?)", (parent, child, '["out"]'))
        self.controller.build_targets(self.controller.campaign(self.cid), [first])
        self.valid.side_effect = lambda paths: set(paths) & {cached[:-4]}
        self.admit()
        active = self.controller.active_attempts()
        self.assertEqual(len(active), 2)
        spec = json.loads(active[-1]["spec"])
        self.assertEqual(spec["targets"], [second])
        self.assertIn(cached[:-4], spec["admission_available"])

    def test_remote_capability_mismatch_requeues_locally_not_failure_loop(self):
        self.admit()
        aid = self.controller.active_attempts()[0]["id"]
        (self.folder(aid) / "stderr.log").write_bytes(
            b"error: Unable to start any build\n"
        )
        self.finish(aid, "build-error")
        self.controller.reconcile()
        self.assertTrue(
            json.loads(
                self.sql(
                    "SELECT metadata FROM derivations WHERE drv=?", (self.drvs[0],)
                ).fetchone()[0]
            )["local_only"]
        )
        self.assertEqual(
            self.sql(
                "SELECT state FROM candidates WHERE drv=?", (self.drvs[0],)
            ).fetchone()[0],
            "queued",
        )
        # Local pool is full: don't route it back to an available remote slot.
        self.admit()
        self.assertEqual(
            self.sql(
                "SELECT state FROM candidates WHERE drv=?", (self.drvs[0],)
            ).fetchone()[0],
            "queued",
        )

    def test_remote_eligibility_includes_dependencies_and_mandatory_features(self):
        graph = BuildGraph(self.db)
        self.assertTrue(graph.remote_eligible(self.drvs[:1], MACHINES))
        self.sql("UPDATE derivations SET metadata=NULL WHERE drv=?", (self.drvs[1],))
        self.assertFalse(graph.remote_eligible(self.drvs[:2], MACHINES))
        mandatory = [dict(MACHINES[0], mandatory=["benchmark"])]
        self.assertFalse(graph.remote_eligible(self.drvs[:1], mandatory))
        self.sql(
            "UPDATE derivations SET metadata=? WHERE drv=?",
            (encode(dict(system="x86_64-linux", features=["benchmark"])), self.drvs[0]),
        )
        self.assertTrue(graph.remote_eligible(self.drvs[:1], mandatory))

    def test_job_and_cpu_bounds_include_immutable_legacy_specs(self):
        p = dict(nix.DEFAULT_POLICY, scheduling="rolling", plan_ahead=256, cpus="0-63")
        old = dict(spec=encode(dict(policy=dict(nix.DEFAULT_POLICY, max_jobs=4))))
        self.assertIsNone(build_policy(p, [old]))  # spare CPUs are not extra job slots
        remote = dict(
            spec=encode(dict(build_location="remote", policy=dict(p, max_jobs=0)))
        )
        self.assertEqual(build_policy(p, [remote])["max_jobs"], 1)
        self.assertIsNone(build_policy(p, [remote] * 6, "remote", MACHINES))
        self.assertIsNone(build_policy(p, [], "remote", []))
        p["cpus"] = "0-5"
        self.assertIsNone(build_policy(p, []))

    def test_output_backfill_preserves_provenance_and_structured_features(self):
        drv = self.drvs[0]
        self.sql(
            "UPDATE derivations SET outputs=?,metadata=NULL,available=1,origin='local',evidence_attempt='old' WHERE drv=?",
            ('{"out":null}', drv),
        )
        data = {
            drv: dict(
                outputs={"out": {}},
                inputDrvs={},
                system="x86_64-linux",
                env={"__json": encode(dict(requiredSystemFeatures=["big-parallel"]))},
            )
        }
        with (
            patch("experiment.nix.Path.is_file", return_value=True),
            patch(
                "experiment.nix.subprocess.check_output", return_value=drv[:-4] + "\n"
            ) as query,
        ):
            nix.add_graph(self.db, data)
        self.assertIn("--query", query.call_args[0][0])
        row = self.sql(
            "SELECT outputs,metadata,available,origin,evidence_attempt FROM derivations WHERE drv=?",
            (drv,),
        ).fetchone()
        self.assertEqual(json.loads(row["outputs"]), {"out": drv[:-4]})
        self.assertEqual(json.loads(row["metadata"])["features"], ["big-parallel"])
        self.assertEqual(tuple(row)[2:], (1, "local", "old"))

    def test_v4_migration_keeps_attempt_specs_and_results(self):
        self.admit()
        before = [tuple(r) for r in self.sql("SELECT id,spec,state FROM attempts")]
        self.sql("ALTER TABLE derivations DROP COLUMN metadata")
        self.sql("PRAGMA user_version=4")
        self.db.commit()
        self.db.close()
        self.db = connect(self.state)
        self.assertEqual(
            [tuple(r) for r in self.sql("SELECT id,spec,state FROM attempts")], before
        )
        self.assertEqual(self.sql("PRAGMA user_version").fetchone()[0], 5)

    def test_worker_disables_offload_only_for_local_rolling_requests(self):
        folder = self.state / "worker"
        folder.mkdir()
        for location, jobs in (("local", 1), ("remote", 0), (None, 2)):
            spec = dict(
                targets=self.drvs[:1],
                output_paths=[],
                policy=dict(nix.DEFAULT_POLICY, max_jobs=jobs),
            )
            if location:
                spec["build_location"] = location
            with (
                patch(
                    "experiment.attempt.nix.resources", return_value={"verified": True}
                ),
                patch(
                    "experiment.attempt.subprocess.Popen",
                    side_effect=RuntimeError("command captured"),
                ) as popen,
            ):
                with self.assertRaisesRegex(RuntimeError, "command captured"):
                    build(folder, spec)
            command = popen.call_args[0][0]
            self.assertEqual(command[command.index("--max-jobs") + 1], str(jobs))
            self.assertEqual("--builders" in command, location == "local")
            self.assertEqual(command[-1], self.drvs[0] + "^*")


class MachineTests(unittest.TestCase):
    def test_configured_capacity_defaults_comments_and_deduplication(self):
        config = dict(
            system={"value": "x86_64-linux"},
            builders={
                "value": "ssh-ng://a x86_64-linux /private/key 6 1 benchmark - - # comment\n"
                "ssh-ng://b - - 2 - benchmark benchmark\nssh-ng://a x86_64-linux - 6 1 benchmark -; ssh-ng://c"
            },
        )
        with patch("experiment.nix.query", return_value=config):
            machines = nix.build_machines()
        self.assertEqual(sum(m["max_jobs"] for m in machines), 9)
        self.assertEqual(machines[1]["systems"], ["x86_64-linux"])
        self.assertEqual(machines[1]["mandatory"], ["benchmark"])
        self.assertNotIn("/private/key", encode(machines))
        with patch(
            "experiment.nix.query", return_value=dict(config, builders={"value": ""})
        ):
            self.assertEqual(nix.build_machines(), [])
