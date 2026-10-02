"""Planner scratch retention must never race durable recovery or lose logs."""

import gzip
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import uuid

from experiment.attempt import plan
from experiment.model import atomic_json, connect, encode
from experiment.retention import prune_plans


class RetentionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.state = Path(self.tmp.name)
        self.db = connect(self.state)
        self.addCleanup(self.db.close)
        self.cutoff = 200000 - 86400

    def attempt(self, kind="plan", state="finished", finished=None):
        aid = str(uuid.uuid4())
        self.db.execute(
            "INSERT INTO attempts(id,campaign,kind,targets,state,created,finished,spec) VALUES(?,?,?,?,?,?,?,?)",
            (aid, "campaign", kind, "[]", state, 1, finished, "{}"),
        )
        folder = self.state / "attempts" / aid
        folder.mkdir(parents=True)
        for name in (
            "spec.json",
            "started.json",
            "exit.json",
            "plan.jsonl",
            "stderr.log",
            "stdout.log",
            "before.json",
            "build-times.json",
            "graph-1.json",
            "graph-2.json.gz",
            "graph-3.tmp",
            "graph-4.json.tmp",
            "graph-not-a-candidate.json",
        ):
            (folder / name).write_bytes(name.encode())
        return folder

    @patch("experiment.retention.stamp", return_value=200000)
    def test_only_consumed_old_planner_graphs_are_pruned(self, _stamp):
        old = self.attempt(finished=self.cutoff - 1)
        boundary = self.attempt(finished=self.cutoff)
        untouched = [
            self.attempt(finished=self.cutoff + 1),
            self.attempt(state="running", finished=self.cutoff - 1),
            self.attempt(state="intended", finished=self.cutoff - 1),
            self.attempt(kind="build", finished=self.cutoff - 1),
            self.attempt(),  # A missing terminal timestamp is not eligible.
        ]
        (old / "graph-9.json").symlink_to(old / "stderr.log")
        (old / "graph-10.json").mkdir()
        self.db.commit()
        facts = self.db.execute("SELECT * FROM attempts ORDER BY id").fetchall()
        before = {
            p: p.read_bytes() for p in self.state.glob("attempts/*/*") if p.is_file()
        }
        report = prune_plans(self.state)
        self.assertTrue(report["dry_run"])
        self.assertEqual((report["attempts"], report["files"]), (2, 8))
        self.assertEqual({p: p.read_bytes() for p in before}, before)
        applied = prune_plans(self.state, apply=True)
        self.assertFalse(applied["dry_run"])
        self.assertEqual(applied["logical_bytes"], report["logical_bytes"])
        removed = {
            f / n
            for f in (old, boundary)
            for n in (
                "graph-1.json",
                "graph-2.json.gz",
                "graph-3.tmp",
                "graph-4.json.tmp",
            )
        }
        self.assertTrue(all(not p.exists() for p in removed))
        for p, data in before.items():
            if p not in removed:
                self.assertEqual(p.read_bytes(), data)
        self.assertTrue(all((f / "graph-1.json").exists() for f in untouched))
        self.assertTrue((old / "graph-9.json").is_symlink())
        self.assertTrue((old / "graph-10.json").is_dir())
        self.assertEqual(
            self.db.execute("SELECT * FROM attempts ORDER BY id").fetchall(), facts
        )
        self.assertEqual(prune_plans(self.state, apply=True)["files"], 0)

    @patch("experiment.retention.stamp", return_value=200000)
    def test_uncommitted_completion_is_not_visible_to_cleanup(self, _stamp):
        folder = self.attempt(state="running", finished=self.cutoff - 2)
        self.db.commit()
        self.db.execute("UPDATE attempts SET state='finished'")
        self.assertEqual(prune_plans(self.state, apply=True)["files"], 0)
        self.assertTrue((folder / "graph-1.json").exists())
        self.db.commit()
        self.assertEqual(prune_plans(self.state, apply=True)["files"], 4)

    def test_atomic_gzip_json_is_complete_and_preserves_previous_file_on_error(self):
        path = self.state / "graph-17.json.gz"
        value = {"small": [3, 11], "large": "asymmetric payload " * 20000}
        atomic_json(path, value)
        self.assertLess(path.stat().st_size, len(encode(value)) // 10)
        with gzip.open(path, "rt") as f:
            self.assertEqual(json.load(f), value)
        old = path.read_bytes()
        with patch("experiment.model.json.dump", side_effect=OSError("disk full")):
            with self.assertRaises(OSError):
                atomic_json(path, {"replacement": 9})
        self.assertEqual(path.read_bytes(), old)

    def test_planner_produces_compressed_graph_before_publishing_row(self):
        folder = self.state / "planner"
        folder.mkdir()
        drv = "/nix/store/" + "a" * 32 + "-library.drv"
        graph = {
            drv: {"outputs": {"out": {"path": "/nix/store/output"}}, "inputDrvs": {}}
        }
        recipe = {"drv": drv, "roles": []}
        spec = {
            "policy": {"eval_seconds": 1},
            "source": "/nix/store/source",
            "targets": [{"id": 71, "attr": ["library"]}],
        }
        with (
            patch(
                "experiment.attempt.subprocess.run",
                return_value=subprocess.CompletedProcess(
                    [], 0, encode(recipe).encode(), b""
                ),
            ),
            patch("experiment.attempt.nix.graph", return_value=graph),
        ):
            self.assertEqual(plan(folder, spec)["exit_code"], 0)
        row = json.loads((folder / "plan.jsonl").read_text())
        self.assertEqual(row["graph"], "graph-71.json.gz")
        with gzip.open(folder / "graph-71.json.gz", "rt") as f:
            self.assertEqual(json.load(f), graph)
        self.assertEqual(row["recipe"], recipe)


if __name__ == "__main__":
    unittest.main()
