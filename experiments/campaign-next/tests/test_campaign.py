"""Real C++ API builds in a disposable store; never use the campaign database."""

import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest

BINARY = Path(sys.argv.pop(1)).resolve()


def invoke(*args, check=True, **kwargs):
    return subprocess.run(
        [str(BINARY), *map(str, args)],
        capture_output=True,
        check=check,
        timeout=20,
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
            NIX_CONFIG="sandbox = false\nbuild-users-group =\nsubstituters =\n"
            "builders =\nmax-jobs = 1\ncores = 1\n",
        )
        self.journal = self.root / "run.jsonl"

    def drv(self, name):
        return subprocess.check_output(
            [
                "nix-instantiate",
                "--store",
                self.store,
                str(Path(__file__).with_name("fixtures.nix")),
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

    def record(self, drv, journal=None):
        return invoke(
            "record",
            drv,
            journal or self.journal,
            "--store",
            self.store,
            check=False,
            env=self.env,
        )

    def inspect(self, path=None):
        return json.loads(invoke("inspect", path or self.journal).stdout)

    def events(self, path=None):
        return [
            json.loads(line)
            for line in (path or self.journal).read_bytes().splitlines()
        ]

    def output(self, events):
        return [
            bytes.fromhex(e["payload"]["fields"][0]["string_hex"])
            for e in events
            if e["kind"] == "nix.result" and e["payload"]["build_output"]
        ]

    def test_real_build_cached_reuse_and_lossless_replay(self):
        drv = self.drv("good")
        result = self.record(drv)
        self.assertEqual(result.returncode, 0, result.stderr.decode(errors="replace"))
        events = self.events()
        summary = self.inspect()
        live = json.loads(result.stdout)
        summary.pop("torn_tail_bytes")
        self.assertEqual(summary, live)
        self.assertEqual(summary["outcome"], "built")
        self.assertEqual([e["seq"] for e in events], list(range(1, len(events) + 1)))
        self.assertEqual(events[0]["kind"], "run.requested")
        self.assertEqual(events[-1]["kind"], "run.finished")
        self.assertIn(b"stdout-before", self.output(events))
        self.assertIn(b"stderr-after", self.output(events))
        self.assertIn(b"binary:\xff", self.output(events))
        times = [e["elapsed_ns"] for e in events]
        self.assertEqual(times, sorted(times))
        observed = {
            line: e
            for e in events
            if e["kind"] == "nix.result" and e["payload"]["build_output"]
            for line in [bytes.fromhex(e["payload"]["fields"][0]["string_hex"])]
        }
        gap = (
            observed[b"stderr-after"]["payload"]["capture"]["mono_ns"]
            - observed[b"stdout-before"]["payload"]["capture"]["mono_ns"]
        )
        self.assertGreater(gap, 60_000_000)
        for output in summary["outputs"]:
            self.assertTrue(output["valid"])
            self.assertEqual(
                (Path(output["path"]) / "result").read_text(), "artifact\n"
            )
        prefix = self.root / "incomplete.jsonl"
        prefix.write_bytes(
            b"".join(json.dumps(e).encode() + b"\n" for e in events[:-1])
        )
        self.assertEqual(self.inspect(prefix)["outcome"], "incomplete")
        replay = invoke("replay", self.journal, "--speed", "0", "--json")
        self.assertEqual(
            [json.loads(line) for line in replay.stdout.splitlines()], events
        )
        plain = invoke("replay", self.journal, "--speed", "10")
        self.assertIn(b"binary:\xff", plain.stdout)
        second = self.root / "cached.jsonl"
        self.assertEqual(self.record(drv, second).returncode, 0)
        self.assertEqual(self.inspect(second)["outcome"], "already-valid")
        self.assertEqual(self.output(self.events(second)), [])
        original = self.journal.read_bytes()
        self.assertNotEqual(self.record(drv).returncode, 0)
        self.assertEqual(self.journal.read_bytes(), original)

    def test_dependency_failure_is_a_result_not_successful_activity_stop(self):
        result = self.record(self.drv("blocked"))
        self.assertEqual(result.returncode, 1, result.stderr.decode(errors="replace"))
        self.assertEqual(self.inspect()["outcome"], "failed")
        events = self.events()
        self.assertIn(b"dependency-failed", self.output(events))
        self.assertNotIn(b"consumer-must-not-run", self.output(events))
        outcomes = [e for e in events if e["kind"] == "nix.build-result"]
        self.assertEqual(len(outcomes), 1)
        self.assertFalse(outcomes[0]["payload"]["success"])
        self.assertTrue(any(e["kind"] == "nix.activity-stopped" for e in events))

    def test_worker_api_error_is_not_a_package_failure(self):
        drv = self.drv("good")
        Path(drv).unlink()
        result = self.record(drv)
        self.assertEqual(result.returncode, 2, result.stderr.decode(errors="replace"))
        self.assertEqual(self.inspect()["outcome"], "worker-error")
        events = self.events()
        self.assertTrue(any(e["kind"] == "worker.error" for e in events))
        self.assertFalse(any(e["kind"] == "nix.build-result" for e in events))
        self.assertEqual(events[-1]["kind"], "run.finished")

    def test_cancellation_drains_and_records_terminal_result(self):
        proc = subprocess.Popen(
            [
                str(BINARY),
                "record",
                self.drv("slow"),
                str(self.journal),
                "--store",
                self.store,
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=self.env,
        )
        try:
            deadline = time.monotonic() + 10
            marker = b"ready-for-cancellation".hex().encode()
            while time.monotonic() < deadline:
                if self.journal.exists() and marker in self.journal.read_bytes():
                    break
                if proc.poll() is not None:
                    self.fail(
                        f"worker finished before cancellation: {proc.communicate()}"
                    )
                time.sleep(0.02)
            else:
                self.fail("did not observe the running builder")
            proc.send_signal(signal.SIGINT)
            out, err = proc.communicate(timeout=8)
            self.assertNotEqual(proc.returncode, 0, err)
            self.assertEqual(json.loads(out)["outcome"], "cancelled")
            self.assertEqual(self.inspect()["outcome"], "cancelled")
            self.assertEqual(self.events()[-1]["kind"], "run.finished")
        finally:
            if proc.poll() is None:
                proc.kill()
                proc.communicate()

    def test_journal_prefix_corruption_and_replay_clock(self):
        events = [
            {
                "version": 1,
                "run": "recorded",
                "seq": 1,
                "wall_ns": 100,
                "elapsed_ns": 0,
                "kind": "run.requested",
                "payload": {"drv": "example.drv"},
            },
            {
                "version": 1,
                "run": "recorded",
                "seq": 2,
                "wall_ns": 101,
                "elapsed_ns": 300_000_000,
                "kind": "nix.activity-stopped",
                "payload": {"id": 7},
            },
        ]
        original = b"".join(json.dumps(e).encode() + b"\n" for e in events)
        self.journal.write_bytes(original + b'{"partial":')
        summary = self.inspect()
        self.assertEqual(summary["outcome"], "incomplete")
        self.assertFalse(summary["complete"])
        self.assertEqual(summary["torn_tail_bytes"], 11)
        start = time.monotonic()
        replay = invoke("replay", self.journal, "--speed", "1", "--json")
        self.assertGreater(time.monotonic() - start, 0.25)
        self.assertEqual(
            [json.loads(line) for line in replay.stdout.splitlines()], events
        )
        start = time.monotonic()
        invoke("replay", self.journal, "--speed", "10", "--json")
        self.assertLess(time.monotonic() - start, 0.25)
        for speed in ("nan", "inf", "-1", "1garbage"):
            self.assertEqual(
                invoke(
                    "replay", self.journal, "--speed", speed, check=False
                ).returncode,
                2,
            )
        self.journal.write_bytes(original + b"not-json\n")
        self.assertEqual(invoke("inspect", self.journal, check=False).returncode, 2)
        for field, value in (("seq", 3), ("run", "different"), ("elapsed_ns", -1)):
            with self.subTest(field=field):
                changed = [events[0], dict(events[1], **{field: value})]
                self.journal.write_text("".join(json.dumps(e) + "\n" for e in changed))
                self.assertEqual(
                    invoke("inspect", self.journal, check=False).returncode, 2
                )


if __name__ == "__main__":
    unittest.main()
