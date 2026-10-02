import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import pyarrow.parquet as pq
import duckdb

from experiment.analytics import (
    LocalBackend,
    Publisher,
    S3Backend,
    latest_sql,
    load_chain,
    main,
)
from experiment.model import connect, event


class FailingBackend(LocalBackend):
    fail = False

    def publish(self, key, data, expected_etag):
        if self.fail:
            self.fail = False
            raise OSError("simulated pointer publication failure")
        return super().publish(key, data, expected_etag)


class AnalyticsTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.experiment, self.state, remote = (
            root / "exp",
            root / "state",
            root / "remote",
        )
        self.experiment.mkdir()
        self.source = connect(self.experiment)
        self.source.execute(
            "INSERT INTO campaigns(id,name,created,manifest,source,revision,policy,nix_version) VALUES('c','camp',1,'{}','s','r','{}','n')"
        )
        self.source.execute(
            "INSERT INTO derivations(drv,name,outputs) VALUES('/drv/a','a','[]')"
        )
        self.source.execute("INSERT INTO edges VALUES('/drv/a','/drv/b','[]')")
        self.source.commit()
        self.backend = FailingBackend(remote)

    def tearDown(self):
        self.source.close()
        self.tmp.cleanup()

    def publisher(self, log_bytes=256 * 1024**2):
        return Publisher(
            self.experiment, self.state, self.backend, "dataset", log_bytes
        )

    def parts(self, manifest, table):
        return [
            pq.ParquetFile(self.backend.root / item["key"]).read().to_pylist()
            for item in manifest["files"]
            if item["table"] == table
        ]

    def test_noop_and_mutation_deletion_tombstone(self):
        publisher = self.publisher()
        first = publisher.publish()
        self.assertEqual(self.parts(first, "derivations")[0][0]["_deleted"], False)
        self.assertEqual(len(self.parts(first, "derivations")), 1)
        obj_count = len(
            list((self.backend.root / "dataset/objects").rglob("*.parquet"))
        )
        self.assertTrue(first["files"])
        second = publisher.publish()
        self.assertIsNone(second["generation"])
        self.assertEqual(
            obj_count,
            len(list((self.backend.root / "dataset/objects").rglob("*.parquet"))),
        )
        self.source.execute("UPDATE derivations SET name='updated' WHERE drv='/drv/a'")
        self.source.execute("DELETE FROM edges WHERE parent='/drv/a'")
        self.source.commit()
        third = publisher.publish()
        self.assertEqual(self.parts(third, "derivations")[0][0]["name"], "updated")
        tomb = self.parts(third, "edges")[0][0]
        self.assertTrue(tomb["_deleted"])
        self.assertEqual((tomb["parent"], tomb["child"]), ("/drv/a", "/drv/b"))
        connection = duckdb.connect()
        connection.execute(
            latest_sql([first, third], lambda key: str(self.backend.root / key))
        )
        self.assertEqual(
            connection.execute("SELECT count(*) FROM edges").fetchone()[0],
            0,
        )
        self.assertEqual(
            connection.execute("SELECT name FROM derivations").fetchall(),
            [("updated",)],
        )
        self.assertEqual(
            connection.execute(
                "SELECT name FROM temporal_derivations ORDER BY _revision"
            ).fetchall(),
            [("a",), ("updated",)],
        )
        self.assertEqual(
            connection.execute("SELECT count(*) FROM replans").fetchone()[0], 0
        )
        self.assertEqual(connection.execute("DESCRIBE replans").fetchone()[1], "BIGINT")
        self.assertEqual(
            connection.execute("SELECT count(*) FROM build_logs").fetchone()[0], 0
        )
        self.assertEqual(load_chain(self.backend, "dataset"), [first, third])
        connection.close()
        publisher.close()

    def test_live_stderr_respects_committed_offset_and_only_complete_lines(self):
        aid = "live-attempt"
        self.source.execute(
            "INSERT INTO attempts(id,campaign,kind,targets,state,created,spec,offset) VALUES(?,?,'build','[]','running',1,'{}',0)",
            (aid, "c"),
        )
        self.source.commit()
        log = self.experiment / "attempts" / aid / "stderr.log"
        log.parent.mkdir(parents=True)
        log.write_bytes(b"ready\nnot-yet\n")
        self.source.execute("UPDATE attempts SET offset=6 WHERE id=?", (aid,))
        self.source.commit()
        p = self.publisher()
        manifest = p.publish()
        rows = sum(self.parts(manifest, "logs"), [])
        self.assertEqual(b"".join(row["raw"] for row in rows), b"ready\n")
        p.close()

    def test_composite_key_null_and_exact_log_roundtrip_with_budget(self):
        aid = "attempt-1"
        self.source.execute(
            "INSERT INTO attempts(id,campaign,kind,targets,state,created,spec,offset) VALUES(?,?,'build','[]','finished',1,'{}',0)",
            (aid, "c"),
        )
        self.source.execute(
            "INSERT INTO activities(attempt,activity,drv,kind,phase,checks) VALUES(?,?,NULL,'build',NULL,'[]')",
            (aid, "act"),
        )
        self.source.commit()
        log = self.experiment / "attempts" / aid / "stderr.log"
        log.parent.mkdir(parents=True)
        raw = (
            b"valid\ninvalid\xffline\n"
            + b"z" * (1024 * 1024 + 21)
            + b"\n"
            + b"torn\xff"
        )
        log.write_bytes(raw)
        # Finished logs include terminal torn bytes. A small byte budget advances incrementally.
        p = self.publisher(log_bytes=400000)
        one = p.publish()
        records = sum((self.parts(one, "logs")), [])
        self.assertEqual(sum(len(r["raw"]) for r in records), 400000)
        self.assertEqual(records[0]["raw"], b"valid\n")
        p.close()
        p = self.publisher(log_bytes=400000)
        two = p.publish()
        records += sum((self.parts(two, "logs")), [])
        self.assertTrue(all(r["end"] - r["start"] == len(r["raw"]) for r in records))
        self.assertEqual(b"".join(r["raw"] for r in records), raw[:800000])
        while sum(len(r["raw"]) for r in records) < len(raw):
            records += sum(self.parts(p.publish(), "logs"), [])
        self.assertEqual(b"".join(r["raw"] for r in records), raw)
        self.assertEqual(records[-1]["raw"], b"torn\xff")
        self.assertTrue(records[-1]["fragment"])
        self.assertIsNone(p.publish()["generation"])
        p.close()

    def test_pointer_failure_restarts_same_generation_and_cleans_spool(self):
        self.backend.fail = True
        p = self.publisher()
        with self.assertRaises(OSError):
            p.publish()
        pending = p.db.execute("SELECT id FROM pending").fetchone()[0]
        p.close()
        p = self.publisher()
        manifest = p.publish()
        self.assertEqual(manifest["generation"], pending)
        self.assertEqual(list((self.state / "spool").iterdir()), [])
        # Crash after remote pointer success but before local checkpoint installation.
        p._finalize = lambda: (_ for _ in ()).throw(RuntimeError("simulated crash"))
        self.source.execute("UPDATE derivations SET name='after' WHERE drv='/drv/a'")
        self.source.commit()
        with self.assertRaises(RuntimeError):
            p.publish()
        p.close()
        p = self.publisher()
        already = p.publish()
        self.assertEqual(
            already["generation"],
            self.backend.get("dataset/latest.json")[0]
            and json.loads(self.backend.get("dataset/latest.json")[0])["generation"],
        )
        p.close()

    def test_remote_existing_without_checkpoint_and_wrong_parent_rejected(self):
        p = self.publisher()
        p.publish()
        p.close()
        # Another checkpoint cannot claim this dataset.
        fresh = Path(self.tmp.name) / "other-state"
        with self.assertRaisesRegex(ValueError, "checkpoint is missing"):
            Publisher(self.experiment, fresh, self.backend, "dataset")
        p = self.publisher()
        self.source.execute("UPDATE derivations SET name='x'")
        self.source.commit()
        p.publish()
        p.close()
        # An externally moved pointer is a parent conflict, not a blind overwrite.
        pointer = self.backend.root / "dataset/latest.json"
        pointer.write_text('{"generation":"external"}')
        self.source.execute("UPDATE derivations SET name='y'")
        self.source.commit()
        with self.assertRaisesRegex(ValueError, "unexpected parent"):
            self.publisher()

    def test_event_continuation_and_upload_failure(self):
        event(self.source, "c", "one", {"x": 1})
        self.source.commit()
        p = self.publisher()
        with patch.object(
            self.backend, "put_immutable", side_effect=OSError("upload failed")
        ):
            with self.assertRaises(OSError):
                p.publish()
        self.assertIsNone(self.backend.get("dataset/latest.json")[0])
        p.close()
        event(self.source, "c", "two", {"y": 2})
        self.source.commit()
        p = self.publisher()
        first = p.publish()
        self.assertEqual(
            [r["kind"] for part in self.parts(first, "events") for r in part], ["one"]
        )
        second = p.publish()
        self.assertEqual(
            [r["kind"] for part in self.parts(second, "events") for r in part], ["two"]
        )
        self.assertEqual(second["events_seq"], 2)
        self.assertEqual(load_chain(self.backend, "dataset"), [first, second])
        self.source.execute("DELETE FROM events")
        self.source.commit()
        with self.assertRaisesRegex(ValueError, "rewound"):
            p.publish()
        p.close()

    def test_bounded_batches_and_snapshot_timestamp(self):
        for i in range(13):
            self.source.execute(
                "INSERT INTO derivations(drv,name,outputs) VALUES(?,?,?)",
                (f"/drv/{i}", "x" * 700, "[]"),
            )
        self.source.commit()
        p = self.publisher()
        with patch("experiment.analytics.PART_BYTES", 1024):
            manifest = p.publish()
        rows = sum(self.parts(manifest, "derivations"), [])
        self.assertEqual(len(rows), 14)
        self.assertGreater(len(self.parts(manifest, "derivations")), 7)
        self.assertEqual({r["_observed_at"] for r in rows}, {manifest["observed_at"]})
        p.close()

    def test_cli_backfill_budget_override_is_only_for_one_run(self):
        aid = "budget-override"
        self.source.execute(
            "INSERT INTO attempts(id,campaign,kind,targets,state,created,spec) VALUES(?,'c','build','[]','finished',1,'{}')",
            (aid,),
        )
        self.source.commit()
        folder = self.experiment / "attempts" / aid
        folder.mkdir(parents=True)
        (folder / "stderr.log").write_bytes(b"abcdefghij\n")
        config = Path(self.tmp.name) / "config.json"
        config.write_text(
            json.dumps(
                dict(
                    bucket="test",
                    experiment=str(self.experiment),
                    state=str(self.state),
                    prefix="dataset",
                    log_bytes=2,
                    reserve_bytes=0,
                )
            )
        )
        with patch("experiment.analytics.S3Backend", return_value=self.backend):
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                main(["--config", str(config), "--log-bytes", "8"])
            self.assertEqual(json.loads(out.getvalue())["log_bytes"], 8)
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                main(["--config", str(config)])
            self.assertEqual(json.loads(out.getvalue())["log_bytes"], 2)
        self.assertEqual(json.loads(config.read_text())["log_bytes"], 2)

    def test_corrupt_pending_object_does_not_publish(self):
        p = self.publisher()
        with patch.object(
            self.backend, "put_immutable", side_effect=OSError("offline")
        ):
            with self.assertRaises(OSError):
                p.publish()
        p.close()
        next((self.state / "spool").glob("*.parquet")).write_bytes(b"corrupted")
        p = self.publisher()
        with self.assertRaisesRegex(ValueError, "checksum mismatch"):
            p.publish()
        self.assertIsNone(self.backend.get("dataset/latest.json")[0])
        self.assertIsNotNone(p.db.execute("SELECT id FROM pending").fetchone())
        p.close()

    def test_activity_identity_is_not_reverse_looked_up_by_drv(self):
        aid = "identity-test"
        drv = "/nix/store/" + "a" * 32 + "-test.drv"
        self.source.execute(
            "INSERT INTO attempts(id,campaign,kind,targets,state,created,spec) VALUES(?,'c','build','[]','finished',1,'{}')",
            (aid,),
        )
        for activity in ("17", "29"):
            self.source.execute(
                "INSERT INTO activities(attempt,activity,drv) VALUES(?,?,?)",
                (aid, activity, drv),
            )
        self.source.commit()
        log = self.experiment / "attempts" / aid / "stderr.log"
        log.parent.mkdir(parents=True)
        raw = b'plain\n@nix {"action":"result","id":29,"type":101,"fields":["distinct output"]}\n'
        log.write_bytes(raw)
        p = self.publisher()
        manifest = p.publish()
        rows = sum(self.parts(manifest, "logs"), [])
        self.assertEqual(rows[1]["activity"], "29")
        self.assertEqual(rows[1]["derivation"], drv)
        self.assertEqual(rows[1]["text"], "distinct output")
        with duckdb.connect() as con:
            con.execute(latest_sql(manifest, lambda key: str(self.backend.root / key)))
            self.assertEqual(
                con.execute(
                    "SELECT activity FROM build_logs ORDER BY start"
                ).fetchall(),
                [(None,), ("29",)],
            )
        p.close()

    def test_destination_and_missing_remote_checkpoint(self):
        p = self.publisher()
        p.publish()
        p.close()
        with self.assertRaisesRegex(ValueError, "different source/destination"):
            Publisher(
                self.experiment,
                self.state,
                LocalBackend(Path(self.tmp.name) / "wrong"),
                "dataset",
            )
        (self.backend.root / "dataset/latest.json").unlink()
        with self.assertRaisesRegex(ValueError, "pointer is missing"):
            self.publisher()

    def test_s3_permission_error_is_not_reported_as_conflict(self):
        from botocore.exceptions import ClientError
        from unittest.mock import Mock

        backend = object.__new__(S3Backend)
        backend.bucket = "test"
        backend.client = Mock()
        error = ClientError({"Error": {"Code": "AccessDenied"}}, "PutObject")
        backend.client.put_object.side_effect = error
        with self.assertRaises(ClientError):
            backend.publish("latest.json", b"{}", None)

    def test_live_oversized_line_and_stdout_do_not_consume_torn_bytes(self):
        aid = "oversized-live"
        self.source.execute(
            "INSERT INTO attempts(id,campaign,kind,targets,state,created,spec,offset) VALUES(?,'c','build','[]','running',1,'{}',?)",
            (aid, 1100006),
        )
        self.source.commit()
        folder = self.experiment / "attempts" / aid
        folder.mkdir(parents=True)
        raw = b"large" + b"x" * 1100000 + b"\ntorn"
        (folder / "stderr.log").write_bytes(raw)
        (folder / "stdout.log").write_bytes(b"out\ntorn")
        p = self.publisher(log_bytes=400000)
        collected = {"stdout": [], "stderr": []}
        for _ in range(3):
            manifest = p.publish()
            for row in sum(self.parts(manifest, "logs"), []):
                collected[row["stream"]].append(row["raw"])
        self.assertEqual(b"".join(collected["stderr"]), raw[:-4])
        self.assertEqual(b"".join(collected["stdout"]), b"out\n")
        self.assertIsNone(p.publish()["generation"])
        p.close()


if __name__ == "__main__":
    unittest.main()
