import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

from botocore.exceptions import ClientError
import duckdb

from experiment.analytics import LocalBackend, Publisher, S3Backend, latest_sql
from experiment.analytics_share import publish_share
from experiment.model import connect


class ShareTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.source = connect(root / "source")
        self.source.execute(
            "INSERT INTO derivations(drv,name,outputs) VALUES('/a','first','[]')"
        )
        self.source.execute("INSERT INTO edges VALUES('/a','/b','[]')")
        self.source.commit()
        self.backend = LocalBackend(root / "remote")
        self.publisher = Publisher(
            root / "source", root / "state", self.backend, "private"
        )
        self.prefix = "share/abcdefghijklmnop/v1"
        self.publisher.publish()

    def tearDown(self):
        self.publisher.close()
        self.source.close()
        self.tmp.cleanup()

    def share(self):
        return publish_share(
            self.backend, "private", self.prefix, "https://example.test"
        )

    def test_full_history_latest_deletion_and_incremental_reuse(self):
        first = self.share()
        self.assertGreater(first["copied"], 0)
        self.assertEqual(self.share(), {"copied": 0, "unchanged": True})
        self.source.execute("UPDATE derivations SET name='second'")
        self.source.execute("DELETE FROM edges")
        self.source.commit()
        delta = self.publisher.publish()
        with patch.object(
            self.backend, "copy_immutable", wraps=self.backend.copy_immutable
        ) as copy:
            second = self.share()
            self.assertEqual(copy.call_count, len(delta["files"]))
        self.assertEqual(second["copied"], len(delta["files"]))
        data, _ = self.backend.get(f"{self.prefix}/index.json")
        index = json.loads(data)
        data, _ = self.backend.get(index["manifest"])
        manifest = json.loads(data)
        self.assertIsNone(manifest["parent"])
        self.assertEqual(len(manifest["files"]), first["objects"] + len(delta["files"]))
        for item in manifest["files"]:
            self.assertTrue(item["key"].startswith(self.prefix + "/objects/"))
        db = duckdb.connect()
        db.execute(latest_sql(manifest, lambda key: str(self.backend.root / key)))
        self.assertEqual(
            db.sql("SELECT name FROM derivations").fetchall(), [("second",)]
        )
        self.assertEqual(
            db.sql(
                "SELECT name FROM temporal_derivations ORDER BY _revision"
            ).fetchall(),
            [("first",), ("second",)],
        )
        self.assertEqual(db.sql("SELECT count(*) FROM edges").fetchone(), (0,))
        sql, _ = self.backend.get(index["sql"])
        self.assertIn(f"https://example.test/{self.prefix}/objects/".encode(), sql)
        self.assertNotIn(b"https://example.test/private/", sql)
        db.close()

    def test_log_byte_total_and_exact_fragments_across_generations(self):
        self.source.execute(
            "INSERT INTO attempts(id,campaign,kind,targets,state,created,spec,offset) VALUES('log-a','c','build','[]','finished',1,'{}',0)"
        )
        self.source.commit()
        log = self.publisher.experiment / "attempts/log-a/stderr.log"
        log.parent.mkdir(parents=True)
        log.write_bytes(b"ab\ncd\nef")
        self.publisher.log_bytes = 3
        for _ in range(3):
            self.publisher.publish()
            self.share()
        data, _ = self.backend.get(f"{self.prefix}/index.json")
        index = json.loads(data)
        self.assertEqual(index["archived_log_bytes"], 8)
        data, _ = self.backend.get(index["manifest"])
        db = duckdb.connect()
        db.execute(
            latest_sql(json.loads(data), lambda key: str(self.backend.root / key))
        )
        rows = db.sql(
            'SELECT start, "end", raw FROM build_logs ORDER BY start'
        ).fetchall()
        self.assertEqual(rows, [(0, 3, b"ab\n"), (3, 6, b"cd\n"), (6, 8, b"ef")])
        db.close()

    def test_copy_failure_does_not_advance_pointer_and_retries(self):
        self.share()
        key = f"{self.prefix}/index.json"
        old, _ = self.backend.get(key)
        self.source.execute("UPDATE derivations SET name='new'")
        self.source.commit()
        self.publisher.publish()
        with patch.object(
            self.backend, "copy_immutable", side_effect=OSError("failed copy")
        ):
            with self.assertRaisesRegex(OSError, "failed copy"):
                self.share()
        self.assertEqual(self.backend.get(key)[0], old)
        self.assertEqual(self.share()["copied"], 1)
        self.assertNotEqual(self.backend.get(key)[0], old)

    def test_invalid_prefix_and_source_checksum_are_rejected(self):
        for prefix in ("share/*/v1", "campaign/v1", "share/short/v1"):
            with self.assertRaises(ValueError):
                publish_share(self.backend, "private", prefix, "https://example.test")
        data, _ = self.backend.get("private/latest.json")
        pointer = json.loads(data)
        data, _ = self.backend.get(pointer["manifest"])
        item = json.loads(data)["files"][0]
        (self.backend.root / item["key"]).write_bytes(b"corrupt")
        with self.assertRaisesRegex(ValueError, "checksum mismatch"):
            self.share()
        self.assertIsNone(self.backend.get(f"{self.prefix}/index.json")[0])

    def test_s3_copy_is_conditional_and_rejects_collisions(self):
        backend = object.__new__(S3Backend)
        backend.bucket = "bucket"
        backend.client = Mock()
        digest = "a" * 64
        original = {
            "Metadata": {"sha256": digest},
            "ContentLength": 37,
            "ETag": '"source-etag"',
        }
        missing = ClientError({"Error": {"Code": "404"}}, "HeadObject")
        backend.client.head_object.side_effect = [original, missing]
        backend.copy_immutable("source", "dest", digest)
        request = backend.client.copy_object.call_args.kwargs
        self.assertEqual(request["CopySourceIfMatch"], original["ETag"])
        self.assertEqual(request["CopySource"], {"Bucket": "bucket", "Key": "source"})
        backend.client.copy_object.reset_mock()
        backend.client.head_object.side_effect = [original, original]
        backend.copy_immutable("source", "dest", digest)
        backend.client.copy_object.assert_not_called()
        backend.client.head_object.side_effect = [
            original,
            {**original, "ContentLength": 38},
        ]
        with self.assertRaisesRegex(ValueError, "collision"):
            backend.copy_immutable("source", "dest", digest)
        backend.client.head_object.side_effect = [
            {**original, "Metadata": {"sha256": "wrong"}}
        ]
        with self.assertRaisesRegex(ValueError, "source object checksum"):
            backend.copy_immutable("source", "dest", digest)


if __name__ == "__main__":
    unittest.main()
