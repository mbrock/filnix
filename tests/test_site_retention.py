"""The public retention plan must never delete a live or recent snapshot."""
from datetime import datetime, timedelta, timezone
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


PRUNE = Path(__file__).resolve().parents[1] / "deploy/site/prune.py"


class SiteRetention(unittest.TestCase):
    def test_retention_protects_current_newest_five_and_recent_partial_uploads(self):
        now = datetime.now(timezone.utc)
        current = "a" * 40
        expired = "b" * 40
        partial = "c" * 40
        keys = []

        def obj(key, age):
            keys.append({"Key": key, "LastModified": (now - age).isoformat(), "Size": 13})

        # The current release is older than the retention window and is not
        # in the five newest. A newer object protects a whole partial upload.
        obj(f"releases/{current}/index.html", timedelta(days=20))
        obj(f"releases/{expired}/index.html", timedelta(days=19))
        obj(f"releases/{expired}/commit.txt", timedelta(days=19))
        obj(f"releases/{partial}/index.html", timedelta(days=18))
        obj(f"releases/{partial}/large.bin", timedelta(hours=23))
        obj("current.json", timedelta(days=30))
        obj("downloads/permanent.bin", timedelta(days=30))
        obj("releases/not-a-commit/index.html", timedelta(days=30))
        # Five recent-ish snapshots all older than 24 hours: retain by count.
        for i in range(5):
            obj(f"releases/{i:040x}/index.html", timedelta(days=2 + i))
        # The partial upload occupies one newest slot, leaving the oldest
        # of those five eligible for deletion; the live SHA remains protected.
        with tempfile.TemporaryDirectory() as tmp:
            inventory = Path(tmp) / "inventory.json"
            inventory.write_text(json.dumps({"Contents": keys}))
            run = subprocess.run(["python3", str(PRUNE), str(inventory), current,
                                  "--endpoint-url", "https://unused.invalid", "--dry-run"],
                                 capture_output=True, text=True, check=True)
            plan = json.loads(run.stdout)
            self.assertEqual(plan["delete"], sorted([
                f"releases/{expired}/index.html", f"releases/{expired}/commit.txt",
                f"releases/{4:040x}/index.html",
            ]))
            self.assertEqual(plan["retained_releases"], 6)

    def test_bulk_cleanup_and_partial_failure(self):
        # A file-backed S3 deletion endpoint exercises the CLI without
        # touching R2. More than one batch and long keys catch size limits.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            aws = root / "aws"
            aws.write_text(f"#!{sys.executable}\n" + '''
import json, os, sys
from pathlib import Path
batch = json.load(open(sys.argv[sys.argv.index("--delete") + 1][7:]))["Objects"]
assert len(batch) <= 1000
if os.environ.get("FAIL_DELETE"):
    print(json.dumps({"Errors": [{"Code": "AccessDenied"}]}))
else:
    state = Path(os.environ["BUCKET_STATE"])
    remove = {o["Key"] for o in batch}
    state.write_text(json.dumps([k for k in json.loads(state.read_text()) if k not in remove]))
    print("{}")
''')
            aws.chmod(0o755)
            current = "a" * 40
            old = datetime.now(timezone.utc) - timedelta(days=10)
            objects = [{"Key": f"releases/{'b' * 40}/{'x' * 200}/{i}",
                        "LastModified": old.isoformat()} for i in range(1007)]
            protected = [f"releases/{i:040x}/index.html" for i in range(5)]
            protected += [f"releases/{current}/index.html", "current.json"]
            objects += [{"Key": k, "LastModified": (old + timedelta(days=1)).isoformat()}
                        for k in protected]
            inventory = root / "inventory.json"
            inventory.write_text(json.dumps({"Contents": objects}))
            state = root / "state.json"
            initial = [o["Key"] for o in objects]
            state.write_text(json.dumps(initial))
            command = [sys.executable, str(PRUNE), str(inventory), current,
                       "--endpoint-url", "https://unused.invalid"]
            env = {**os.environ, "PATH": f"{tmp}:{os.environ['PATH']}", "BUCKET_STATE": str(state)}
            failed = subprocess.run(command, env={**env, "FAIL_DELETE": "1"}, capture_output=True)
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn(b"AccessDenied", failed.stderr)
            self.assertEqual(json.loads(state.read_text()), initial)
            subprocess.run(command, env=env, capture_output=True, check=True)
            self.assertEqual(sorted(json.loads(state.read_text())), sorted(protected))

    def test_invalid_current_cannot_authorize_deletion(self):
        run = subprocess.run(["python3", str(PRUNE), "/nonexistent", "not-a-sha",
                              "--endpoint-url", "https://unused.invalid"], capture_output=True)
        self.assertNotEqual(run.returncode, 0)
        self.assertIn(b"current must be a full commit SHA", run.stderr)


if __name__ == "__main__":
    unittest.main()
