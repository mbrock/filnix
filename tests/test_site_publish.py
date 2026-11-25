"""Content-addressed R2 publication uploads only changed blobs and verifies before promoting."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


PUBLISH = Path(__file__).resolve().parents[1] / "deploy/site/publish_manifest.py"

MOCK_AWS = f"""#!{sys.executable}
import json, os, shutil, sys
from pathlib import Path

root = Path(os.environ["MOCK_R2"])
log = Path(os.environ["MOCK_LOG"])
args = sys.argv[1:]
# Strip --endpoint-url URL
while "--endpoint-url" in args:
    i = args.index("--endpoint-url")
    del args[i:i+2]

if args[:2] == ["s3api", "list-objects-v2"]:
    prefix = args[args.index("--prefix") + 1]
    contents = []
    for p in sorted(root.rglob("*")):
        if p.is_file():
            key = p.relative_to(root).as_posix()
            if key.startswith(prefix):
                contents.append({{"Key": key, "Size": p.stat().st_size}})
    print(json.dumps({{"Contents": contents, "IsTruncated": False}}))
elif args[:2] == ["s3", "sync"]:
    src = Path(args[2])
    dst_uri = args[3]
    assert dst_uri.startswith("s3://")
    prefix = dst_uri.split("/", 3)[3].rstrip("/")
    copied = []
    for p in sorted(src.iterdir()):
        if p.is_file():
            if os.environ.get("DROP_UPLOAD") == "1":
                continue
            target = root / prefix / p.name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(p, target)
            copied.append(p.name)
    with log.open("a") as fh:
        fh.write(json.dumps({{"sync": copied}}) + "\\n")
elif args[:2] == ["s3", "cp"]:
    src, dst = args[2], args[3]
    if dst == "-":
        key = src.split("/", 3)[3]
        sys.stdout.buffer.write((root / key).read_bytes())
    else:
        key = dst.split("/", 3)[3]
        target = root / key
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, target)
else:
    raise SystemExit(f"Unsupported mock aws invocation: {{args}}")
"""


class SiteManifestPublish(unittest.TestCase):
    def test_delta_upload_and_missing_blob_protection(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            bin_dir = base / "bin"
            bin_dir.mkdir()
            aws = bin_dir / "aws"
            aws.write_text(MOCK_AWS)
            aws.chmod(0o755)
            r2 = base / "r2"
            r2.mkdir()
            log = base / "log.jsonl"
            env = {
                **os.environ,
                "PATH": f"{bin_dir}:{os.environ['PATH']}",
                "MOCK_R2": str(r2),
                "MOCK_LOG": str(log),
            }

            sha1 = "a" * 40
            site = base / "site"
            (site / "docs").mkdir(parents=True)
            (site / "index.html").write_text("<h1>home</h1>")
            (site / "style.css").write_text("body{color:black}")
            (site / "docs" / "a.html").write_text("<p>unchanged</p>")
            (site / "docs" / "dup.html").write_text("<p>unchanged</p>")
            (site / "commit.txt").write_text(sha1 + "\n")

            # First publish uploads 4 unique blobs (a.html and dup.html deduplicate).
            run1 = subprocess.run(
                [sys.executable, str(PUBLISH), str(site), sha1,
                 "--endpoint-url", "https://unused.invalid", "--skip-live-check"],
                env=env, capture_output=True, text=True, check=True,
            )
            self.assertIn("4 new blobs", run1.stdout)
            cur = json.loads((r2 / "current.json").read_text())
            self.assertEqual(cur, {"sha": sha1})
            manifest1 = json.loads((r2 / f"releases/{sha1}/manifest.json").read_text())
            self.assertEqual(manifest1["files"]["/docs/a.html"][0], manifest1["files"]["/docs/dup.html"][0])
            self.assertEqual(manifest1["files"]["/style.css"][2], "text/css; charset=utf-8")

            # Second publish changes only index.html + commit.txt -> uploads only 2 blobs!
            sha2 = "b" * 40
            (site / "index.html").write_text("<h1>home v2</h1>")
            (site / "commit.txt").write_text(sha2 + "\n")
            run2 = subprocess.run(
                [sys.executable, str(PUBLISH), str(site), sha2,
                 "--endpoint-url", "https://unused.invalid", "--skip-live-check"],
                env=env, capture_output=True, text=True, check=True,
            )
            self.assertIn("2 new blobs", run2.stdout)
            self.assertIn("2 reused from R2", run2.stdout)
            self.assertEqual(json.loads((r2 / "current.json").read_text()), {"sha": sha2})
            syncs = [json.loads(line)["sync"] for line in log.read_text().splitlines()]
            self.assertEqual([len(s) for s in syncs], [4, 2])

            # If sync drops blobs, verification refuses to promote current.json.
            sha3 = "c" * 40
            (site / "index.html").write_text("<h1>broken upload</h1>")
            (site / "commit.txt").write_text(sha3 + "\n")
            run3 = subprocess.run(
                [sys.executable, str(PUBLISH), str(site), sha3,
                 "--endpoint-url", "https://unused.invalid", "--skip-live-check"],
                env={**env, "DROP_UPLOAD": "1"}, capture_output=True, text=True,
            )
            self.assertNotEqual(run3.returncode, 0)
            self.assertIn("Missing or mismatched blobs", run3.stderr)
            self.assertEqual(json.loads((r2 / "current.json").read_text()), {"sha": sha2})


if __name__ == "__main__":
    unittest.main()
