#!/usr/bin/env python3
"""Publish a complete site to R2 as content-addressed blobs + release manifest.

Stores unique file bodies under blobs/<sha256>, writes a single immutable
releases/<sha>/manifest.json mapping canonical paths to [sha256, size, type],
verifies every referenced blob and the manifest, and atomically replaces
current.json. Only blobs absent from R2 are uploaded.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import mimetypes
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


CONTENT_TYPES = {
    ".html": "text/html; charset=utf-8",
    ".css": "text/css; charset=utf-8",
    ".js": "text/javascript; charset=utf-8",
    ".mjs": "text/javascript; charset=utf-8",
    ".json": "application/json; charset=utf-8",
    ".xml": "application/xml; charset=utf-8",
    ".txt": "text/plain; charset=utf-8",
    ".md": "text/markdown; charset=utf-8",
    ".svg": "image/svg+xml",
    ".png": "image/png",
    ".jpg": "image/jpeg",
    ".jpeg": "image/jpeg",
    ".webp": "image/webp",
    ".ico": "image/x-icon",
    ".woff2": "font/woff2",
    ".wasm": "application/wasm",
    ".pdf": "application/pdf",
    ".v": "text/plain; charset=utf-8",
    ".pl": "text/plain; charset=utf-8",
    ".nix": "text/plain; charset=utf-8",
    ".c": "text/plain; charset=utf-8",
    ".h": "text/plain; charset=utf-8",
    ".tsv": "text/tab-separated-values; charset=utf-8",
}


def content_type_for(path: Path) -> str:
    ext = path.suffix.lower()
    if ext in CONTENT_TYPES:
        return CONTENT_TYPES[ext]
    guessed, _ = mimetypes.guess_type(path.name)
    if guessed:
        if guessed.startswith("text/") and "charset=" not in guessed:
            return f"{guessed}; charset=utf-8"
        return guessed
    return "application/octet-stream"


def sha256_file(path: Path) -> tuple[str, int]:
    h = hashlib.sha256()
    size = 0
    with path.open("rb") as fh:
        while chunk := fh.read(1 << 20):
            h.update(chunk)
            size += len(chunk)
    return h.hexdigest(), size


def aws_cmd(endpoint: str, *args: str) -> list[str]:
    return ["aws", "--endpoint-url", endpoint, *args]


def list_prefix(endpoint: str, bucket: str, prefix: str) -> dict[str, int]:
    """List all objects under prefix via paginated s3api list-objects-v2."""
    found: dict[str, int] = {}
    token = None
    while True:
        cmd = aws_cmd(endpoint, "s3api", "list-objects-v2", "--no-paginate",
                      "--bucket", bucket, "--prefix", prefix, "--output", "json")
        if token:
            cmd.extend(["--continuation-token", token])
        out = subprocess.run(cmd, check=True, capture_output=True, text=True).stdout
        data = json.loads(out) if out.strip() else {}
        for obj in data.get("Contents", []):
            found[obj["Key"]] = int(obj["Size"])
        if not data.get("IsTruncated"):
            break
        token = data["NextContinuationToken"]
    return found


def scan_site(site: Path) -> tuple[dict[str, list], dict[str, tuple[Path, int]]]:
    """Return (manifest_files, unique_blobs[sha256 -> (path, size)])."""
    files: dict[str, list] = {}
    blobs: dict[str, tuple[Path, int]] = {}
    for p in sorted(site.rglob("*")):
        if not p.is_file():
            continue
        rel = "/" + p.relative_to(site).as_posix()
        digest, size = sha256_file(p)
        files[rel] = [digest, size, content_type_for(p)]
        blobs.setdefault(digest, (p, size))
    return files, blobs


def publish(site: Path, sha: str, bucket: str, endpoint: str,
            skip_live_check: bool = False) -> bool:
    if not (len(sha) == 40 and all(c in "0123456789abcdef" for c in sha)):
        raise SystemExit(f"Invalid commit SHA: {sha}")
    commit_file = site / "commit.txt"
    if not commit_file.is_file() or commit_file.read_text().strip() != sha:
        raise SystemExit("Site commit.txt does not match release SHA; not publishing")

    # Never replace a newer or identical live release.
    if not skip_live_check:
        current_objs = list_prefix(endpoint, bucket, "current.json")
        if "current.json" in current_objs:
            raw = subprocess.run(
                aws_cmd(endpoint, "s3", "cp", f"s3://{bucket}/current.json", "-", "--no-progress"),
                check=True, capture_output=True, text=True,
            ).stdout
            live = json.loads(raw)["sha"]
            if not (len(live) == 40 and all(c in "0123456789abcdef" for c in live)):
                raise SystemExit("Invalid live SHA in current.json")
            repo = os.environ["GITHUB_REPOSITORY"]
            status = subprocess.run(
                ["gh", "api", f"repos/{repo}/compare/{live}...{sha}", "--jq", ".status"],
                check=True, capture_output=True, text=True,
            ).stdout.strip()
            if status in ("behind", "identical"):
                print(f"Keeping newer or identical live release {live}")
                return False

    files, blobs = scan_site(site)
    total_bytes = sum(entry[1] for entry in files.values())
    unique_bytes = sum(sz for _, sz in blobs.values())
    print(f"This release: {len(files)} paths ({total_bytes:,} bytes), "
          f"{len(blobs)} unique blobs ({unique_bytes:,} bytes)")

    existing = list_prefix(endpoint, bucket, "blobs/")
    missing = {
        h: (p, sz) for h, (p, sz) in blobs.items()
        if existing.get(f"blobs/{h}") != sz
    }
    upload_bytes = sum(sz for _, sz in missing.values())
    print(f"Delta upload: {len(missing)} new blobs ({upload_bytes:,} bytes), "
          f"{len(blobs) - len(missing)} reused from R2")

    if missing:
        with tempfile.TemporaryDirectory() as tmp:
            stage = Path(tmp)
            for h, (src, _) in missing.items():
                dst = stage / h
                try:
                    os.link(src, dst)
                except OSError:
                    shutil.copy2(src, dst)
            subprocess.run(
                aws_cmd(endpoint, "s3", "sync", str(stage), f"s3://{bucket}/blobs/", "--no-progress"),
                check=True,
            )

    # Verify every referenced blob exists in R2 with the exact expected size.
    verified = list_prefix(endpoint, bucket, "blobs/") if missing else existing
    bad = [h for h, (_, sz) in blobs.items() if verified.get(f"blobs/{h}") != sz]
    if bad:
        raise SystemExit(f"Missing or mismatched blobs in R2 ({len(bad)}, e.g. {bad[0]}); not promoting")
    print(f"Verified {len(blobs)} blobs in R2")

    manifest = {
        "version": 1,
        "sha": sha,
        "created": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "files": files,
    }
    manifest_key = f"releases/{sha}/manifest.json"
    with tempfile.TemporaryDirectory() as tmp:
        mpath = Path(tmp) / "manifest.json"
        mpath.write_text(json.dumps(manifest, separators=(",", ":")), encoding="utf-8")
        manifest_size = mpath.stat().st_size
        subprocess.run(
            aws_cmd(endpoint, "s3", "cp", str(mpath), f"s3://{bucket}/{manifest_key}",
                    "--content-type", "application/json", "--no-progress"),
            check=True,
        )
        # Read back and verify the immutable manifest before promoting.
        check_raw = subprocess.run(
            aws_cmd(endpoint, "s3", "cp", f"s3://{bucket}/{manifest_key}", "-", "--no-progress"),
            check=True, capture_output=True, text=True,
        ).stdout
        checked = json.loads(check_raw)
        if checked.get("sha") != sha or len(checked.get("files", {})) != len(files):
            raise SystemExit("Uploaded manifest verification failed; not promoting")

        cur = Path(tmp) / "current.json"
        cur.write_text(json.dumps({"sha": sha}) + "\n", encoding="utf-8")
        subprocess.run(
            aws_cmd(endpoint, "s3", "cp", str(cur), f"s3://{bucket}/current.json",
                    "--content-type", "application/json", "--cache-control", "no-store", "--no-progress"),
            check=True,
        )
    print(f"Promoted manifest release {sha} ({manifest_size:,} byte manifest)")
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site", type=Path)
    parser.add_argument("sha")
    parser.add_argument("--bucket", default="filnix-site")
    parser.add_argument("--endpoint-url", required=True)
    parser.add_argument("--skip-live-check", action="store_true")
    args = parser.parse_args()
    promoted = publish(args.site, args.sha, args.bucket, args.endpoint_url, args.skip_live_check)
    gh_out = os.environ.get("GITHUB_OUTPUT")
    if gh_out:
        with open(gh_out, "a", encoding="utf-8") as fh:
            fh.write(f"promoted={'true' if promoted else 'false'}\n")
    if promoted:
        summary = os.environ.get("GITHUB_STEP_SUMMARY")
        if summary:
            with open(summary, "a", encoding="utf-8") as fh:
                fh.write(f"Published https://filnix.org/ (release {args.sha})\n")
        print(f"@@site-live {datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')} {args.sha}")


if __name__ == "__main__":
    main()
