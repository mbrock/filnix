#!/usr/bin/env python3
"""Prune expired site snapshots after a successful, serialized promotion."""
import argparse
from datetime import datetime, timedelta, timezone
import json
import re
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inventory")
    parser.add_argument("current")
    parser.add_argument("--bucket", default="filnix-site")
    parser.add_argument("--endpoint-url", required=True)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    if not re.fullmatch(r"[0-9a-f]{40}", args.current):
        parser.error("current must be a full commit SHA")
    with open(args.inventory) as f:
        inventory = json.load(f)
    releases = {}
    for obj in inventory.get("Contents", []):
        match = re.match(r"^releases/([0-9a-f]{40})/", obj["Key"])
        if match:
            releases.setdefault(match[1], []).append(obj)
    # Use the youngest object, including partial uploads. Protect recent
    # readers and in-flight browser checks, not just successfully promoted trees.
    newest = {sha: max(datetime.fromisoformat(o["LastModified"].replace("Z", "+00:00"))
                       for o in objects) for sha, objects in releases.items()}
    keep = set(sorted(newest, key=newest.get, reverse=True)[:5]) | {args.current}
    cutoff = datetime.now(timezone.utc) - timedelta(days=1)
    keys = sorted(o["Key"] for sha, objects in releases.items()
                  if sha not in keep and newest[sha] < cutoff for o in objects)
    print(json.dumps({"delete": keys if args.dry_run else len(keys), "retained_releases": len(releases) -
                      sum(sha not in keep and date < cutoff for sha, date in newest.items())}), flush=True)
    if args.dry_run:
        return
    for start in range(0, len(keys), 1000):
        batch = {"Objects": [{"Key": key} for key in keys[start:start + 1000]], "Quiet": True}
        number = start // 1000 + 1
        # Record the exact request before any side effects, including a failure
        # or interrupted response. Do not retry an uncertain batch here.
        print(json.dumps({"batch": number, "requested": batch["Objects"]}), flush=True)
        with tempfile.NamedTemporaryFile(mode="w") as payload:
            json.dump(batch, payload)
            payload.flush()
            result = subprocess.run(
                ["aws", "--endpoint-url", args.endpoint_url, "s3api", "delete-objects",
                 "--bucket", args.bucket, "--delete", f"file://{payload.name}", "--output", "json"],
                capture_output=True, text=True)
        print(json.dumps({"batch": number, "returncode": result.returncode,
                          "stdout": result.stdout, "stderr": result.stderr}), flush=True)
        if result.returncode:
            raise SystemExit(f"R2 retention batch {number} failed; inspect the logged response before retrying")
        # S3 multi-delete can return HTTP success with individual failures.
        # AWS CLI emits no output for an empty quiet-success response, even
        # with --output json. Nonempty invalid output is not evidence of success.
        try:
            response = json.loads(result.stdout) if result.stdout.strip() else {}
        except json.JSONDecodeError:
            raise SystemExit(f"R2 retention batch {number} returned invalid JSON; inspect the log before retrying")
        if not isinstance(response, dict) or not isinstance(response.get("Errors", []), list):
            raise SystemExit(f"R2 retention batch {number} returned an invalid response; inspect the log before retrying")
        errors = response.get("Errors", [])
        if errors:
            raise SystemExit(f"R2 retention failed: {errors}")
        print(json.dumps({"batch": number, "completed": len(batch["Objects"])}), flush=True)


if __name__ == "__main__":
    main()
