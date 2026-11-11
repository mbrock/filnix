#!/usr/bin/env bash
# Called only by the trusted main-branch job, serialized with other promotes.
# AWS credentials are object-only, restricted to this bucket.
set -euo pipefail
bucket=filnix-site
prefix="releases/$GITHUB_SHA/"
aws_args=(--endpoint-url "https://d66b4fdcf8b2d4b0949d7fa3518b9b58.r2.cloudflarestorage.com")

# A failed read (other than an absent object) stops publication. In
# particular, a temporary network/auth failure cannot erase a newer release.
aws "${aws_args[@]}" s3api list-objects-v2 --bucket "$bucket" --prefix current.json --output json > bucket.json
if python3 -c 'import json,sys; sys.exit(not any(o["Key"]=="current.json" for o in json.load(open("bucket.json")).get("Contents",[])))'; then
  aws "${aws_args[@]}" s3 cp "s3://$bucket/current.json" current.json --no-progress
  live=$(python3 -c 'import json; print(json.load(open("current.json"))["sha"])')
  [[ $live =~ ^[0-9a-f]{40}$ ]] || { echo "Invalid live SHA" >&2; exit 1; }
  status=$(gh api "repos/$GITHUB_REPOSITORY/compare/$live...$GITHUB_SHA" --jq .status)
  case $status in
    behind|identical)
      echo "Keeping newer or identical live release $live" | tee -a "$GITHUB_STEP_SUMMARY"
      echo "promoted=false" >> "$GITHUB_OUTPUT"
      exit 0 ;;
  esac
fi

# Only inventory this upload on the fast path. Whole-bucket retention is
# scheduled separately under the same promotion lock.
python3 - <<'PY'
from pathlib import Path
new = sum(p.stat().st_size for p in Path("_site").rglob("*") if p.is_file())
print(f"This release {new:,} bytes")
PY

aws "${aws_args[@]}" s3 sync _site "s3://$bucket/$prefix" --no-progress
aws "${aws_args[@]}" s3api list-objects-v2 --bucket "$bucket" --prefix "$prefix" --output json > uploaded.json
python3 - <<'PY'
import json, os
from pathlib import Path
prefix = f'releases/{os.environ["GITHUB_SHA"]}/'
expected = {prefix + str(p.relative_to("_site")): p.stat().st_size
            for p in Path("_site").rglob("*") if p.is_file()}
actual = {o["Key"]: o["Size"] for o in json.load(open("uploaded.json")).get("Contents", [])}
if expected != actual:
    raise SystemExit("Uploaded object paths/sizes do not match the complete site; not promoting")
print(f"Verified {len(expected)} objects, {sum(expected.values()):,} bytes")
PY
test "$(aws "${aws_args[@]}" s3 cp "s3://$bucket/${prefix}commit.txt" - --no-progress)" = "$GITHUB_SHA"

# R2 object replacement is atomic. Failed/incomplete uploads never get here.
printf '{"sha":"%s"}\n' "$GITHUB_SHA" > current.json
aws "${aws_args[@]}" s3 cp current.json "s3://$bucket/current.json" \
  --content-type application/json --cache-control no-store --no-progress
echo "promoted=true" >> "$GITHUB_OUTPUT"
echo "Published https://filnix.org/ (release $GITHUB_SHA)" >> "$GITHUB_STEP_SUMMARY"
echo "@@site-live $(date -u +%FT%TZ) $GITHUB_SHA"
