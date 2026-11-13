#!/usr/bin/env bash
# Make a fresh cutover candidate from latest main, then run every read-only gate.
# No commit, push, release, or deployment is performed by this command.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
out=${1:?usage: run.sh NEW_OUTPUT_DIRECTORY [BASE_REF]}
base=${2:-origin/main}
jobs=${PE_JOBS:-8}
if [ -e "$out" ]; then
  echo "Refusing existing output directory: $out" >&2
  exit 2
fi
git -C "$repo" fetch origin main
revision=$(git -C "$repo" rev-parse "$base")
if ! git -C "$repo" merge-base --is-ancestor "$revision" HEAD; then
  echo 'FAIL baseline integration: merge latest main into the pipeline branch first' >&2
  exit 1
fi
mkdir -p "$out"
out=$(cd "$out" && pwd)
printf 'baseline=%s\npipeline=%s\n' "$revision" "$(git -C "$repo" rev-parse HEAD)" >"$out/revisions.txt"
git -C "$repo" diff -- nanofil/rocq/scripts/proof-eng >"$out/pipeline.diff"
mkdir "$out/source"
git -C "$repo" archive "$revision" nanofil/rocq/glibc | tar -x -C "$out/source"
before=$out/source/nanofil/rocq/glibc
"$here/../materialize.sh" "$out/worktree" >"$out/materialize.log" 2>&1
after=$out/worktree/nanofil/rocq/glibc
# materialize.sh starts from branch HEAD; replace only its glibc input with
# the exact fetched main revision rather than relying on a recent branch merge.
"$here/../apply.sh" "$before" "$after" >"$out/apply.log" 2>&1
git -C "$out/worktree" add -A nanofil/rocq/glibc
. "$here/../env.sh"
bash "$here/plugin.sh" "$out/plugin" >"$out/plugin.log" 2>&1
status=0
run() {
  local name=$1
  shift
  if python3 "$repo/nanofil/tests/watch.py" --label "$name" --warn-after 900 --timeout 7200 -- \
      "$@" >"$out/$name.log" 2>&1; then
    echo "PASS $name" | tee -a "$out/verdicts.txt"
  else
    local code=$?
    echo "FAIL $name (exit $code; $out/$name.log)" | tee -a "$out/verdicts.txt"
    status=1
  fi
}
run cache-preflight python3 "$out/worktree/scripts/ci-cache-check.py" --flake "$out/worktree" \
  packages.x86_64-linux.filcc-staging packages.x86_64-linux.site-swipl
run before-build bash "$here/../build.sh" "$before" "$jobs"
run after-build bash "$here/../build.sh" "$after" "$jobs"
run statements python3 "$here/check.py" statements "$before" "$after" \
  --plugin "$out/plugin" --output "$out/statements" --jobs "${PE_QUERY_JOBS:-2}"
run before-audits python3 "$here/audit.py" "$before" --output "$out/before-audits"
layout=${PE_AUDIT_LAYOUT:-$out/flat-layout}
if [ -z "${PE_AUDIT_LAYOUT:-}" ]; then
  run audit-layout bash "$here/prepare-layout.sh" "$before" "$layout"
fi
run after-audits python3 "$here/audit.py" "$after" --layout "$layout" --output "$out/after-audits"
run audit-comparison python3 "$here/compare-audits.py" "$out/before-audits/report.json" "$out/after-audits/report.json"
run glibc nix build -L --no-link --keep-going --max-jobs "$jobs" "$out/worktree#checks.x86_64-linux.nanofil-glibc"
run glibc-units nix build -L --no-link -f "$out/worktree/nanofil/survey/glibc/regress.nix" units
run docs nix build -L --no-link "$out/worktree#checks.x86_64-linux.nanofil-docs"
run site nix build -L --no-link --max-jobs "$jobs" "$out/worktree#site"
# These local unit gates are also run by pages.yml; publication is not a gate.
run site-python python3 -m unittest discover -s "$out/worktree/tests" -p 'test_site_*.py'
run site-worker node --test "$out/worktree/deploy/site/worker.test.mjs"
if [ "$base" != origin/main ]; then
  echo "FAIL freshness (explicit baseline is not origin/main)" | tee -a "$out/verdicts.txt"
  status=1
else
  git -C "$repo" fetch origin main
  if [ "$(git -C "$repo" rev-parse origin/main)" != "$revision" ]; then
    echo "FAIL freshness (main advanced during checks)" | tee -a "$out/verdicts.txt"
    status=1
  fi
fi
echo "Cutover exit status: $status" | tee -a "$out/verdicts.txt"
exit "$status"
