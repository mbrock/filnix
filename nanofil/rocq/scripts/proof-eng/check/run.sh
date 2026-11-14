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
cp -r "$before" "$out/name-gate-tree"
if python3 -I "$here/../stages/10-flatten.py" "$out/name-gate-tree" \
    --name-report "$out/flatten-names.json" >"$out/name-gate.log" 2>&1; then
  echo 'PASS name-gate' | tee -a "$out/verdicts.txt"
else
  echo "FAIL name-gate (see $out/name-gate.log and flatten-names.json)" | tee -a "$out/verdicts.txt"
  { printf '# Cutover blocked by duplicate names\n\n```json\n'; cat "$out/flatten-names.json"; printf '\n```\n'; } >"$out/cutover-packet.md"
  exit 1
fi
rm -rf "$out/name-gate-tree"
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
run abstract-general bash "$here/../abstract-general.sh" "$after" "$out/abstract-general" "$jobs"
run runtime-partition python3 "$here/check.py" partition "$before" --output "$out/runtime-partition"
if [ -s "$out/runtime-partition/general-targets.txt" ]; then
  run abstract-apply env PE_RUNTIME=abstract \
    PE_PROGRAM_TARGETS="$(cat "$out/runtime-partition/general-targets.txt")" \
    bash "$here/../apply.sh" "$before" "$out/abstract"
else
  echo 'FAIL abstract-apply (no compiler-derived original general targets)' | tee -a "$out/verdicts.txt"
  status=1
fi
if bash "$here/../build.sh" "$out/abstract" "$jobs" >"$out/abstract-build.log" 2>&1; then
  echo 'PASS abstract-build' | tee -a "$out/verdicts.txt"
else
  echo 'PARTIAL abstract-build (statement check requires every original general file)' | tee -a "$out/verdicts.txt"
fi
run tactics-boundary bash "$here/tactics-boundary.sh" "$before" "$out/tactics-boundary"
run tactics-before-build bash "$here/../build.sh" "$out/tactics-boundary/before" "$jobs"
run tactics-after-build bash "$here/../build.sh" "$out/tactics-boundary/after" "$jobs"
run packet python3 "$here/packet.py" "$after" --output "$out/cutover-packet.md" \
  --stage30-before "$out/tactics-boundary/before" --stage30-after "$out/tactics-boundary/after" \
  --plugin "$out/plugin"
stage50_evidence=()
if [ -f "$here/../stages/50-program.py" ]; then
  run packet-abstract python3 "$here/packet.py" "$out/abstract" --stage50-only \
    --output "$out/abstract-packet.md" --interpreter-evidence "$out/cutover-packet.stage50.json"
  for receipt in "$out/cutover-packet.stage50.json" "$out/abstract-packet.stage50.json"; do
    if [ -f "$receipt" ]; then
      stage50_evidence+=(--stage50-evidence "$receipt")
    fi
  done
fi
run statements python3 "$here/check.py" statements "$before" "$after" \
  --abstract-after "$out/abstract" --plugin "$out/plugin" --output "$out/statements" --jobs "${PE_QUERY_JOBS:-2}" \
  "${stage50_evidence[@]}"
run before-audits python3 "$here/audit.py" "$before" --output "$out/before-audits"
layout=${PE_AUDIT_LAYOUT:-$out/flat-layout}
if [ -z "${PE_AUDIT_LAYOUT:-}" ]; then
  run audit-layout bash "$here/prepare-layout.sh" "$before" "$layout"
fi
run after-audits python3 "$here/audit.py" "$after" --layout "$layout" --output "$out/after-audits"
run hello-abstract bash "$here/hello-abstract.sh" "$before" "$out/hello-abstract" "$out/abstract"
run audit-comparison python3 "$here/compare-audits.py" "$out/before-audits/report.json" "$out/after-audits/report.json" \
  --hello-abstract "$out/hello-abstract/audit/report.json" "${stage50_evidence[@]}"
run glibc nix build -L --no-link --keep-going --max-jobs "$jobs" "$out/worktree#checks.x86_64-linux.nanofil-glibc"
run glibc-units nix build -L --no-link -f "$out/worktree/nanofil/survey/glibc/regress.nix" units
run docs nix build -L --no-link "$out/worktree#checks.x86_64-linux.nanofil-docs"
run site nix build -L --no-link --max-jobs "$jobs" "$out/worktree#site"
# These local unit gates are also run by pages.yml; publication is not a gate.
run site-python python3 -m unittest discover -s "$out/worktree/tests" -p 'test_site_*.py'
run site-worker node --test "$out/worktree/deploy/site/worker.test.mjs"
if [ "$base" != origin/main ]; then
  echo "PASS pinned-baseline ($revision; no latest-main freshness claim)" | tee -a "$out/verdicts.txt"
else
  git -C "$repo" fetch origin main
  if [ "$(git -C "$repo" rev-parse origin/main)" != "$revision" ]; then
    echo "FAIL freshness (main advanced during checks)" | tee -a "$out/verdicts.txt"
    status=1
  fi
fi
echo "Cutover exit status: $status" | tee -a "$out/verdicts.txt"
{
  printf '\n## Local cutover verdicts\n\n```text\n'
  cat "$out/revisions.txt" "$out/verdicts.txt"
  printf '```\n\n## Flattened-name inventory\n\n```json\n'
  cat "$out/flatten-names.json"
  printf '```\n\n## Complete statement differences\n\n```text\n'
  cat "$out/statements/report.txt"
  printf '```\n'
} >>"$out/cutover-packet.md"
exit "$status"
