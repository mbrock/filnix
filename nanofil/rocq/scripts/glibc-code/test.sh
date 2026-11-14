#!/usr/bin/env bash
# Exercise byte parity and fail-first checks with the real captured units.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
capture=${1:?pass the glibc capture directory}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
python3 -I "$here/test-blocks.py"
python3 -I "$here/test-source.py"
python3 -I "$here/skeleton.py" string/Strcmp __GI_strcmp --capture "$capture" \
  --rocq-function glibc_strcmp >"$work/strcmp-skeleton"
grep -F 'WP (ERun (mkFrame glibc_strcmp e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.' \
  "$work/strcmp-skeleton"
python3 -I "$here/generate.py" "$capture"
python3 -I "$here/generate.py" "$capture" --form shared-prelude --output "$work/staged"
python3 -I "$here/generate.py" "$capture" --form shared-prelude --tree "$work/staged"

# A wrong atom, a wrong proof, a missing file and a stale slice must all fail.
python3 - "$work/staged" <<'PY'
from pathlib import Path
import sys
tree = Path(sys.argv[1])
p = tree / 'stdio/PrintfStateCode.v'
p.write_text(p.read_text().replace('TAtom "__printf_buffer_done"', 'TAtom "wrong_body"', 1))
p = tree / 'stdio/PrintfBufferFileCode.v'
p.write_text(p.read_text().replace('Proof. vm_compute. reflexivity. Qed.', 'Proof. exact I. Qed.', 1))
(tree / 'stdio/PrintfBufferIoCode.v').unlink()
(tree / 'getopt/GetoptCode99.v').write_text('stale\n')
PY
if python3 -I "$here/generate.py" "$capture" --form shared-prelude --tree "$work/staged" \
    --directory stdio --directory getopt >"$work/rejected"; then
  echo "generator accepted corrupt fixtures" >&2; exit 1
fi
grep -F 'stdio: 6 files, 3 differ, 0 stale' "$work/rejected"
grep -F 'getopt: 9 files, 0 differ, 1 stale' "$work/rejected"

# Exercise the style-sync CLI in an isolated copy, never in the real manifests.
mkdir -p "$work/nanofil/rocq/scripts/glibc-code" "$work/nanofil/rocq/glibc/string"
cp "$here/sync-proof-styles.py" "$work/nanofil/rocq/scripts/glibc-code/"
cp "$here/../../glibc/string/code.toml" "$work/nanofil/rocq/glibc/string/"
mkdir -p "$work/styles/string"
cp "$work/staged/string/"*Code.v "$work/styles/string/"
python3 - "$work/styles/string" <<'PY'
from pathlib import Path
import re
import sys
# Keep this test's default-style control independent of main's conversions.
for file in Path(sys.argv[1]).glob('*.v'):
    file.write_text(re.sub(r'Proof\. vm_cast_no_check \(eq_refl .+\)\. Qed\.',
                           'Proof. vm_compute. reflexivity. Qed.', file.read_text()))
PY
cat >"$work/styles/string/StrcmpCode.v" <<'COQ'
(** Generated fixture. Do not edit. *)
Lemma sample : Some true = Some true.
Proof. vm_cast_no_check (eq_refl (Some true)). Qed.
COQ
python3 -I "$work/nanofil/rocq/scripts/glibc-code/sync-proof-styles.py" "$work/styles"
grep -F '"StrcmpCode.v" = "vm_cast_no_check"' "$work/nanofil/rocq/glibc/string/code.toml"
cp "$work/nanofil/rocq/glibc/string/code.toml" "$work/styles-before.toml"
cp "$work/styles/string/StrcmpCode.v" "$work/Strcmp-valid.v"
reject_sync() {
  if python3 -I "$work/nanofil/rocq/scripts/glibc-code/sync-proof-styles.py" \
      "$work/styles" >"$work/$1.log" 2>&1; then
    echo "style sync accepted $1" >&2; exit 1
  fi
  grep -F "$2" "$work/$1.log"
  cmp "$work/styles-before.toml" "$work/nanofil/rocq/glibc/string/code.toml"
}
cat >>"$work/styles/string/StrcmpCode.v" <<'COQ'
Lemma plain : Some false = Some false.
Proof.
  vm_compute. reflexivity.
Qed.
COQ
reject_sync mixed-multiline 'mixed proof styles'
cp "$work/Strcmp-valid.v" "$work/styles/string/StrcmpCode.v"
cat >>"$work/styles/string/StrcmpCode.v" <<'COQ'
Lemma unknown : True.
Proof.
  exact I.
Qed.
COQ
reject_sync unknown-multiline 'unrecognized computed proof'
cp "$work/Strcmp-valid.v" "$work/styles/string/StrcmpCode.v"
printf '\nQed.\n' >>"$work/styles/string/StrcmpCode.v"
reject_sync unmatched-proof 'unrecognized proof block'
rm "$work/styles/string/StrcmpCode.v"
reject_sync missing-converted 'missing fixture:'
sed 's/Do not edit\.//' "$work/Strcmp-valid.v" >"$work/styles/string/StrcmpCode.v"
reject_sync damaged-header 'unrecognized generated header'
cp "$work/Strcmp-valid.v" "$work/styles/string/StrcmpCode.v"
mv "$work/styles/string/StrncmpCode.v" "$work/Strncmp-valid.v"
reject_sync missing-default 'missing fixture:'
mv "$work/Strncmp-valid.v" "$work/styles/string/StrncmpCode.v"
python3 -I "$work/nanofil/rocq/scripts/glibc-code/sync-proof-styles.py" "$work/styles"
cmp "$work/styles-before.toml" "$work/nanofil/rocq/glibc/string/code.toml"
cp "$here/generate.py" "$here/prelude.py" "$here/source.py" "$here/source.pl" "$here/select.pl" "$work/nanofil/rocq/scripts/glibc-code/"
cp "$here/../../glibc/CodePrelude.v" "$work/nanofil/rocq/glibc/"
for part in bin src survey bench; do ln -s "$here/../../../$part" "$work/nanofil/$part"; done
for script in gallina.pl link.pl; do ln -s "$here/../$script" "$work/nanofil/rocq/scripts/$script"; done
python3 -I "$work/nanofil/rocq/scripts/glibc-code/generate.py" "$capture" \
  --output "$work/cast"
grep -F 'Proof. vm_cast_no_check (eq_refl (Some strcmp_module)). Qed.' "$work/cast/string/StrcmpCode.v"
grep -F 'Proof. vm_cast_no_check (eq_refl (Some (Defined glibc_strcmp))). Qed.' "$work/cast/string/StrcmpCode.v"
grep -F 'Proof. vm_compute. reflexivity. Qed.' "$work/cast/string/StrncmpCode.v"

# A row may name a real root but request a function those units do not define.
# The string layout used to silently emit an empty fallback for that mistake.
python3 - "$work/nanofil/rocq/glibc/string/code.toml" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1])
p.write_text(p.read_text().replace(
    'Strcmp|strcmp|string/strcmp.os|__GI_strcmp',
    'Strcmp|strcmp|string/strcmp.os|__GI_strcmp absent_lane_function', 1))
PY
if python3 -I "$work/nanofil/rocq/scripts/glibc-code/generate.py" "$capture" \
    --output "$work/missing" >"$work/missing.log" 2>&1; then
  echo 'generator accepted a manifest function absent from linked units' >&2; exit 1
fi
grep -F 'missing function in linked units: absent_lane_function' "$work/missing.log"
grep -F 'fixture row Strcmp|strcmp|string/strcmp.os|__GI_strcmp absent_lane_function' "$work/missing.log"
echo 'code generator: byte parity, corrupt-fixture rejection, manifest proof styles and missing-function rejection passed'
