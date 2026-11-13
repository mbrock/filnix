#!/usr/bin/env bash
# Exercise byte parity and fail-first checks with the real captured units.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
capture=${1:?pass the glibc capture directory}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
python3 -I "$here/generate.py" "$capture" --legacy --output "$work/legacy"
cp -r "$work/legacy" "$work/staged"
python3 -I "$here/../proof-eng/stages/15-code.py" "$work/staged"
cp "$here/../proof-eng/overlay/CodePrelude.v" "$work/staged/"
python3 -I "$here/generate.py" "$capture" --tree "$work/staged"

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
if python3 -I "$here/generate.py" "$capture" --tree "$work/staged" \
    --directory stdio --directory getopt >"$work/rejected"; then
  echo "generator accepted corrupt fixtures" >&2; exit 1
fi
grep -F 'stdio: 3 files, 3 differ, 0 stale' "$work/rejected"
grep -F 'getopt: 8 files, 0 differ, 1 stale' "$work/rejected"

# Exercise the style-sync CLI in an isolated copy, never in the real manifests.
mkdir -p "$work/nanofil/rocq/scripts/glibc-code" "$work/nanofil/rocq/glibc/string"
cp "$here/sync-proof-styles.py" "$work/nanofil/rocq/scripts/glibc-code/"
cp "$here/../../glibc/string/code.toml" "$work/nanofil/rocq/glibc/string/"
mkdir -p "$work/styles/string"
cat >"$work/styles/string/StrcmpCode.v" <<'COQ'
(** Generated fixture. Do not edit. *)
Lemma sample : Some true = Some true.
Proof. vm_cast_no_check (eq_refl (Some true)). Qed.
COQ
python3 -I "$work/nanofil/rocq/scripts/glibc-code/sync-proof-styles.py" "$work/styles"
grep -F '"StrcmpCode.v" = "vm_cast_no_check"' "$work/nanofil/rocq/glibc/string/code.toml"
cp "$here/generate.py" "$here/prelude.py" "$work/nanofil/rocq/scripts/glibc-code/"
for part in bin src survey bench; do ln -s "$here/../../../$part" "$work/nanofil/$part"; done
for script in gallina.pl link.pl; do ln -s "$here/../$script" "$work/nanofil/rocq/scripts/$script"; done
python3 -I "$work/nanofil/rocq/scripts/glibc-code/generate.py" "$capture" \
  --legacy --output "$work/cast"
grep -F 'Proof. vm_cast_no_check (eq_refl (Some strcmp_module)). Qed.' "$work/cast/string/StrcmpCode.v"
grep -F 'Proof. vm_cast_no_check (eq_refl (Some (Defined glibc_strcmp))). Qed.' "$work/cast/string/StrcmpCode.v"
grep -F 'Proof. vm_compute. reflexivity. Qed.' "$work/cast/string/StrncmpCode.v"
echo 'code generator: byte parity, corrupt-fixture rejection and manifest proof styles passed'
