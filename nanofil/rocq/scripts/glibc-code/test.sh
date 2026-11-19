#!/usr/bin/env bash
# Exercise exact regeneration and fail-first checks with the captured units.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
capture=${1:?pass the glibc capture directory}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
python3 -I "$here/test-blocks.py"
python3 -I "$here/test-source.py"
python3 -I "$here/test-block-facts.py"
python3 -I "$here/test-image.py"
python3 -I "$here/skeleton.py" string/Strcmp __GI_strcmp --capture "$capture" \
  --rocq-function Unit_string_strcmp_os.fn___GI_strcmp >"$work/strcmp-skeleton"
grep -F 'WP (ERun (mkFrame Unit_string_strcmp_os.fn___GI_strcmp e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.' \
  "$work/strcmp-skeleton"
python3 -I "$here/generate.py" "$capture"
python3 -I "$here/generate.py" "$capture" --output "$work/staged"

# A changed shared body, a changed proof, a missing join part and a stale
# file all fail comparison, including when checking only the Hello views.
python3 - "$work/staged" <<'PY'
from pathlib import Path
import sys

tree = Path(sys.argv[1])
path = tree / 'glibc/Unit_string_strlen_os.v'
text = path.read_text()
changed = text.replace('"__strlen"', '"wrong_body"', 1)
assert changed != text
path.write_text(changed)
path = tree / 'hello/HelloImageCodeItems01.v'
path.write_text(path.read_text().replace('Proof. reflexivity. Qed.', 'Proof. exact I. Qed.'))
(tree / 'hello/HelloImageCodeItems03.v').unlink()
(tree / 'hello/HelloImageCode999.v').write_text('stale\n')
PY
if python3 -I "$here/generate.py" "$capture" --tree "$work/staged" --directory hello >"$work/rejected"; then
  echo 'generator accepted corrupt fixtures' >&2
  exit 1
fi
grep -E 'glibc: [0-9]+ files, 1 differ, 0 stale' "$work/rejected"
grep -E 'hello: [0-9]+ files, 2 differ, 1 stale' "$work/rejected"
echo 'code generator: byte parity and corrupt-fixture rejection passed'
