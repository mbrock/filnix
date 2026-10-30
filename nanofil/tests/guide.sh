#!/usr/bin/env bash
# The guide's example outputs: docs/guide.md shows what nanofil makes of
# docs/guide/list.c at each stage, and README.md what -O makes of
# docs/guide/sum.c, in blocks between
#
#   <!-- guide: NAME -->
#   ...
#   <!-- /guide -->
#
# This script recomputes every NAME below from nanofil's own commands and
# tests/guide.pl, and writes them into those files.
#
#   guide.sh            rewrite the blocks
#   guide.sh --check    exit 1, showing the difference, if any block is stale
#
# Needs FILCC (preprocessing) and the bin/nanofil host on SWI-Prolog.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
nanofil=$here/../bin/nanofil
export FILCC=${FILCC:?set FILCC to a filcc clang}
# The outputs are those of the defaults, from the sources.
unset NANOFIL_STATE NANOFIL_OPT NANOFIL_REGISTERS NANOFIL_BRANCHES NANOFIL_CHECKS \
  NANOFIL_MEMCPY NANOFIL_INLINE NANOFIL_SIMPLIFY NANOFIL_VECTORS NANOFIL_STD
cd "$here/../docs/guide"

# sum_func: the func(sum, ...) clause of IR text on stdin.
sum_func() { sed -n '/^func(sum,/,/^\]).$/p'; }
nf() { "$nanofil" "$@" </dev/null; }
script() { "$nanofil" --script ../../tests/guide.pl "$1" list.c </dev/null; }

out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
for name in pp parse elaborate context promote checked renew mutant abi homes; do
  script "$name" >"$out/$name"
done
cp list.c "$out/source"
nf cc-ir list.c | sum_func >"$out/lower"
nf -O cc-ir list.c | sum_func >"$out/optimized"
nf -O cc-ir sum.c | sum_func >"$out/readme-sum"
nf cc list.c | sed -n '/^\.Lsum\.L4:/,/^\tmovq %rax, -8(%rbp)$/p' >"$out/asm-check"
nf -O cc list.c >"$out/asm"
sed -n '/^pizlonatedFIP[0-9]*_sum:/,/^\.Lsum\.start:/p' "$out/asm" >"$out/asm-prologue"
sed -n '/^\.Lsum\.L3:/,/^\.Lsum\.L5:/p' "$out/asm" >"$out/asm-loop"
rm "$out/asm"
{ echo "\$ nanofil run list.c three"; nf run list.c three
  echo "\$ nanofil -O run list.c three"; nf -O run list.c three; } >"$out/run"

python3 -I - "$out" "${1:-}" "$here/../docs/guide.md" "$here/../README.md" <<'PY'
import difflib, os, re, sys
out, mode, files = sys.argv[1], sys.argv[2], sys.argv[3:]
names = set()

def block(m):
    name = m.group(1)
    names.add(name)
    path = os.path.join(out, name)
    if not os.path.exists(path):
        sys.exit(f"guide.sh: a block names an unknown output {name}")
    body = open(path).read()
    if not body.strip():
        sys.exit(f"guide.sh: the output {name} is empty")
    lang = ("asm" if name.startswith("asm") else "text" if name == "run"
            else "c" if name == "source" else "prolog")
    return f"<!-- guide: {name} -->\n```{lang}\n{body}```\n<!-- /guide -->"

stale = []
for f in files:
    text = open(f).read()
    new = re.sub(r"<!-- guide: (\S+) -->\n.*?<!-- /guide -->", block, text, flags=re.S)
    if new == text:
        continue
    stale.append(f)
    if mode == "--check":
        sys.stdout.writelines(difflib.unified_diff(
            text.splitlines(True), new.splitlines(True), f, "regenerated"))
    else:
        open(f, "w").write(new)
unused = sorted(set(os.listdir(out)) - names)
if unused:
    sys.exit(f"guide.sh: outputs no block shows: {' '.join(unused)}")
if mode == "--check":
    if stale:
        sys.exit("guide.sh: stale outputs; run nanofil/tests/guide.sh")
    print(f"guide.sh: {len(names)} outputs current")
else:
    print(f"guide.sh: {len(names)} outputs, {len(stale)} files updated")
PY
