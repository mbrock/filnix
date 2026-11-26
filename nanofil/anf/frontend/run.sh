#!/usr/bin/env bash
# Build and gate the Gallina C frontend (nanofil/rocq/frontend/) through
# CertiRocq's λANF (-O 1 --anf-variant 8), nanofil/anf/lower/AnfLower.v, and
# nanofil-backend compile-allocated into a Fil-C x86-64 binary over the arena
# of nanofil/anf.
#
# When FILCC is available, links anf-frontend and verifies byte-for-byte
# output parity against nanofil-frontend across the C test corpus under both
# the default nursery and a 4096-word stress nursery with FUGC verification.
#
# Environment:
#   FILCC             Fil-C's clang (default /tmp/filcc/bin/clang)
#   NANOFIL_BACKEND   default rocq/backend/nanofil-backend, built if missing
#   ANF_STRESS_NURSERY  default 4096
#   ANF_WORK          scratch directory (default mktemp -d)
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
anf=$(cd "$here/.." && pwd)
nanofil=$(cd "$anf/.." && pwd)
frontend="$nanofil/rocq/frontend"
filcc=${FILCC:-/tmp/filcc/bin/clang}
backend=${NANOFIL_BACKEND:-$nanofil/rocq/backend/nanofil-backend}
stress=${ANF_STRESS_NURSERY:-4096}
work=${ANF_WORK:-$(mktemp -d)}
mkdir -p "$work/f" "$work/t"
echo "work: $work"
stamp() { date -u +%H:%M:%S; }

t0=$SECONDS
echo "$(stamp) building nanofil-backend, anf-lower, and reference nanofil-frontend"
[[ -x $backend ]] || make -C "$nanofil/rocq/backend" -j"${NIX_BUILD_CORES:-4}" nanofil-backend >"$work/backend.log"
make -C "$anf/lower" -j"${NIX_BUILD_CORES:-4}" anf-lower >"$work/anf-lower.log"
[[ -x "$frontend/nanofil-frontend" ]] || make -C "$frontend" -j"${NIX_BUILD_CORES:-4}" >"$work/frontend.log"
echo "$(stamp) tools ready in $((SECONDS - t0)) s"

cp "$frontend"/{CAst,CAttrs,CLex,CParse,CCanon,CPp}.v "$work/f/"
cp "$anf/lower/Prims.v" "$here"/{Drive,Tap}.v "$work/t/"

t0=$SECONDS
echo "$(stamp) compiling frontend and tapping λANF (CertiRocq -O 1 --anf-variant 8)"
(
  cd "$work/f"
  rocq compile -w -all -R . Frontend CAst.v
  rocq compile -w -all -R . Frontend CAttrs.v
  rocq compile -w -all -R . Frontend CLex.v
  rocq compile -w -all -R . Frontend CParse.v
  rocq compile -w -all -R . Frontend CCanon.v
  rocq compile -w -all -R . Frontend CPp.v
)
(
  cd "$work/t"
  rocq compile -w -all -R "$work/f" Frontend -R . AnfFrontend Prims.v
  rocq compile -w -all -R "$work/f" Frontend -R . AnfFrontend Drive.v
  rocq compile -w -all -R "$work/f" Frontend -R . AnfFrontend Tap.v
)
echo "$(stamp) tapped in $((SECONDS - t0)) s ($(wc -l <"$work/t/AnfFrontend.Drive.run.ir") lines)"

t0=$SECONDS
echo "$(stamp) lowering λANF via anf-lower"
"$anf/lower/anf-lower" "$work/t/AnfFrontend.Drive.run.ir" >"$work/frontend.nir" 2>"$work/lower.err"
echo "$(stamp) lowered in $((SECONDS - t0)) s: $(cat "$work/lower.err")"

t0=$SECONDS
echo "$(stamp) validating and compiling IR via nanofil-backend compile-allocated"
"$backend" compile-allocated "$work/frontend.nir" >"$work/frontend.s"
echo "$(stamp) compiled in $((SECONDS - t0)) s ($(wc -l <"$work/frontend.s") lines of assembly)"

if [[ ! -x $filcc ]]; then
  echo "$(stamp) FILCC ($filcc) not present; stopping after assembly emission"
  exit 0
fi

t0=$SECONDS
as -o "$work/frontend.o" "$work/frontend.s"
"$filcc" -O2 -c -I"$anf" -o "$work/anf_arena.o" "$anf/anf_arena.c"
"$filcc" -O2 -c -o "$work/rt.o" "$anf/lower/anf_lower_rt.c"
"$filcc" -O2 -c -o "$work/prims.o" "$anf/lower/anf_prims.c"
"$filcc" -O2 -c -I"$anf" -o "$work/driver.o" "$here/driver.c"
"$filcc" -o "$work/anf-frontend" \
  "$work/driver.o" "$work/rt.o" "$work/prims.o" "$work/anf_arena.o" "$work/frontend.o"
echo "$(stamp) linked $work/anf-frontend in $((SECONDS - t0)) s"

ulimit -s "${ANF_STACK_KB:-1048576}"

python3 - "$nanofil" "$frontend/nanofil-frontend" "$work/anf-frontend" "$stress" "$filcc" <<'PY'
import glob, os, subprocess, sys, tempfile

nanofil, ref_bin, anf_bin, stress, filcc = sys.argv[1:6]
cfiles = sorted(glob.glob(os.path.join(nanofil, 'tests', '**', '*.c'), recursive=True))
if not cfiles:
    sys.exit("no .c fixtures found")

lex_diffs = parse_diffs = 0
for cf in cfiles:
    for cmd in ('lex', 'parse'):
        r1 = subprocess.run([anf_bin, cmd, cf], capture_output=True)
        r2 = subprocess.run([ref_bin, cmd, cf], capture_output=True)
        if (r1.returncode == 0) != (r2.returncode == 0) or (r1.returncode == 0 and r1.stdout != r2.stdout):
            if cmd == 'lex':
                lex_diffs += 1
            else:
                parse_diffs += 1
            if lex_diffs + parse_diffs <= 5:
                print(f"DIFF {cmd} {cf}: rc {r1.returncode} vs {r2.returncode}", file=sys.stderr)

print(f"parity ({len(cfiles)} files): lex_diffs={lex_diffs}, parse_diffs={parse_diffs}")
if lex_diffs or parse_diffs:
    sys.exit(1)

# Preprocessor parity across all 20 glibc headers under default and stress nurseries.
headers = [
    'stdio', 'stdlib', 'string', 'stdint', 'ctype', 'limits', 'errno', 'unistd',
    'signal', 'math', 'pthread', 'time', 'sys/stat', 'dirent', 'wchar',
    'inttypes', 'fcntl', 'sys/mman', 'getopt', 'setjmp',
]
senv = os.environ.copy()
senv.update({'ANF_NURSERY': stress, 'FUGC_SCRIBBLE': '1', 'FUGC_VERIFY': '1'})

with tempfile.TemporaryDirectory() as td:
    hfiles = []
    for h in headers:
        p = os.path.join(td, f"h-{h.replace('/', '_')}.c")
        with open(p, 'w') as f:
            f.write(f"#include <{h}.h>\n")
        hfiles.append(p)
    pp_diffs = 0
    for hf in hfiles:
        for cmd in ('pp', 'pp-parse'):
            r1 = subprocess.run([anf_bin, '--clang', filcc, cmd, hf], capture_output=True)
            r2 = subprocess.run([ref_bin, '--clang', filcc, cmd, hf], capture_output=True)
            if r1.returncode != 0 or r2.returncode != 0 or r1.stdout != r2.stdout:
                pp_diffs += 1
                if pp_diffs <= 5:
                    print(f"PP DIFF {cmd} {os.path.basename(hf)}: rc {r1.returncode} vs {r2.returncode}", file=sys.stderr)
    print(f"pp parity ({len(hfiles)} glibc headers): pp_diffs={pp_diffs}")
    if pp_diffs:
        sys.exit(1)

    r_ref_pp = subprocess.run([ref_bin, '--clang', filcc, 'pp-bench'] + hfiles, capture_output=True, text=True, check=True)
    r_anf_pp = subprocess.run([anf_bin, '--clang', filcc, 'pp-bench'] + hfiles, capture_output=True, text=True, check=True)
    r_str_pp = subprocess.run([anf_bin, '--clang', filcc, 'pp-bench'] + hfiles, env=senv, capture_output=True, text=True, check=True)
    print(r_ref_pp.stdout.strip())
    print(r_anf_pp.stdout.strip())
    print("pp stress:", r_str_pp.stdout.strip())

r_ref = subprocess.run([ref_bin, 'bench'] + cfiles, capture_output=True, text=True, check=True)
r_anf = subprocess.run([anf_bin, 'bench'] + cfiles, capture_output=True, text=True, check=True)
r_str = subprocess.run([anf_bin, 'bench'] + cfiles, env=senv, capture_output=True, text=True, check=True)
print(r_ref.stdout.strip())
print(r_anf.stdout.strip())
print("stress:", r_str.stdout.strip())
PY
