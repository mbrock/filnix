#!/usr/bin/env bash
# Reproduce the Serenity typed-syscall spike against a real SerenityOS tree
# and real Fil-C. Steps:
#
#   1. sparse-clone SerenityOS at a pinned commit (or use $SERENITY);
#   2. run gen.py, which writes generated/;
#   3. layout check: the X-macro structs match Kernel/API/Syscall.h's;
#   4. compile Serenity's LibC and LibCore syscall users against the patched
#      Syscall.h, without and then with the typed LibSystem/syscall.h;
#   5. compile the trusted marshaller for every generic params struct, and
#      check that the six special structs are refused;
#   6. build libpizlo with its Linux syscall layer split out of the core
#      (libpizlo/), and check on Linux that it behaves like the stock build;
#   7. build that core for x86_64-pc-serenity and sort its undefined symbols;
#   8. build the split libpizlo with the spike natives, then build and run
#      demo/: well-formed calls, seven attacks, five compile-time mistakes.
#
# Steps 3 to 5 and 7 compile for Serenity: Serenity's own LibC, AK and
# Kernel/API headers instead of glibc. Nothing here runs on Serenity; step 8
# runs on Linux with a Linux emulation of the kernel trap.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
work=${WORK:-$(mktemp -d)}
SERENITY_REV=1a00c247b06730267fd6b0dc9f700a435c3e66b4
S=${SERENITY:-$work/serenity}

step() { printf '\n== %s\n' "$*"; }

if [ ! -d "$S/Kernel" ]; then
  step "cloning SerenityOS $SERENITY_REV into $S"
  git clone --quiet --filter=blob:none --no-checkout https://github.com/SerenityOS/serenity.git "$S"
  git -C "$S" sparse-checkout set AK Kernel/API Kernel/Arch Kernel/Tasks Kernel/Syscalls Tests/Kernel \
    Userland/Libraries/{LibC,LibSystem,LibCore,LibELF,LibFileSystem,LibIPC,LibRegex,LibTimeZone,LibCrypt,LibUnicode,LibDl}
  git -C "$S" checkout --quiet "$SERENITY_REV"
fi

step "generating tables from Kernel/API/Syscall.h and Kernel/Tasks/Process.h"
python3 "$here/gen.py" "$S" "$here/generated"

# Fil-C's compiler pieces, without the filnix wrappers that add glibc headers.
nix() { command nix --extra-experimental-features 'nix-command flakes' "$@"; }
filc=$(nix eval --raw "$repo#filcc.components.outPath")
filc0=$(nix eval --raw "$repo#filcc.components.filc0")
libcxx=$(nix eval --raw "$repo#filcc.components.filc-libcxx")
nix build --no-link "$repo#filcc.components"
res=$(grep -o -- '-resource-dir [^ ]*' "$filc/bin/clang++" | cut -d' ' -f2)

# Fil-C's driver adds -internal-isystem /usr/include for its Linux target
# even with -nostdinc; AK/Platform.h includes <features.h> when it exists,
# so an empty one shadows the host's.
mkdir -p "$work/shim/AK"
: >"$work/shim/features.h"
sed -E 's/#( *)cmakedefine01 ([A-Z0-9_]+)/#\1define \2 0/' "$S/AK/Debug.h.in" >"$work/shim/AK/Debug.h"

serenity_cxx() {
  "$filc0/bin/clang-20" --driver-mode=g++ -resource-dir "$res" \
    -std=c++23 -nostdinc -nostdinc++ -fno-exceptions -fno-rtti -Wno-user-defined-literals \
    -isystem "$work/shim" -isystem "$libcxx/include/c++" \
    -isystem "$S/Userland/Libraries/LibC" -isystem "$S/Userland/Libraries/LibSystem" -isystem "$res/include" \
    ${OVERLAY:+-I"$OVERLAY"} -I"$S" -I"$S/Userland/Libraries" \
    -D__serenity__ -U__linux__ -U__gnu_linux__ -Ulinux "$@"
}

step "layout check: generated/layout_check.cpp against the unmodified Syscall.h"
serenity_cxx -fsyntax-only -I"$here/generated" "$here/generated/layout_check.cpp"
grep -o '[0-9]* assertions' "$here/generated/layout_check.cpp"

# Overlays: the patched Syscall.h alone, then with the typed LibSystem header.
patched=$work/overlay-patched
typed=$work/overlay-typed
mkdir -p "$patched/Kernel/API" "$typed/Kernel/API" "$typed/LibSystem"
cp "$here"/generated/{Syscall.h,SyscallParams.h,SyscallSignatures.h} "$patched/Kernel/API/"
cp "$here"/generated/{Syscall.h,SyscallParams.h,SyscallSignatures.h} "$typed/Kernel/API/"
ln -sf "$here/LibSystem/syscall.h" "$typed/LibSystem/syscall.h"
ln -sf "$here/LibSystem/syscall.h" "$typed/syscall.h"

step "Serenity LibC/LibCore syscall users: original, patched Syscall.h, typed syscall()"
cd "$S"
users=$(git grep -l -E '\bsyscall\(' -- Userland/Libraries/LibC Userland/Libraries/LibCore Tests/Kernel/fuzz-syscalls.cpp)
printf '%-48s %8s %8s %8s\n' file original patched typed
for f in $users; do
  o=$(serenity_cxx -fsyntax-only "$f" 2>&1 | grep -c 'error:' || true)
  p=$(OVERLAY=$patched serenity_cxx -fsyntax-only "$f" 2>&1 | grep -c 'error:' || true)
  t=$(OVERLAY=$typed serenity_cxx -fsyntax-only "$f" 2>&1 | grep -c 'error:' || true)
  printf '%-48s %8s %8s %8s\n' "$f" "$o" "$p" "$t"
done
step "call sites the typed path rejects"
for f in $users; do
  OVERLAY=$typed serenity_cxx -fsyntax-only "$f" 2>&1 |
    grep -E '^[^ ]+\.cpp:[0-9]+:[0-9]+: (error|note: in instantiation)' || true
done | sort -u
cd "$here"

step "trusted marshaller: all generic params structs against Serenity headers"
OVERLAY=$patched serenity_cxx -fsyntax-only runtime/marshal_check.cpp
echo "generic structs: ok"
for sc in mmap mremap futex create_thread set_mmap_name ptrace; do
  printf '%s: ' "$sc"
  if OVERLAY=$patched serenity_cxx -fsyntax-only -DREFUSED="$sc" runtime/marshal_check.cpp >"$work/refused.log" 2>&1; then
    echo "NOT refused"; exit 1
  fi
  grep -o 'static assertion failed: .*' "$work/refused.log" | sed 's/static assertion failed: //' | sort -u | paste -sd';' -
done

cxx=$(nix build --no-link --print-out-paths "$repo#filcc")/bin/clang++

step "libpizlo with its Linux syscall layer split out: same behavior on Linux"
split=$(nix build --impure --no-link --print-out-paths -f "$here/libpizlo/libpizlo-split.nix")
"${cxx%++}" -O1 "$here/libpizlo/syscall_smoke.c" -o "$work/smoke" -lpthread
"$work/smoke" >"$work/smoke-stock.txt"
LD_LIBRARY_PATH=$split/lib "$work/smoke" >"$work/smoke-split.txt"
diff "$work/smoke-stock.txt" "$work/smoke-split.txt"
echo "stock and split agree on $(wc -l <"$work/smoke-split.txt") checks"

step "libpizlo core built for x86_64-pc-serenity"
"$here/libpizlo/serenity-core.sh" "$S" "$work/serenity-core"

step "building the split libpizlo with the spike natives"
spike=$(nix build --impure --no-link --print-out-paths --expr "
  let flake = builtins.getFlake \"$repo\"; in
  import $here/libpizlo/libpizlo-split.nix {
    inherit flake;
    libpizlo = import $here/libpizlo-spike.nix { filcc = flake.packages.x86_64-linux.filcc; };
  }")

step "demo: well-formed calls (Linux emulation of the trap)"
"$cxx" -std=c++20 -O1 "$here/demo/demo.cpp" -o "$work/demo" -L"$spike/lib"
# The filcc runpath lists the stock libpizlo first; LD_LIBRARY_PATH wins over it.
LD_LIBRARY_PATH=$spike/lib "$work/demo"

step "demo: attacks, each of which libpizlo must stop"
for a in string-length string-freed out-buffer out-ptr forged-params indirect-length raw-buffer; do
  status=0
  LD_LIBRARY_PATH=$spike/lib "$work/demo" "$a" >"$work/attack.log" 2>&1 || status=$?
  where=$(grep -m1 -o '<runtime>: zsys_serenity_[a-z]*' "$work/attack.log" || true)
  printf '%-16s exit=%-3s %s | %s\n' "$a" "$status" "$where" \
    "$(grep -m1 -o 'filc safety error: [^(]*' "$work/attack.log" || grep -m1 'NOT stopped' "$work/attack.log")"
  [ -n "$where" ] || exit 1
done

step "demo: mistakes the typed macro rejects at compile time"
"$cxx" -std=c++20 -c "$here/demo/compile_fail.cpp" -o /dev/null
for i in 1 2 3 4 5; do
  printf 'case %s: ' "$i"
  if "$cxx" -std=c++20 -DCASE="$i" -c "$here/demo/compile_fail.cpp" -o /dev/null >"$work/cf.log" 2>&1; then
    echo "compiled (unexpected)"; exit 1
  fi
  grep -m1 -o 'error: .*' "$work/cf.log"
done
