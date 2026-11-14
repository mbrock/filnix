#!/usr/bin/env bash
# Build a SerenityOS cross toolchain and sysroot from Nixpkgs' clang 23.
#
# Serenity's Toolchain/BuildClang.sh compiles a whole patched LLVM. Clang 23
# already has Serenity's driver upstream, so this script takes clang, lld and
# the LLVM tools from Nixpkgs' binary cache and builds only what Nixpkgs lacks:
# the runtimes for the Serenity target (compiler-rt builtins and crt files,
# libunwind, libc++abi, libc++ with Serenity's libc++ patch). It lays them out
# where Serenity's CMake toolchain file expects Toolchain/Local/clang, then
# builds Serenity's LibC, its dynamic loader and a few utilities with them.
# The boot stage builds the whole system, makes Serenity's disk image (which
# needs sudo for a loop mount) and boots it headless in QEMU, running smoke.sh.
#
# Usage: serenity-clang23.sh SERENITY_CHECKOUT [STAGE...]
# The checkout must be complete (not sparse). Stages: toolchain runtimes
# system boot; the default is the first three.
set -euo pipefail

S=$(cd "$1" && pwd)
shift
stages=${*:-toolchain runtimes system}
here=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
nix() { command nix --extra-experimental-features 'nix-command flakes' "$@"; }
step() { printf '\n== %s\n' "$*"; }

pkg() { nix build --no-link --print-out-paths --inputs-from "$repo" "nixpkgs#$1"; }
clang=$(pkg llvmPackages_23.clang-unwrapped)
clanglib=$(pkg llvmPackages_23.clang-unwrapped.lib)
lld=$(pkg llvmPackages_23.lld)
llvm=$(pkg llvmPackages_23.llvm)
export PATH=$(pkg cmake)/bin:$(pkg ninja)/bin:$(pkg python3)/bin:$PATH

arch=x86_64
triple=$arch-unknown-serenity
tc=$S/Toolchain/Local/clang
root=$S/Build/${arch}clang/Root
res=$tc/lib/clang/23

if [[ " $stages " == *" toolchain "* ]]; then
  step "Toolchain/Local/clang from Nixpkgs clang 23"
  rm -rf "$tc"
  mkdir -p "$tc/bin" "$res/lib"
  # Clang finds libc++ headers, the runtime libraries and ld.lld relative to
  # its own directory, and Nixpkgs' clang has its resource directory compiled
  # in, in the store. So clang and clang++ are wrappers that run clang through
  # a symlink here with -no-canonical-prefixes, which makes this directory
  # clang's own, and point it at a writable copy of the resource directory
  # that the Serenity compiler-rt goes into.
  cp -r --no-preserve=mode "$clanglib/lib/clang/23/include" "$res/include"
  for cc in clang clang++; do
    ln -s "$clang/bin/clang-23" "$tc/bin/$cc-23"
    printf '#!/bin/sh\nexec %s -no-canonical-prefixes -resource-dir %s "$@"\n' "$tc/bin/$cc-23" "$res" >"$tc/bin/$cc"
    chmod +x "$tc/bin/$cc"
  done
  ln -s "$lld/bin/ld.lld" "$tc/bin/ld.lld"
  for t in llvm-ar llvm-nm llvm-objcopy llvm-objdump llvm-ranlib llvm-strip llvm-cxxfilt llvm-readelf llvm-addr2line llvm-symbolizer; do
    ln -s "$llvm/bin/$t" "$tc/bin/$t"
  done

  step "LibC headers into the sysroot"
  (cd "$S" && cmake -DSERENITY_ARCH=$arch -DSERENITY_SYSROOT="$root" -P Meta/CMake/link_libc_headers.cmake)
  ls "$root/usr/include" | wc -l
fi

build=$S/Build/clang23-runtimes
cross=(
  -G Ninja -DCMAKE_BUILD_TYPE=Release
  -DCMAKE_SYSTEM_NAME=SerenityOS -DCMAKE_SYSTEM_PROCESSOR=$arch -DCMAKE_SYSROOT="$root"
  -DCMAKE_C_COMPILER="$tc/bin/clang" -DCMAKE_CXX_COMPILER="$tc/bin/clang++" -DCMAKE_ASM_COMPILER="$tc/bin/clang"
  -DCMAKE_C_COMPILER_TARGET=$triple -DCMAKE_CXX_COMPILER_TARGET=$triple -DCMAKE_ASM_COMPILER_TARGET=$triple
  -DCMAKE_AR="$tc/bin/llvm-ar" -DCMAKE_RANLIB="$tc/bin/llvm-ranlib" -DCMAKE_NM="$tc/bin/llvm-nm"
  -DCMAKE_OBJCOPY="$tc/bin/llvm-objcopy" -DCMAKE_STRIP="$tc/bin/llvm-strip"
  -DLLVM_ENABLE_PER_TARGET_RUNTIME_DIR=ON -DLLVM_DEFAULT_TARGET_TRIPLE=$triple
)

if [[ " $stages " == *" runtimes "* ]]; then
  step "runtime sources: compiler-rt 23.1.3, libc++ at Serenity's LLVM commit"
  # compiler-rt matches the compiler. libc++, libc++abi and libunwind come from
  # the LLVM commit Serenity pins, because Serenity's libc++ patch is written
  # against its locale API; libc++ supports being built by the latest released
  # clang, which is 23.
  rt=$S/Build/compiler-rt-23
  rm -rf "$rt"
  cp -r --no-preserve=mode "$(pkg llvmPackages_23.compiler-rt.src)" "$rt"
  commit=$(sed -n "s/^LLVM_COMMIT='\([0-9a-f]*\)'.*/\1/p" "$S/Toolchain/BuildClang.sh")
  src=$S/Build/llvm-project-$commit
  if [ ! -d "$src/.git" ]; then
    git init -q "$src"
    git -C "$src" remote add origin https://github.com/llvm/llvm-project.git
  fi
  git -C "$src" sparse-checkout set --no-cone /cmake /runtimes /libcxx /libcxxabi /libunwind \
    /third-party /llvm/cmake /llvm/utils/llvm-lit /llvm/utils/lit /libc/shared /libc/hdr \
    /libc/include/llvm-libc-macros /libc/include/llvm-libc-types /libc/src/__support
  git -C "$src" fetch -q --depth 1 --filter=blob:none origin "$commit"
  git -C "$src" checkout -q -f FETCH_HEAD
  git -C "$src" clean -fdq
  # Serenity's other LLVM patches build LLVM to run on Serenity (0002, 0003),
  # add /usr/local to the driver's paths (0001), profile support (0004) and
  # RISC-V CPU features (0006); a cross toolchain for x86_64 needs none of them.
  patch -d "$src" -p1 -s <"$S/Toolchain/Patches/llvm/0005-libcxx-Add-support-for-SerenityOS.patch"

  step "compiler-rt builtins and crt files"
  rm -rf "$build"
  cmake -S "$rt/compiler-rt" -B "$build/compiler-rt" "${cross[@]}" \
    -DCMAKE_C_COMPILER_WORKS=ON -DCMAKE_CXX_COMPILER_WORKS=ON -DCMAKE_ASM_COMPILER_WORKS=ON \
    -DCMAKE_INSTALL_PREFIX="$res" -DCOMPILER_RT_DEFAULT_TARGET_ONLY=ON \
    -DCOMPILER_RT_BUILD_BUILTINS=ON -DCOMPILER_RT_BUILD_CRT=ON -DCOMPILER_RT_EXCLUDE_ATOMIC_BUILTIN=OFF \
    -DCOMPILER_RT_BUILD_SANITIZERS=OFF -DCOMPILER_RT_BUILD_XRAY=OFF -DCOMPILER_RT_BUILD_LIBFUZZER=OFF \
    -DCOMPILER_RT_BUILD_PROFILE=OFF -DCOMPILER_RT_BUILD_MEMPROF=OFF -DCOMPILER_RT_BUILD_ORC=OFF \
    -DCOMPILER_RT_BUILD_CTX_PROFILE=OFF -DCOMPILER_RT_BUILD_GWP_ASAN=OFF >"$build-compiler-rt.log"
  ninja -C "$build/compiler-rt" install >>"$build-compiler-rt.log"
  ls "$res/lib/$triple"

  step "libunwind, libc++abi and libc++"
  # As in Serenity's Toolchain/CMake/LLVMConfig.cmake: configure checks link
  # against Serenity's stub libraries, since its LibC is not built yet.
  # LibC links libc++.a into libc.so (-static-libstdc++), so the archives must
  # be position-independent, not just PIE as Serenity's clang defaults to.
  flags="-Wno-unused-command-line-argument -nostartfiles -L$S/Toolchain/Stubs/$arch"
  cmake -S "$src/runtimes" -B "$build/runtimes" "${cross[@]}" \
    -DCMAKE_C_FLAGS="$flags" -DCMAKE_CXX_FLAGS="$flags" -DCMAKE_POSITION_INDEPENDENT_CODE=ON \
    -DCMAKE_INSTALL_PREFIX="$tc" -DLLVM_ENABLE_RUNTIMES="libunwind;libcxxabi;libcxx" \
    -DLIBUNWIND_USE_COMPILER_RT=ON -DLIBCXXABI_USE_COMPILER_RT=ON -DLIBCXX_USE_COMPILER_RT=ON \
    -DLIBCXX_ENABLE_STATIC_ABI_LIBRARY=ON -DLIBCXX_INCLUDE_BENCHMARKS=OFF -DLIBCXX_INCLUDE_TESTS=OFF \
    -DLIBCXXABI_INCLUDE_TESTS=OFF -DLIBUNWIND_INCLUDE_TESTS=OFF \
    -DLIBCXXABI_HAS_DL_LIB=OFF -DLIBCXXABI_HAS_PTHREAD_LIB=OFF -DLIBCXX_HAS_M_LIB=OFF \
    -DLIBCXX_HAS_PTHREAD_LIB=OFF -DLIBUNWIND_HAS_DL_LIB=OFF -DLIBUNWIND_HAS_PTHREAD_LIB=OFF \
    >"$build-runtimes.log"
  ninja -C "$build/runtimes" install >>"$build-runtimes.log"
  ls "$tc/lib/$triple"
fi

if [[ " $stages " == *" system "* ]]; then
  step "Serenity superbuild: Lagom host tools, then configure the system"
  # The host tools (code generators) build with Nixpkgs' gcc; the system
  # builds with Serenity's own CMake toolchain file, which finds
  # Toolchain/Local/clang.
  gcc=$(pkg gcc | grep -v -- -man)
  # Serenity's CMakeLists.txt refuses any clang but the exact LLVM commit it
  # pins; that is a policy, so tell it to expect this clang instead.
  sed -i 's/^set(LLVM_VERSION ".*")$/set(LLVM_VERSION "23.1.3")/' "$S/CMakeLists.txt"
  super=$S/Build/superbuild-${arch}clang
  cmake -G Ninja -S "$S/Meta/CMake/Superbuild" -B "$super" \
    -DSERENITY_ARCH=$arch -DSERENITY_TOOLCHAIN=Clang \
    -DCMAKE_C_COMPILER="$gcc/bin/gcc" -DCMAKE_CXX_COMPILER="$gcc/bin/g++" \
    -DSERENITY_CACHE_DIR="$S/Build/caches" -DCMAKE_INSTALL_PREFIX="$S/Build/lagom-install" \
    >"$S/Build/superbuild.log"
  ninja -C "$super" serenity-configure >>"$S/Build/superbuild.log"
  step "LibC, crt0, the dynamic loader and some utilities"
  ninja -C "$S/Build/${arch}clang" ${SYSTEM_TARGETS:-LibC crt0 Loader.so true echo cat} \
    >"$S/Build/system.log"
  tail -1 "$S/Build/system.log"
fi

if [[ " $stages " == *" boot "* ]]; then
  step "the whole system, a disk image, and a boot in QEMU"
  sb=$S/Build/${arch}clang
  ninja -C "$sb" >"$S/Build/full.log"
  ninja -C "$sb" install >>"$S/Build/full.log"
  tools=$(pkg qemu_kvm | head -1)/bin:$(pkg genext2fs)/bin:$(pkg e2fsprogs | grep -- -bin)/bin:$(pkg rsync)/bin
  # Serenity's image script must run as root to loop-mount the image, and
  # sudo would drop PATH, so it runs under sudo env.
  (cd "$sb" && sudo env PATH="$tools:$PATH" SERENITY_SOURCE_DIR="$S" SERENITY_ARCH=$arch \
    SERENITY_TOOLCHAIN=Clang "$S/Meta/build-image-qemu.sh" >"$S/Build/image.log")
  # Self-test mode runs /home/anon/Tests/run-tests-and-shutdown.sh on the
  # serial console; swap in a short smoke script instead of the test suite.
  mnt=$S/Build/mnt
  mkdir -p "$mnt"
  sudo mount -o loop "$sb/_disk_image" "$mnt"
  sudo install -m 755 -o 100 -g 100 "$here/smoke.sh" "$mnt/home/anon/Tests/run-tests-and-shutdown.sh"
  sudo umount "$mnt"
  (cd "$sb" && PATH="$tools:$PATH" SERENITY_SOURCE_DIR="$S" SERENITY_ARCH=$arch SERENITY_TOOLCHAIN=Clang \
    SERENITY_RUN=ci SERENITY_KERNEL_CMDLINE="graphics_subsystem_mode=off system_mode=self-test" \
    timeout 600 python3 "$S/Meta/run.py" >"$S/Build/serial.log" 2>&1) || true
  sed -n '/==== clang 23 SerenityOS smoke ====/,/==== smoke done ====/p' "$S/Build/serial.log"
  grep -q '==== smoke done ====' "$S/Build/serial.log"
fi
