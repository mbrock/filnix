# Determinate Nix under Fil-C

[Determinate Nix](https://github.com/DeterminateSystems/nix-src) is
Determinate Systems' fork of Nix. Its extra features include parallel
evaluation, lazy trees, `builtins.parallel`, Wasm in the language and an
async (Boost.Asio) store layer. This port builds v3.22.5 (based on Nix
2.35.2) with Fil-C and runs its test suites. It also runs parallel
evaluation hard enough that races, use-after-frees and out-of-bounds
accesses in the fork would show up as Fil-C safety panics.

```sh
nix build -L .#legacyPackages.x86_64-linux.pkgsFilc.determinate-nix
# the functional suite again, with eval-cores = 8 for every evaluation:
nix build -L .#legacyPackages.x86_64-linux.pkgsFilc.determinateNixComponents.nix-functional-tests-parallel
```

RESULTS

## Packaging

Nixpkgs has no Determinate Nix package, so
[ports/determinate-nix.nix](../ports/determinate-nix.nix) instantiates the
fork's own `packaging/components.nix`. That is the component scope that
Nixpkgs vendors for upstream Nix, so the same structure carries over. The
scope sits on Nixpkgs' `nixDependencies` from `pkgsFilc`, and the source is
the release tarball. The Fil-C overrides that the upstream Nix 2.34 port
needs are now shared as `nixFilcOverrides` in
[ports/overlay.nix](../ports/overlay.nix): no LTO, no sigaltstack handler,
fork instead of vfork, no namespaces, seccomp off with `filter-syscalls`
defaulting to false, libc's nss_dns by path, and the plugins suite skipped.
The upstream `nix` derivation is unchanged by the refactoring (same
`.drv`).

What Determinate Nix needs on top of that:

- **Its libgit2.** libfetchers calls `git_config_backend_from_values`, from
  the fork's libgit2 2.0 pre-release. The fork's `dependencies.nix` supplies
  it, applied over the libgit2 port.
- **No Wasm, Sentry or mimalloc.** wasmtime is Rust with a JIT, and
  sentry-native brings crashpad. mimalloc would replace Fil-C's allocator.
- **No unity build.** Each library would otherwise be one translation unit,
  which serializes the slow Fil-C compile.
- **Scope-local Boost with an Asio fix** (see below). The rest of pkgsFilc
  keeps its cached Boost.
- **`util-linux` from the build platform** for the `enosys` wrapper and the
  functional tests. The scope is not spliced, so these would otherwise be
  Fil-C builds (and `enosys` installs a seccomp filter).

## Porting changes (Fil-C, not Determinate Nix bugs)

The source patches are in
[patches/determinate-nix/](../patches/determinate-nix/). Only 0005 changes
behaviour outside Fil-C.

1. **Pointer-typed packed `Value` words** (0001). The upstream port turns off
   the bit-packed `Value` layout, because it keeps tagged pointers in
   `uint64_t` words and Fil-C drops capabilities from integer-typed memory.
   Determinate Nix cannot do that: parallel evaluation lives in that layout
   (the atomic `p0` word with its thunk → pending → awaited states,
   `waitOnThunk`, `notifyWaiters`), and the generic layout has none of it.
   The patch makes `PackedPointer` a small `FilcPackedWord` struct under
   `__FILC__`. The struct holds a `char *` that behaves like the integer:
   tag bits are set and cleared with pointer arithmetic, and integers and
   doubles are stored as capability-less addresses. `std::atomic` of a
   struct holding one pointer is lock-free under Fil-C and keeps the
   capability, so the memory-ordering protocol is unchanged. The mask
   becomes a plain `uint64_t` constant. Nothing changes without `__FILC__`.
   The same patch should let the upstream port use the packed layout too.
2. **No `__cxa_throw` interposer** (0002). Determinate Nix interposes
   `__cxa_throw`, to abort on `std::logic_error`, and finds the real one with
   `dlsym(RTLD_NEXT, ...)`. Fil-C's `dlsym` traps on `RTLD_NEXT`, so the first
   exception of any kind stopped the program.
3. **`syscall()` results truncated to `int`** (0003). Fil-C's `syscall()`
   returns -1 as 4294967295. `openat2` and `fchmodat2` failures then looked
   like successes: `fchmodatTryNoFollow` returned normally for missing
   files and symlinks, and a failed `openat2` would have become file
   descriptor 4294967295.
4. **No huge reservations** (0004). The fork reserves an 8 GiB mapping for
   each `Exprs` bump allocator and 1 GiB for each symbol table. Fil-C
   materializes and zeroes the capability shadow of the whole mapping on
   the first pointer store, so every `EvalState` cost gigabytes of RSS. The
   expression tests reached 11 GiB and were OOM-killed; natively they peak
   at 117 MiB. Under Fil-C the bump allocator uses its upstream resource
   (the reservation is only an optimization), and the symbol arena is
   128 MiB. All of Nixpkgs needs about 12 MiB of symbols.
5. **Boost.Asio's `io_context` executor** (patches/boost-asio-io-context-executor-pointer.patch).
   It keeps `io_context* | bits` in a `uintptr_t`. The async `computeClosure`
   (and the rest of the Asio store code) trapped in `use_service`.
6. **Skipped test:** `CompressionDecompressionTest.invalidDecompression/*`
   is the open exception-lifetime issue that the upstream port also skips
   (docs/filc-findings.md).

The Fil-C-level findings (`RTLD_NEXT`, `syscall()`, Asio) are also in
[filc-findings.md](filc-findings.md).

BUGS
