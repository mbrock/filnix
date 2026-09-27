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

## Results

- **Builds and passes its suites.** `determinate-nix` (nix-everything) builds,
  so all of these ran and passed:

  | Suite | Result |
  | --- | --- |
  | nix-util-tests | 787 pass, also under `enosys` without openat2/fchmodat2 |
  | nix-store-tests | 722 pass |
  | nix-fetchers-tests | 31 pass |
  | nix-flake-tests | 23 pass |
  | nix-expr-tests | 366 pass |
  | functional tests | 184 ok, 0 fail, 38 skipped |
  | functional tests with `eval-cores = 8` and `parallel-eval` | 184 ok, 0 fail, 38 skipped |

  The skips are the suite's own (no daemon, no network, and so on), plus
  the tests that need this Nix to create namespaces, plus three that hit the
  Fil-C unwinding bug. These numbers are from `orb/determinate-nix`
  (main's toolchain). On `orb/determinate-nix-batch` (batch's toolchain with
  mbrock/fil-c fa8c296, Asio fix in the global Boost), the results are:
  - nix-util-tests: 791 pass. The decompression tests are no longer
    skipped, and `ChunkedVector.ConcurrentAdd` is fixed by patch 0006.
  - store 722, fetchers 31, flake 23 and expr 366 pass.
  - Functional tests: 188 ok, 0 fail, 35 skipped, both normally and with
    eval-cores = 8. That now includes `plugins`, `read-only-store`,
    `binary-cache` and `multiple-outputs-substitute-failure`.
  - race3.nix still traps (the Determinate Nix bug below).
- **Parallel evaluation gives the same results as native Nix.** With
  eval-cores = 8 under Fil-C, the `.drv` paths match native upstream Nix
  2.35.2 in each of these:
  - all 25,017 top-level Nixpkgs attributes (22,484 derivations)
  - four NixOS systems (minimal, server, Xfce desktop, Docker host), forced
    in parallel by `nix eval --json`
  - `builtins.parallel` over 2,155 packages

  There were no safety panics. Native Determinate Nix, built from the same
  scope, also matches with eval-cores 1 and 8.
- **One real race in parallel evaluation**, caught by Fil-C as an
  out-of-bounds write and confirmed with ThreadSanitizer and natively (bug 1
  below). Also two minor issues (bugs 2 and 3).
- **Porting problems in Fil-C itself**: `dlsym(RTLD_NEXT)`, the width of
  `syscall()`'s result, shadow memory for huge `mmap` reservations, and
  nested exceptions during unwinding. The last one is fixed in mbrock/fil-c
  fa8c296.

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
defaulting to false, and libc's nss_dns by path. The functional tests run
the Fil-C `nix` (including the plugins suite), with the sandbox tests off.
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
5. **Boost.Asio's `io_context` executor** (patches/boost-asio-io-context-executor-pointer.patch,
   now in the global boost187 port with a check). It keeps
   `io_context* | bits` in a `uintptr_t`. The async `computeClosure` (and
   the rest of the Asio store code) trapped in `use_service`.
6. **Test adjustments.** Unlike upstream, the fork refuses to build in a
   diverted store without the sandbox, where upstream quietly turns the
   sandbox off. So besides the shared switch that turns off sandbox tests,
   `unprivilegedUserNamespacesSupported` reports false and the unguarded
   diverted-store tail of `shell.sh` is dropped. The exception-lifetime
   skips from before batch pinned mbrock/fil-c fa8c296 are gone.

7. **Reload after a failed pointer CAS** (0006). Under contention, Fil-C's
   failed `compare_exchange_strong` on a pointer can write back the winner's
   address without its capability. `ChunkedVector::ensureChunk` returns that
   value, so `ChunkedVector.ConcurrentAdd` sometimes trapped. The patch
   reloads the pointer under `__FILC__`.

The Fil-C-level findings (`RTLD_NEXT`, `syscall()`, Asio, pointer CAS) are also in
[filc-findings.md](filc-findings.md).

## Bugs found in Determinate Nix

### 1. Parallel evaluation mutates one shared exception from several threads

The standalone report for Determinate Systems is
[determinate-nix-addtrace-race.md](determinate-nix-addtrace-race.md).

**This is a real bug: a data race in the fork's parallel evaluator that
becomes heap corruption.** When a thunk fails, `force()` stores
`std::current_exception()` in a `Value::Failed`
(`src/libexpr/include/nix/expr/eval-inline.hh`). Everyone who forces that
value later gets the *same* exception object back from
`std::rethrow_exception`. On the way up, catch sites decorate it in place:
`forceInt`/`evalBool`'s `errorCtx`, `callFunction`'s "while calling the
'…' builtin", `ExprSelect`, and so on all call `BaseError::addTrace`, which
does `err.traces.push_front(...)` on the shared object. With eval-cores > 1,
worker threads that reach the same failed thunk run those `push_front`s
concurrently on one `std::list`, without synchronization.
`CloneableError::throwClone` ("Useful when the exception can get modified
when appending traces") exists for exactly this, but nothing calls it.

Reproducer ([tests/determinate-nix/race3.nix](../tests/determinate-nix/race3.nix)):

```nix
{ n ? 20000 }:
let
  bad = builtins.throw "shared failure";
  xs = builtins.genList (i: builtins.tryEval (builtins.add bad i)) n;
  failures = builtins.length (builtins.filter (r: !r.success) xs);
in
builtins.parallel xs (builtins.seq failures (builtins.sub 0 bad))
```

```sh
nix eval --extra-experimental-features parallel-eval --option eval-cores 8 \
  --impure --expr 'import ./race3.nix {}'
```

- **Under Fil-C** it stops 3 runs out of 3 with a worker thread writing out
  of bounds inside `std::list::push_front`:

  ```
  filc safety error: cannot write pointer with ptr >= upper.
      (libnixutil.so) list:969:26: std::list<nix::Trace>::__link_nodes_at_front (inlined)
      (libnixutil.so) list:1247:3: std::list<nix::Trace>::push_front(nix::Trace&&) (inlined)
      (libnixutil.so) ../error.cc:32:16: nix::BaseError::addTrace(...)
      (libnixexpr.so) ../eval.cc:898:7: nix::EvalState::addErrorTrace<...>(nix::Error&, nix::PosIdx, ...)
      (libnixexpr.so) ../eval.cc:1746:25: nix::EvalState::callFunction(...)
      (libnixexpr.so) ../eval.cc:1853:11: nix::ExprCall::eval(...)
      (nix) eval-inline.hh:142:23: nix::ValueStorage<8ul, void>::force(...)
      (libnixexpr.so) ../primops.cc:1207:15: nix::prim_tryEval(...)
      ...
      (libnixexpr.so) ../parallel-eval.cc:297:89: nix::prim_parallel(...)::$_0::operator()() const
      (libnixexpr.so) ../parallel-eval.cc:114:13: nix::Executor::worker()
  ```

  Other runs report `ptr < lower` at the same place. The same panic happens
  with no experimental feature at all: `nix eval --json --option eval-cores 8`
  of an attribute set whose attributes share one failing thunk
  ([race.nix](../tests/determinate-nix/race.nix)). There `value-to-json`'s
  `parallelForceDeep` hands the attributes to the workers.
- **Natively** there is no crash, but updates get lost. With
  `--show-trace`, the final error prints "(N duplicate frames omitted)",
  one frame for every thread that ever decorated the shared exception.
  eval-cores = 1 gives 19999 every time; eval-cores = 8 gave 19823, 19792,
  19744, 19628 and 19790 in five runs. So 150 to 370 `push_front`s were
  lost to the race each time.
- **ThreadSanitizer** (a native TSan build of the same source, `withTSan`)
  reports it directly: write/write and read/write races in
  `BaseError::addTrace` from `Executor::worker` threads, on a heap block
  allocated by `__cxa_allocate_exception` in `primop_throw`. It happens for
  race3.nix and for the `nix eval --json` variant.
  [tests/determinate-nix/tsan-addtrace.txt](../tests/determinate-nix/tsan-addtrace.txt)
  has one full report.

Nixpkgs has plenty of shared failing thunks: aliases that throw, `meta`
checks, broken packages reached along several paths. So with eval-cores > 1
this can corrupt the heap in ordinary evaluations that hit errors, not only
in contrived ones.

The single-threaded half of the problem is shared with upstream Nix 2.35
(it has `Failed` values too). Every later forcing of a failed thunk prepends
its frames to the one exception, so an error reports frames from unrelated
earlier forcings. In [pollute.nix](../tests/determinate-nix/pollute.nix),
the error from `builtins.sub bad 2` shows "while calling the 'add' builtin"
from an earlier `tryEval (builtins.add bad 1)`, in both Nix 2.35.2 and
Determinate Nix.

**Proposed fix**
([patches/determinate-nix/proposed-fix-rethrow-failed-value-copies.patch](../patches/determinate-nix/proposed-fix-rethrow-failed-value-copies.patch),
not applied in the port): never let anyone modify the stored exception.
`force()` stores a clone (`throwClone`) in `Value::Failed`, because the
failing thread's own catch sites keep decorating the exception in flight.
Every later forcing then rethrows a fresh clone of the stored one:

```c++
if (InternalType(p0_ & 0xff) == tFailed) {
    try {
        std::rethrow_exception((std::bit_cast<Failed *>(p1))->ex);
    } catch (BaseError & e) {
        e.throwClone();
    }
}
```

Checked with native builds of the patched source:

- race3.nix gives the same six-frame trace with eval-cores 1 and 8, with
  no "duplicate frames".
- pollute.nix no longer shows the unrelated 'add' frame.
- A TSan build of the patched source reports no `addTrace` races for
  race3.nix or race.nix (two runs each). Only the `trylevel` race below is
  left.

The native functional suite passes with the patch, after one expected
output is updated. That output is
`eval-fail-memoised-error-trace-not-mutated`, whose comment promises a fresh
exception on every forcing but whose `.err.exp` recorded the mutation.

### 2. `EvalState::trylevel` is a plain `int` shared by all threads

TSan also reports `prim_tryEval`'s `MaintainCount trylevel(state.trylevel)`:
all threads increment and decrement it without synchronization. Only the
debugger reads it, and the debugger turns parallel evaluation off, so the
effect is harmless today. It is still undefined behaviour and pollutes TSan
output. An atomic or thread-local counter would fix it.

### 3. The symbol table's arena is never unmapped

`ContiguousArena` (`src/libexpr/symbol-table.cc`) maps 1 GiB per
`SymbolTable` and has no destructor, so every destroyed `EvalState` leaks
its symbol pages, plus 1 GiB of address space. That matters for long-lived
processes and test binaries that create many `EvalState`s. Patch 0005 adds
the `munmap`. Found while investigating the Fil-C memory blow-up in porting
change 4; not a safety issue.

## What was checked and came out clean

Under Fil-C, every one of these would have trapped on a use-after-free,
out-of-bounds access or capability loss in the parallel evaluator. None did:

- The thunk state machine (thunk → pending → awaited, `waitOnThunk`,
  `notifyWaiters`, the waiter domains), `Executor` workers,
  `parallelForceDeep` in `value-to-json`, `builtins.parallel`, and the
  concurrent symbol table and `boost::concurrent_flat_map`s. They ran
  through the whole Nixpkgs and NixOS evaluations above, at 8 threads, with
  results identical to native Nix.
- The whole functional suite with eval-cores = 8. It differs from
  eval-cores = 1 only as expected: stack-overflow errors are reported one
  frame deeper (`eval-fail-toJSON-stack-overflow`,
  `eval-fail-derivation-structuredAttrs-stack-overflow`), and the debugger
  warns that it disables multi-threading (`repl/debugger-*`). The parallel
  variant drops those cases.

Observed but not a bug: `ValueStorage::isTrivial()` reads `p1` before `p0`.
That can pair a finished value's payload with a still-pending tag and
`dynamic_cast` it as an `Expr *`. Its only caller is flake input parsing,
which is single-threaded.

Memory: Fil-C Determinate Nix needs about 2.5 to 3 times native RSS. Four
NixOS systems peak at 8.2 GB against 2.5 GB natively. The Nixpkgs sweep was
therefore run in 16 chunks of about 1,560 attributes each, peaking at
7 to 10 GB per process
([tests/determinate-nix/drvs-chunk.nix](../tests/determinate-nix/drvs-chunk.nix)).
