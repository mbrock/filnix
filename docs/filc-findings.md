# Fil-C behaviour found while porting

Compiler and runtime findings from package builds, for reporting upstream.
Each has a filnix workaround, noted below.

## Atomic pointer loads miss later integer stores

After an atomic pointer store or CAS to a word, the runtime keeps the value
in an atomic box referenced from the word's aux slot. A later plain *integer*
store to the same word writes only the primary word. Non-atomic pointer loads
then see the new address, but atomic pointer loads return the stale box:

```c
static intptr_t slot;
__atomic_store_n((void **)&slot, (void *)(intptr_t)12, __ATOMIC_SEQ_CST);
slot = -1;
/* __atomic_load_n((void **)&slot, ...) still returns 12 */
```

A plain *pointer* store clears the box, so the value is only stale when the
atomic and plain accesses use different types. libgit2's config cache does
this: it fills `intptr_t configmap_cache[]` with atomic pointer operations
and clears it with integer stores, so config changes after the first lookup
were ignored. `patches/libgit2-configmap-cache-clear.patch` clears it
atomically.

## `clang++` ran in C driver mode

The wrapper execs `clang-20`, and Clang picks its driver mode from its name.
C++ links therefore lacked `-lm`, and `clang++ file.c` compiled C.
`compiler/filc.nix` now passes `--driver-mode=g++`. Upstream's own layout
invokes `clang++` directly and is unaffected.

## Handlers for SIGSEGV and friends are refused

`sigaction` for SIGSEGV, SIGBUS, SIGILL, SIGFPE and SIGTRAP keeps the default
action, so a self-sent SIGSEGV kills the process (Alien::Build's
`test_alien.t`). This is deliberate (`is_unsafe_signal_for_handlers`).

Boost.Test's execution monitor installs such handlers at startup. The Boost
port leaves the refused signals uncaught and keeps the rest, so SIGALRM
timeouts still fail the test. `abort()` stops the process directly rather
than raising SIGABRT, so an aborting test case ends the run.

## Pointer tag bits must not round-trip through integers

Converting a pointer to an integer and back drops its capability. Optimized
code sometimes survives because LLVM folds `inttoptr(ptrtoint(p) & mask)`
into `llvm.ptrmask`, but `-O0` builds do not. Boost.Function stored a flag in
bit 0 of its vtable pointer this way, so every call trapped at `-O0` (Boost.
Test's runner in the boost check). Use `zorptr`/`zandptr` from `stdfil.h`.

## Unsupported: `sigaltstack`, `llvm.debugtrap`, `ptrace`, `seccomp`

doctest's self-tests use the first two, strace needs `ptrace`, and
libseccomp called `seccomp` (syscall 317). Nix is built without seccomp
filtering.

These stop the program rather than fail with `ENOSYS`, so code that probes
for them dies. The `seccomp()` syscall is missing, but
`prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, ...)` passes through and
installs a filter for the whole process, runtime threads included.
`patches/libseccomp-filc-no-seccomp-syscall.patch` makes libseccomp treat
the syscall as absent, as on kernels before 3.17: API level 1, filters
loaded with `prctl`, and `EOPNOTSUPP` for TSYNC and user notification.
`tests/libseccomp-prctl-filter.c` loads a filter in the build.

libseccomp's tests call `seccomp` (syscall 317). Nix is built without
seccomp filtering. Catch2 and doctest run their fatal-signal handlers on a
`sigaltstack`; their ports and consumers set `CATCH_CONFIG_NO_POSIX_SIGNALS`
and `DOCTEST_CONFIG_NO_POSIX_SIGNALS`. The Catch2 v2 port defines it in the
single header under `__FILC__`, which fixed all 81 of CLI11's tests.
UnitTest++'s `CrashingTestsAreReportedAsFailures` calls a null function
pointer and expects its SIGSEGV handler to report it; it is excluded.

## x86 inline assembly needs an explicit "cc" clobber

Clang marks every x86 `asm` statement as clobbering the flags (`~{flags}`),
as GCC does, but FilPizlonator only accepts flag-setting instructions when
the source also names `"cc"`. Otherwise-valid code such as oneTBB's
`__asm__("bsr %1,%0" : "=r"(pos) : "r"(n))` is rejected at run time.

## Local pointer arrays at -O0 were not all GC roots

libopus 1.6.1's `test_opus_decode` and `test_opus_encode`, built as Nix builds
them (meson `--buildtype=plain`, so `-O0`), freed and reused live decoders.
The cause was in FilPizlonator's frame layout: a local that is accessed
at computed offsets gets an explicit stack aux, whose address goes in a
frame "lowers" slot so the collector can scan it. Slots were assigned by
interference, but edges were only added at `llvm.lifetime.start`, and
clang emits no lifetime markers at -O0. Every such local then shared one
slot, and the collector saw only the stack aux of whichever local was
initialized last. With two local pointer arrays, the objects held by the
first were collected (`checks.gc-local-arrays`):

```c
int *objs[10], *other[10];
for (int t = 0; t < 10; t++) { objs[t] = malloc(20000); objs[t][2] = t; other[t] = 0; }
/* allocate a lot; objs[t][2] reads back as 0 */
```

The fork makes each always-live explicit local interfere with every other
one. This affected every meson package in Nixpkgs, since `plain` means no
`-O`. Clues on the way: making the test's `dec` array static, or letting its
address escape, hid the bug, and so did deleting later code in the function
that never ran before the crash.

## `<fenv.h>` stopped the program

User glibc's x86_64 `fegetround`, `fesetround`, `fegetenv`, `fesetenv`,
`feholdexcept`, `fegetexcept`, `fedisableexcept`, `fegetmode` and the rest
used inline assembly with memory operands (`fnstcw`, `fldcw`, `fnstenv`,
`fldenv`, `stmxcsr`, `ldmxcsr`), which FilPizlonator rejects when the code
runs. Only `feclearexcept`, `feenableexcept` and `fetestexcept` went through
runtime natives. libopenmpt's tests and oneTBB's FPU-state capture hit this.
The fork now uses the MXCSR builtins, `zmath_getcw`/`zmath_setcw` and the
register form of `fnstsw`; the x87 status word cannot be loaded, so flags
that `fldenv` would put there go to MXCSR instead (`checks.fenv`).
`sysdeps/x86/fpu/fenv_private.h` used the same instructions for the x87 hold
and restore paths and is fixed too.

## Asynchronous `pthread_cancel` does not stop a running thread

glibc cancels an asynchronous-cancel thread by sending it SIGCANCEL, but the
runtime reserves glibc's internal signals (`is_unsafe_signal_for_kill`), so
`pthread_cancel` only takes effect at the next cancellation point. A thread
spinning in computation is never cancelled, and joining it hangs. polkit's
runaway-script killer relies on this to stop JavaScript rules that loop;
its test hung and is excluded, and a looping rule would hang polkitd.

## A pointer at a misaligned offset in a constant crashes the compiler

```c
struct ext { unsigned len; void *ptr; } __attribute__((packed));
static char buf[4];
const struct ext e = { sizeof buf, buf };
```

fails `Assertion '!(Offset % WordSize)'` in `computeConstantRelocations`
(BlueZ's MIDI test, through ALSA's `snd_seq_ev_ext`). The fork briefly fell
back to a run-time initializer here; Filip Pizlo pointed out that this is
unsound and introduces a GC crash, and it is reverted (mbrock/fil-c
`d6cbb69`). The only right fix is at the source: don't pack structs that
hold pointers. `patches/alsa-seq-unpacked-pointers.patch` drops `packed`
from ALSA's `snd_seq_ev_ext` and `snd_seq_ev_quote` under Fil-C, which grows
`snd_seq_event_t` from 28 to 32 bytes: the ALSA sequencer no longer matches
the kernel's layout, while PCM audio is unaffected.

## `[[clang::annotate]]` on a function crashed the compiler

An annotated function that a translation unit uses makes Clang emit
`@llvm.global.annotations` (appending linkage, section `llvm.metadata`), and
FilPizlonator fails `Assertion 'G.getLinkage() != GlobalValue::AppendingLinkage
|| ...'` in `lockDownLinkage`, which only allows the ctor/dtor and used lists.
Abseil 20260107's `ABSL_REFACTOR_INLINE` puts `[[clang::annotate("inline-me")]]`
on the deprecated `MutexLock(Mutex*)` constructors and other inline functions,
so protobuf, re2 and every other abseil user crashed the compiler.
`patches/abseil-cpp-no-refactor-annotate.patch` drops the annotation; the
pass could simply delete `llvm.global.annotations`, which codegen discards.

Any annotated function or global does it, used or not:

```c
__attribute__((annotate("realtime"))) void f(void) {}   /* assertion failure */
```

Rubber Band 4.0 marks its real-time entry points this way (`RTENTRY__` in
`src/common/sysutils.h`); the port defines it empty. This is not a
regression from the common-symbol change below: upstream's assertion is
the same. Annotations on locals and fields, and `__builtin_annotation`,
compile but stop the program when they run ("Unhandled intrinsic:
llvm.var.annotation", `llvm.ptr.annotation`, `llvm.annotation`).

`patches/fil-c/filpizlonator-annotations.patch` (fork branch
`orb/toolchain-asm`, tested with the dev LLVM build) erases
`llvm.global.annotations` and its now-unused `llvm.metadata` strings at the
start of the pass, and removes the three intrinsics as codegen does (tests
`annotateglobal`, `annotateglobalO0`, `annotateglobalfail`). The Abseil and
Rubber Band workarounds can go once filnix pins it.

## Version scripts with `extern "C++"` blocks abort the driver

The Fil-C driver parses version scripts itself to rename symbols, fails on
`extern "C++" { *google*; };` ("Failed to parse version script ... Expected
;") and then hits `UNREACHABLE` in `Gnu.cpp`. protobuf's `libprotobuf.map`
uses this form; the port turns the maps off with
`-Dprotobuf_HAVE_LD_VERSION_SCRIPT=OFF`.

## Byte-wise copies drop capabilities

Swapping or copying an object that contains pointers byte by byte (for
example `std::swap_ranges` over `char*`, as protobuf's `internal::memswap`
and `MicroString::InternalSwap` do) keeps the addresses but not the
capabilities, since only pointer-sized pointer stores write the shadow
space. The next dereference traps with "cannot read pointer with null
object". `memcpy`/`memmove` preserve capabilities, but only when source and
destination have the same alignment within a word: protobuf's generated
`InternalSwap` calls `memswap<N>` on a field range that can start at a
4-byte offset, so a plain `char tmp[N]` still lost the pointer of a
`RepeatedField` after a swap. The port swaps through a buffer offset to the
source's misalignment.

## Linker-generated `__start_`/`__stop_` section symbols are not visible

Code that collects descriptors in a named section and walks it with
`__start_SECTION`/`__stop_SECTION` fails to link: the references become
`pizlonated___start_SECTION`, which the linker does not define. ELL, BlueZ
(`patches/bluez-no-debug-section.patch`) and weston's test runner use this
pattern; the ports disable pattern-selected debug output or register the
entries from constructors. protobuf 33/34 use it for weak descriptor
defaults (`pb_defaults`, only when `PROTOBUF_DESCRIPTOR_WEAK_MESSAGES_ALLOWED`),
which the port turns off; `libprotobuf.so` otherwise fails to load with an
undefined `pizlonated___stop_pb_defaults`.

Declared weak and hidden, as in `<lttng/tracepoint.h>`, the references link, but
using one does not give a null pointer: the program jumps to a bad address
and gets SIGSEGV. This happens for any undefined global declared both weak
and hidden; plain weak references are null as expected:

```c
extern int x __attribute__((weak));                        /* &x == 0 */
extern int y __attribute__((weak, visibility("hidden")));  /* &y: SIGSEGV */
```

Every lttng-ust-instrumented program crashed in its tracepoint constructor;
`patches/lttng-ust-tracepoint-ctor-registration.patch` registers each
tracepoint from its own constructor instead.

## `get_mempolicy` checks one word too many of the node mask

`zsys_get_mempolicy` checks `ceil(maxnode / 64)` words of the node mask, but
the kernel copies `ALIGN(maxnode - 1, 64) / 8` bytes. libnuma passes its
mask size plus one as `maxnode`, so `numa_preferred()` with a 1024-bit mask
fails the check (136 bytes against a 128-byte mask). lttng-ust is built with
`--disable-numa` until the runtime matches the kernel.

## `membarrier` stops the program

Like the syscalls in the unsupported list, `membarrier` (324) stops the
program rather than failing with `ENOSYS`, so liburcu's memb flavor and
lttng-ust's copy of it died in their constructors while probing it. Both
already have a fallback for headers without `__NR_membarrier`; the ports
use it under Fil-C (`patches/liburcu-filc.patch`,
`patches/lttng-ust-no-membarrier.patch`).

## `dlopen` of a bare soname ignores the caller's RUNPATH

`dlopen("libnss_dns.so.6662")` fails in a Fil-C program even though the
library sits in the Fil-C sysroot's lib directory and that directory is in
the program's RUNPATH. Nix preloads nss_dns this way and warns, which NixOS's
nix.conf check turns into an error; the Nix port passes libc's full path
instead. Adding the sysroot lib directory to the loader's trusted
directories would fix NSS module loading in general.

## Plugins could not call back into the executable (libtool `-dlopen self`)

slapd's test083-argon2 failed with `symbol lookup error` when `argon2.so`
called `lutil_passwd_add` in the slapd executable. The toolchain is not at
fault: with `-rdynamic` or `-Wl,--export-dynamic`, a Fil-C executable lists
`pizlonated_f`, `pizlonatedFI<n>_f` and `pizlonatedFIP<n>_f` in `.dynsym`, and
a dlopened plugin resolves them. slapd was linked without that flag.

OpenLDAP links slapd with libtool's `-dlopen self`. Libtool turns that into
`--export-dynamic` only when configure found that "a program can dlopen
itself", which is a run test. Fil-C is a cross target, so the test reports
`cross`, and libtool falls back to a preloaded symbol table (`slapdS.o`),
which does not export anything to plugins. `toolchain/libtool-dlopen-self-hook.sh`
presets `lt_cv_dlopen_self=yes` for every Fil-C build, since Fil-C programs
run on the build machine. OpenLDAP's full test suite then passes. Packages that
use Meson's `export_dynamic` or pass `-export-dynamic` to libtool directly
were not affected.

## `accept` and `recvfrom` reject a length pointer with a null address

`accept(fd, NULL, &len)` stops the program ("cannot write pointer with null
object") in `handle_returned_addr`, which checks the address buffer for
`*len` bytes whenever the length pointer is non-null. Linux ignores the
length when the address is null, and NSPR's `PR_Accept(fd, NULL, ...)`
relies on that; `recvfrom` shares the helper. The NSPR port passes no length
when it wants no address (`patches/nspr-null-peer-address.patch`).

## Function descriptors bind to an interposable implementation symbol

A Fil-C function `f` is exported as a small `pizlonated_f` that returns a
descriptor, and the descriptor refers to the code through a default-visibility
symbol, `pizlonatedFIP<n>_f`, with an `R_X86_64_64` relocation. The dynamic
linker resolves that relocation in the global scope, so when two libraries
define the same function, the one loaded first supplies the code for both
descriptors. `RTLD_LOCAL` no longer isolates a library:

```c
/* liba.so: int which(void) { return 1; }   (linked into main)
 * libb.so: int which(void) { return 2; }   (dlopened RTLD_LOCAL) */
int (*f)(void) = dlsym(dlopen("libb.so", RTLD_LOCAL | RTLD_NOW), "which");
f();  /* 1 under Fil-C, 2 natively */
```

sdl12-compat exposed this. It defines the SDL 1.2 API as passthroughs to
functions it looks up with `dlsym` in an `RTLD_LOCAL` libSDL2 (sdl2-compat),
which exports the same names. `dlsym(libSDL2, "SDL_strrchr")` returned a
descriptor pointing back into sdl12-compat, which recursed until the stack
overflowed. Linking the dlopened library with `-Wl,-Bsymbolic-functions`
resolves its descriptors at link time (the sdl2-compat port does this), and
libraries with a `local: *` version script, like SDL3, are not affected.
Binding the descriptor to a local alias of the implementation would give
native `dlsym` semantics.

## A 55,000-line parser takes 50 minutes and 6.7 GB to compile

PostgreSQL's Bison parser, `src/backend/parser/gram.c` (54,771 lines: about
30,000 lines of tables, then `base_yyparse` with a 2,279-case action
`switch`), took
Fil-C's Clang 50 min 32 s (2,951 s user) and 6.7 GB peak RSS to compile. Clang
20.1.8 without Fil-C took 1.55 s and 179 MB with the same flags (no `-O`, so
`-O0`, plus `-ggdb` and `-fdata-sections -ffunction-sections`, as the Nixpkgs
recipe produces). Stack samples with `eu-stack` during the compile were in
`FilPizlonatorPass`: `Pizlonator::emitChecks` splitting blocks through
`SplitBlockAndInsertIfElse` (then `BasicBlock::replaceSuccessorsPhiUsesWith`),
`Pizlonator::optimizedAccessCheckOrigin` creating origin globals (each with a
unique name from `ValueSymbolTable::makeUniqueName`), and
`Pizlonator::getOrigin` uniquing constant structs. That points to costs
that grow with function size, not total code size.

Reproduce with the recipe's configure, `make -C src/backend
generated-headers`, and the recipe's compile command for `gram.o`. Building
`postgresql` for Fil-C also needs `jitSupport = false` (LLVM is out of scope)
and a replacement for its `-flto` flag (see the libpq port).

sdl12-compat hit a similar function-size cost: one startup function that
inlines a symbol loader for each of about 340 SDL2 functions took
873 s and 3.8 GB at `-O3`, and 30 s and 0.3 GB with the loader marked
`noinline` (`patches/sdl12-symbol-loader.patch`; `sdl2-symbol-loader.patch`
does the same for sdl2-compat).

## Pointer tagging works; integer-typed storage loses capabilities

Setting tag bits in a pointer is fine under Fil-C. What drops a capability
is keeping the pointer in an *integer-typed* location. Upstream's
`gimso_semantics.md` and `invisicaps_by_example.md` give the rules; this
matrix (filcc at the current pin, `-O0` and `-O2`, with each store and load
in a separate `noinline` function) shows them in
practice:

| Pattern | -O0 | -O2 |
| --- | --- | --- |
| Tag and untag with integer math inside one expression (`(T *)((uintptr_t)p & ~7)`) | ok | ok |
| Same, through a local `uintptr_t` variable | trap | ok |
| Pointer-typed field or union member, tagged with pointer arithmetic or `zorptr` | ok | ok |
| Pointer stored, tag bits set by an integer read-modify-write of the same slot, then loaded *as a pointer* | ok | ok |
| `uintptr_t` field, heap array, union member written as an integer | trap | trap |
| `_Atomic uintptr_t` / `std::atomic<uintptr_t>` | trap | trap |
| Tagged value passed or returned as `uintptr_t` | trap | trap |
| NaN-boxing style high-bit tags in a `uintptr_t` | trap | trap |

Two rules explain it. The FilPizlonator can recover a capability across a
ptr→int→int-math→ptr chain when it sees the original pointer in the same
value flow (so optimized code and single expressions work, while `-O0`
spills to integer-typed stack slots). In memory, a slot's capability lives in
the shadow space and is written only by *pointer* stores: an integer store
updates the address but keeps the previous capability, and an integer load
never carries one. So a tagged representation keeps working if the words are
declared and loaded as pointers (a `void *` or a pointer member of a union),
with tag math done by pointer arithmetic, `zorptr`/`zandptr`/`zretagptr`
from `<stdfil.h>`, or integer math on a pointer-typed load. Rewriting the
whole representation is rarely needed.

Examples: oneTBB's `queuing_rw_mutex` keeps a flag bit in queue pointers held
in `std::atomic<uintptr_t>`, and PulseAudio's `pa_atomic_ptr_t` stored pointers
as `uintptr_t`; both ports change only the atomic's type to a pointer and set
the bit with pointer arithmetic. Boost.Asio's `io_context::basic_executor_type`
keeps `io_context* | runtime_bits` in a `uintptr_t target_`, so the first
`use_service` through a strand traps;
`patches/boost-asio-io-context-executor-pointer.patch` makes it a `char *`
(in the Boost 1.86 and 1.87 ports, and as
`patches/asio-io-context-executor-pointer.patch` for standalone Asio).
z3's region and stack allocators chain pages through a header word
holding the previous page with a flag in bit 0, and the stack keeps its
marks the same way, all as `size_t`; `test-z3 -a` trapped in
`region::~region()`. `patches/z3-page-headers-pointers.patch` keeps them
as `char *` and tags with pointer arithmetic. Nix's own bit-packed `Value`
takes the same fix in Determinate Nix, where parallel evaluation depends on
that layout. oneTBB's tbbmalloc is a different problem: it
carves objects out of raw `mmap` chunks, which have no per-object capabilities,
so the port builds without it.

NSPR's arena allocator (`PLArena`, used by all of NSS) keeps `base`, `limit`
and `avail` as `PRUword` and hands out `(void *)a->avail`, so every arena
allocation was a pointer without a capability. The fields are public, so
`patches/nspr-arena-pointer-provenance.patch` keeps them and instead
rebuilds each pointer from the arena header, which starts the block:
`(char *)a + (a->avail - (PRUword)a)`.

Copying memory keeps capabilities only for words that stay 8-byte aligned.
`memcpy` of a struct holding a pointer to `buf + 12` and back loses the
pointer's capability (at `buf + 8` it survives). NSS's softoken saves a
digest's state behind a 12-byte header, and SHA-256's context holds
function pointers, so every restored context (`PK11_CloneContext`, used
for the TLS 1.3 transcript hash) trapped when called.
`patches/nss-softoken-state-alignment.patch` pads the header to 16 bytes.

Constant-time selection by XOR-masking two pointers cannot keep either
capability. NSS swaps the real and fake RSA premaster keys this way
(`ssl3_CSwapPK11SymKey`), which broke every TLS RSA key exchange;
`patches/nss-ssl-cswap-symkey.patch` selects through a two-element array
under Fil-C.

netCDF kept NCZarr's chunk-cache nodes in an `ncexhash` map whose data is
a `uintptr_t` (`patches/netcdf-exhash-pointer-data.patch` makes it
`void *`), and aligned vlen data with `(void *)NC_read_align((uintptr_t)p,
a)` (`patches/netcdf-vlen-align-pointer.patch` adds the delta to `p`).
GEOS's `IndexedPointInAreaLocator::SegmentView` packs a 2-bit offset into
a `std::size_t` copy of a coordinate pointer, which stopped every
point-in-polygon test; `patches/geos-segmentview-pointer-tag.patch` keeps
a `const char *` and tags it by pointer arithmetic.

## Huge static initializers compile very slowly

A C++ global like `const std::vector<T> v = {{...}, ... }` with a few
hundred elements builds one large constructor function, and Fil-C's
pipeline spends most of its time in SROA (`PromoteMemToReg`) on it. 400
elements of two small vectors each take minutes, compared with 3 seconds
for Nixpkgs' Clang, and time grows faster than linearly. NSS's
`pk11_gtest` and `freebl_gtest` test-vector tables took over 20 minutes per
file, so the NSS port leaves those two gtest binaries out.

gtest's own registration hits the same cost: every `TEST`/`TEST_F` adds a
`MakeAndRegisterTestInfo` call with `std::string` temporaries to the file's
static constructor. The campaign killed libyuv twice after 15 silent
minutes: its `convert_argb_test.cc` (1,748 tests) compiled at `-O3` for
over 12 CPU minutes at 11 GB before we stopped it, where Nixpkgs' Clang
takes under 90 s. `-ftime-trace` on a sixteenth of the tests put 11.4
of 59 s in `_GLOBAL__sub_I_…`, and stack samples of larger slices were in
SROA's `PromoteMemToReg` (`IDFCalculator`), in `EarlyCSE`, and in
`MemCpyOpt`'s MemorySSA updates. A quarter of the file took 8 to 9.5
minutes and 4.4 to 5.2 GB. At `-O0` the whole file takes 144 s and 5.1 GB,
so the libyuv port compiles only its test code at `-O0`.

## `dlsym(RTLD_NEXT, ...)` is a safety error

```c
void *p = dlsym(RTLD_NEXT, "puts");
/* filc safety error: cannot access pointer with null object
   (ptr = 0xffffffffffffffff,<null>) in zsys_dlsym */
```

`zsys_dlsym` treats the handle as a pointer to a loaded object, so the
`RTLD_NEXT` (and presumably `RTLD_DEFAULT`) pseudo-handles trap instead of
being looked up. Determinate Nix interposes `__cxa_throw` this way (to abort
on `std::logic_error`), so every thrown exception stopped the program; the
port builds without the interposer (docs/determinate-nix.md).
rsync's `source-change-size-continues` test LD_PRELOADs a shim that
wraps `read` this way; the port excludes that test.

## `syscall()` returns -1 as 4294967295

`syscall` is declared to return `long`, but a failing call returns the
32-bit -1 zero-extended:

```c
long r = syscall(__NR_fchmodat2, AT_FDCWD, "/nonexistent", 0600, AT_SYMLINK_NOFOLLOW);
/* r == 4294967295, errno == ENOENT; the same for openat2. getpid works. */
```

So `if (syscall(...) < 0)` never sees the failure. Determinate Nix calls
`openat2` and `fchmodat2` this way; its `fchmodatTryNoFollow` test failed
(no error for a missing file or a symlink), and a failed `openat2` would
have become file descriptor 4294967295. The port truncates both results to
`int`.

## A contended failed pointer CAS writes back an address without its capability

When `compare_exchange_strong` on a `std::atomic<T *>` fails because another
thread has just installed a pointer, the value written back to `expected`
sometimes has the winner's address but no capability. A plain load of the
same atomic right afterwards has the capability.
[tests/determinate-nix/filc-cas-expected.cc](../tests/determinate-nix/filc-cas-expected.cc)
has 8 threads race to fill slots and counts `!zhasvalidcap(expected)` after
failed CASes. It reports 3 to 65 such writebacks per run with both the
batch toolchain (fa8c296) and the previous pin, and 0 after a load. The
single-threaded case is fine. Determinate Nix's `ChunkedVector::ensureChunk`
returns `expected` to the thread that lost the race, so its `ConcurrentAdd`
test sometimes trapped writing through the chunk (about 1 run in 10). The
port reloaded after a failed CAS (patch 0006) until mbrock/fil-c 18b27e5
fixed `filc_strong_cas_ptr_with_manual_tracking`. Its non-box path read the
slot's `lower_or_box` and then the address. Another thread that installed
a box in between left the new address paired with the stale (null) lower.
The fix re-checks `lower_or_box` and retries. The reproducer is in the fork
as `filc/tests/casexpectedcap`.

## Found by Fil-C: a use-after-free in libopenmpt's locale decoding

Not a Fil-C issue, but a bug it caught. libopenmpt 0.8.9's
`decode_locale_impl` (`src/mpt/string_transcode/transcode.hpp`) grows its
output vector when the codecvt facet returns `partial`, then `continue`s,
but `out_next` still points into the freed buffer and the do-while
condition does not continue on `partial`, so it returns
`std::wstring(out.data(), out_next)` from a dangling pointer. libc++
returns `partial` for characters the C locale cannot convert, so
libopenmpt's own test suite hits it; Fil-C reported a 100 MB read from a
128-byte object. `patches/libopenmpt-codecvt-partial.patch` fixes it and
is worth sending upstream.

## Autoconf's `sigsetjmp` probe crashes the compiler

`AC_CHECK_FUNCS([sigsetjmp])` compiles `char sigsetjmp(); ... sigsetjmp();`,
and FilPizlonator stops with ``Assertion `F.getFunctionType() ==
SigsetjmpTy' failed`` ("Unexpected setjmp signature: i8 (...)"). The probe
then reports the function missing. Real `<setjmp.h>` callers are fine; a
diagnostic instead of the assertion would be enough. Seen in pth's
configure, whose SUSv2 `makecontext` probe also failed (it passes a
`void (*)(void *)`, which Clang rejects), so pth picked a `setjmp` backend
that patches the `jmp_buf` stack pointer. The port selects pth's
`makecontext`/`swapcontext` backend, which Fil-C supports.

## Exceptions thrown during another unwind reuse its state

`nix-store --store 'local?read-only=true' --add FILE` (with
`extra-experimental-features = read-only-local-store`) stopped in
`landing_pad` with "cannot read pointer to free object" when SQLite's
read-only error propagated, and so did a failing substitution
(`substitution-goal.cc:228`) and nix-util-tests'
`decompress.decompressInvalidInputThrowsCompressionError`. The functional
tests `read-only-store`, `binary-cache` and
`multiple-outputs-substitute-failure` were skipped for it and the gtest
excluded.

The runtime keeps the unwind state (context, exception, the frame phase 1
found, the forced-unwind callback) in `filc_thread` rather than in the
exception, and the compiler's `resume` does not pass the exception back. So
a second unwind that starts before the first finishes overwrites it:

- A destructor running as a cleanup throws and catches its own exception.
  The outer `resume` then continued with the inner exception, which
  `__cxa_end_catch` had already freed, and the next personality call
  trapped. Natively the landing pad hands its own exception to
  `_Unwind_Resume`.

  ```cpp
  struct Cleanup { ~Cleanup() { try { throw 42; } catch (int) {} } };
  void f() { Cleanup c; throw std::runtime_error("outer"); } /* traps */
  ```

- Fibers. Nix's `sourceToSink` runs in a boost coroutine2 fiber. The
  coroutine's exception is rethrown in the caller, whose cleanup destroys
  the coroutine, which switches back to the fiber and unwinds it by
  throwing `forced_unwind`. Both stacks' unwinds shared the one per-thread
  state (`filc_resume_unwind` asserted `found_frame_for_unwind`).

The runtime fix (`patches/fil-c/runtime-exception-unwind.patch`, fork
branch `filnix`) saves the outer state when an inner raise finds its
handler and restores it when the inner exception lands, if the frame
running the outer cleanup is still live. `swapcontext` moves the state into
the context it leaves and restores the target's. The reproducers are in
`tests/fork-regressions/exception-unwind` and the fork's
`filc/tests/nestedexceptioncleanup` and `fiberexceptionunwind`.

The functional tests only failed once they ran the Fil-C `nix`: Nixpkgs
puts `nix-cli.__spliced.hostHost or nix-cli` on the suite's PATH, the scope
here has no `__spliced`, and the build platform's Nix was tested instead.
That is also why the `plugins` test failed: a Fil-C plugin loaded into
native Nix finds no `pizlonated_*` symbols. With the Fil-C `nix`, it passes.

Determinate Nix hit the same bug (its read-only store command, the
substitution tests and the libutil `invalidDecompression` tests); with
fa8c296 pinned its port no longer skips them.

## Found by Fil-C: pointer rebasing across buffers in FFmpeg's flashsv2

`libavcodec/flashsv2enc.c` copies its frame blocks to key blocks and rebases
their pointers with `key_blocks[i].enc += (s->keybuffer - s->encbuffer)`. The
address lands in `keybuffer`, but the pointer is still derived from
`encbuffer`, which is undefined behaviour in C; Fil-C refused the read
(`fate-vsynth1-flashsv2`). The port writes
`keybuffer + (enc - encbuffer)`. FFmpeg 8.1 also stores its `av_log`
callback in an `atomic_uintptr_t`, dropping the function pointer's
capability.

libyuv's `InterpolatePlane` and `InterpolatePlane_16` do the same: they pass
`src1 - src0` as the row stride, so the kernels read the second plane as
`src0 + stride` (`TestARGBInterpolate`).
`patches/libyuv-interpolate-planes.patch` blends through both pointers
under Fil-C. The port also defines `LIBYUV_DISABLE_X86`: libyuv's x86 row
kernels are inline assembly with memory operands, which Fil-C refuses.

## `__sync_*` builtins on pointers drop the capability

Clang lowers `__sync_bool_compare_and_swap`, `__sync_val_compare_and_swap`
and `__sync_lock_test_and_set` on pointer operands to `ptrtoint` and an
integer `cmpxchg`/`atomicrmw xchg`, so the stored pointer has no capability
and the next dereference traps, whether the load is atomic or not:

```c
static int x = 42;
int *g;
__sync_bool_compare_and_swap(&g, 0, &x);
*g;   /* cannot read pointer with null object */
```

The `__atomic_*` builtins keep pointers intact. cffi's `_embedding.h` locks
Python start-up this way (it stores a pointer into
`PyCapsule_Type.tp_as_buffer`), so every cffi embedding module trapped in
`Py_InitializeEx`; `patches/cffi-filc.patch` uses
`__atomic_compare_exchange_n`. Upstream Fil-C has the same lowering
(`EmitToInt` in `clang/lib/CodeGen/CGBuiltin.cpp`); keeping pointer operands
pointer-typed there would cover every package that still uses the `__sync`
builtins on pointers.

## libffi closures receive read-only arguments

The Fil-C libffi port's `ffi_closure_callback` points `avalue[i]` into the
`zargs()` buffer, which is read-only. A closure handler may write to its
by-value arguments (they are its own copies in C), and cffi's
`test_callback_large_struct` does (`s.a += 1` on a struct argument):

```c
static void handler(ffi_cif *cif, void *ret, void **args, void *data) {
    *(int *)args[0] += 1;   /* cannot write to read-only object */
}
```

Copying each argument into its own buffer fixes it (`avalue[i] = memcpy
(alloca (size), argp, size)` in `src/x86/ffi64.c`; the handler above and the
cffi test then pass, as does libffi's test suite). That change rebuilds
everything above libffi, so for now cffi skips the test.

## cffi

cffi 2.0 works with these changes (`patches/cffi-filc.patch`):

- `ffi.callback()` needs libffi's `ffi_closure_alloc()`; cffi's own
  write+execute trampoline allocator fails under Fil-C.
- The type-building recursion limit is 200 instead of 1000 levels: each level
  takes about 20 KB of stack under Fil-C, so the stack overflowed before
  cffi could raise its RuntimeError.
- The pure-Python ctypes backend (`FFI(backend=CTypesBackend())`) does not
  work: it passes addresses through `ctypes.cast()` from integers. The
  default `_cffi_backend` is unaffected.
- `ffi.cast("int *", some_int)` and function pointers round-tripped through
  `intptr_t` trap when used, as Fil-C intends.

## Records containing unions are passed as integers

Fil-C's clang sends every union argument and return value through memory,
but a struct that *contains* a union still goes through the normal x86-64
register classification. That picks each eightbyte's type from the union's
IR type, so when the union's IR type is an integer and the pointer sits in
another member, the pointer travels as `i64` and loses its capability:

```c
static int x;
union U { long l; void *a[1]; };
struct W { union U u; long tag; };
struct W make(void) { struct W w; w.u.a[0] = &x; return w; } /* { i64, i64 } */
/* make().u.a[0] has no capability; passing a W as an argument is the same */
```

Only records of at most 16 bytes are affected (larger ones go in memory).
`std::variant<long, int *>` returned by value loses its pointer this way.
fmt's one-argument `format_arg_store` comes back as `{ ptr, i64 }`, so a
custom-type argument keeps its object pointer but loses its formatter
function pointer: `fmt::vformat("{}", fmt::make_format_args(seconds(42)))`
stops, as would spdlog, which logs through `make_format_args`, with one
custom-type argument. fmt's own suite hit it through wide strings. Treating any record that
contains a union the way the fork already treats a bare union, in
`X86_64ABIInfo::classifyArgumentType` and `classifyReturnType`, would fix
it. `patches/fmt-arg-store-in-memory.patch` makes fmt's store 32 bytes.

## The runtime leaves FE_INEXACT set when `main` starts

C requires the floating-point status flags to be clear at program startup.
Under Fil-C, `fetestexcept(FE_ALL_EXCEPT)` already returns `FE_INEXACT` in
the first constructor:

```c
int main(void) { return fetestexcept(FE_ALL_EXCEPT); } /* 0x20; 0 natively */
```

The runtime's own code raises it in the program's thread: libpas's
allocation slow paths use floating-point heuristics, and so does other
runtime work that runs on the mutator (a single-size loop of `malloc(16)`
raised it again after about 35,000 allocations). mbrock/fil-c 2d9aa14 clears
the flags before the program starts and 702ca31 preserves them around
`verse_heap_allocate`, which makes a single allocation clean, but start-up
and later runtime work still raise it; a full fix means saving the flags
at every runtime entry that may do floating-point math, or keeping the
runtime's heuristics in integers. fmt's `float_test.isnan` checks that the
flags are clear and is excluded, and `tests/fork-regressions/fenv-*.c` are
not run yet.

## Unsupported: allocation failure

Fil-C's allocator never returns null. A request larger than the address
space (`FILC_MAX_ALLOCATION_SIZE`, `PAS_MAX_ADDRESS`) is a safety panic in
`malloc` and `operator new` alike, where glibc returns null and libc++
throws `std::bad_alloc`; smaller huge requests succeed lazily (64 TiB did).
fmt's `util_test.format_system_error` probes `std::allocator` with
`SIZE_MAX / 2` bytes and is excluded, as are two of Redis's corrupt-dump
tests, which request 2^61 bytes and expect zmalloc to fail.

## `-fno-builtin` with `setjmp` crashed the compiler

With `-fno-builtin`, Clang no longer treats `setjmp` as a builtin, so the
call is not marked `returns_twice`, and FilPizlonator asserts
`F.hasFnAttribute(Attribute::ReturnsTwice)`:

```c
#include <setjmp.h>
static jmp_buf jb;
int run(void) { if (setjmp(jb)) return 1; longjmp(jb, 1); }
/* clang -O2 -fno-builtin: assertion failure */
```

Ghostscript's configure adds `-fno-builtin` to every compile;
`patches/ghostscript-filc.patch` drops it. A proposed fork change,
`patches/fil-c/filpizlonator-setjmp-common.patch` (not yet compiled or
tested), marks `setjmp`, `_setjmp` and `sigsetjmp` and their calls
`returns_twice` by name, as GCC does, with tests `setjmpnobuiltin` and
`setjmpnobuiltinO0`. The Ghostscript workaround can go once filnix pins a
fork revision with it.

## Fil-C's and the native compiler wrapper see each other's flags

The Fil-C cc-wrapper and binutils wrapper are salted
`x86_64_unknown_linux_gnu`, the build platform's salt. The native
wrappers (`depsBuildBuild` compilers) have the same salt, so each accepts
both roles' flags: libraries in `nativeBuildInputs` put their `-L` ahead
of the Fil-C ones in Fil-C links, and Fil-C libraries reach native links.
Ghostscript's configure found the native zlib (`undefined reference to
pizlonated_deflate`), and after removing it its native `mkromfs` linked
Fil-C's `libz.so`. The port removes zlib and cups from
`nativeBuildInputs` and hands the native zlib to the auxiliary tools
alone.

Fixed: `toolchain/wrappers.nix` now salts both Fil-C wrappers
`x86_64_unknown_linux_gnufilc0` (the target prefix stays empty), and
`checks.wrapper-roles` links `-lz` with both compilers while each
platform's zlib is in scope. The Ghostscript port no longer needs its
workaround. Nothing in filnix referred to the old salt; the change
rebuilds everything built with Fil-C.

## Found by Fil-C: pointers round-tripped through file names in Ghostscript

Ghostscript's band list names its scratch files after their `IFILE` or
`MEMFILE` (`"encoded_file_ptr_%p"`, `"\377%p"`) and gets the object back
with `sscanf("%p")`. The integer has no capability, so rendering to any
banded device trapped in `clist_rewind`. The port records the encoded
pointers in a `zexact_ptrtable` and decodes them from it. `find_jmp_buf`
aligned a `jmp_buf` by casting an integer back to a pointer, and now uses
pointer arithmetic.

## `__attribute__((common))` crashed the compiler

A common symbol makes FilPizlonator assert in `lockDownLinkage`
(`G.getLinkage() != GlobalValue::CommonLinkage`), whether it comes from
`-fcommon` or from the attribute:

```c
int x;   /* clang -O2 -fcommon: assertion failure */
```

Redis's `redismodule.h` declares every module API pointer
`__attribute__((__common__))`, so `tls.c` and all test modules hit it.
Defining `REDISMODULE_ATTR_COMMON` as `__attribute__((weak))` works around
it. The same proposed patch gives common symbols weak linkage, which the
linker merges the same way (tests `commonsym`, `commonsymfcommon`, and
`commonsymfail`, which checks that a common array keeps its bounds).

## Cancellable syscalls without a runtime wrapper stop the program

Fil-C's glibc sends cancellation points through `__syscall_cancel`
(`patches/glibc-filc-cancellation.patch`). A call the Fil-C runtime does
not wrap ends in inline `syscall` assembly, which the runtime refuses:

```c
sync_file_range(fd, 0, 1, SYNC_FILE_RANGE_WRITE);
/* filc safety error: cannot handle inline asm ... syscall
   (libc.so.6666) sync_file_range.c:29: sync_file_range */
```

Redis's port falls back to `fsync`. Other cancellable calls that bypass
the runtime would stop the same way.

Some internal `*_nocancel` helpers take the same path. glibc's `nftw`
opens subdirectories with `__openat64_nocancel` when it may keep more
than one descriptor open, so a recursive walk stops the program at the
first subdirectory (Xapian's test harness `rm_rf`). With `nopenfd` 1 it
avoids that call; the Xapian port and the PipeWire experiment pass 1.

## Found porting Redis: pointers kept as bytes

Redis keeps client pointers inside rax keys (client tracking and blocked
client timeouts), swaps sort elements as `long` (`pqsort.c`, geoPoints
hold `sds` pointers), and packs its encoded reply buffers so a `robj *`
sits at any offset. Each lost or misaligned the capability. The port
(`patches/redis-filc.patch`) registers clients in a `zexact_ptrtable` and
decodes key bytes through it, swaps as `void *`, and aligns the reply
chunks. The module key-metadata API passes pointers as `uint64_t`, so
modules that store pointers there cannot work under Fil-C; its tests are
skipped.

## Target-dependent tool twins leaked into native libraries

Not a Fil-C bug but a packaging one. `ports/build-tools.nix` builds GLib
2.80.4 and gobject-introspection 1.80.1 twins whose generators emit
pointer-GType C for Fil-C. They replaced `glib` for the whole package set
whose target is Fil-C (`pkgsFilc.buildPackages`), so every native library
there that links GLib was rebuilt against 2.80.4 and fell off
cache.nixos.org. Where it needed more, it broke: Pango 1.57's pkg-config
file wants GLib 2.82, so `pangocairo`/`gtk+-3.0` lookups failed (libdecor,
i3, pangomm), glibmm-based libxml++ tests exited 127, gjs's debugger tests
failed. Fil-C packages reached these through build tools, e.g.
`sdl2-config` (native SDL → PipeWire → FFADO → libxml++) or fontforge
(DejaVu → fontconfig), so one campaign had them blocking hundreds of
packages. The Graphviz alias worked around one instance.

Fixed: the twins are named only in the Fil-C set's `pkgsBuildHost`
attribute, which splicing and `buildPackages` read; native packages inside
that set keep the ordinary GLib. Two Nixpkgs packages depend on the target
platform themselves and needed the same treatment as Qt already had: the
gobject-introspection wrapper (with a Fil-C target it wraps the scanner and
propagates the Fil-C GI) is aliased to the native one inside that set, and
PyGObject's `hostPlatform != targetPlatform` pkg-config workaround
(NixOS/nixpkgs#378447, meant for cross builds) is undone there. Native
PyGObject, and through it graphene, GTK 4, GStreamer, PipeWire and SDL,
then match the native set too. Such native tools propagate the ordinary
GLib and GI into Fil-C builds (gdk-pixbuf for GTK 3, PyGObject for
libgweather), so their `gdbus-codegen` could come first on PATH: GTK 3's
generated D-Bus code switched on GTypes and failed to compile. The twins'
setup hooks now put their generators (`gdbus-codegen`, `glib-genmarshal`,
`glib-mkenums`, the `g-ir-*` tools) and their `.pc` files first on PATH
and `PKG_CONFIG_PATH_FOR_BUILD` in a post hook; Meson finds gdbus-codegen
through the build `gio-2.0.pc`. `checks.generator-precedence` covers both.
`tests/gtk-ports.nix` checks that native Pango, GTK 3, glibmm, cairo,
sdl2-compat and PyGObject in that set match the native package set. Fil-C
packages rebuild once: every user of the twins (their setup hooks
changed), and packages whose build tools link GLib: anything under
fontconfig (DejaVu's fontforge), systemd (swtpm → json-glib), or the build
Python's Pillow (libraqm), about a third of a 520-package sample.

The Python ports' `packageOverrides` reach the build Python in the same
way. The PyGObject pin, which matches the Fil-C GI, is now applied only
when Python's host is Fil-C (`filcOnly` in `pyports.nix`). Natively,
3.48.2 failed to compile its regress test library (`_GI_TEST_EXTERN`);
the build Python now has Nixpkgs' PyGObject.

Still open: the build Python for Fil-C (`python3.pythonOnBuildForHost`)
is not the cached native Python 3.12 either. CPython's passthru forwards
every scalar override argument to its build-platform splices, so the Fil-C
port's `enableLTO = false` drops `--with-lto` there too, and the whole
native Python 3.12 package set is rebuilt (Django's timing-ratio test then
failed on a loaded builder; `pyports.nix` now drops that one noisy ratio).
Expressing the LTO change without an override argument would put that set
back on cache.nixos.org, but changes the Fil-C Python derivation and so
every Fil-C Python package.

## GType in integer storage cannot be fixed in GLib's headers

GType is a pointer under Fil-C's GLib, and the common pre-2.80 idiom keeps
it in `gsize` once storage:

```c
static gsize id = 0;
if (g_once_init_enter (&id)) {
  GType t = g_type_register_static (...);
  g_once_init_leave (&id, t);
}
return id;
```

clang rejects the store and the `return` (`-Wint-conversion` is an error),
and a cast would not help: an integer load never carries a capability, so
the returned GType would trap on first use. GLib's macros cannot repair
this, since the storage and the `return` belong to the caller; each
generator or hand-written `get_type` has to store a GType and use
`g_once_init_enter_pointer`/`g_once_init_leave_pointer` (or
`G_DEFINE_*_TYPE`, which the GLib port keeps pointer-valued at every API
ceiling). The same goes for `switch` on a GType (switch on its
`(guintptr)` value) and for clearing `G_SIGNAL_TYPE_STATIC_SCOPE` (use
`zandptr`).

Generators that write such C for the package being built are patched in
`ports/build-tools.nix`, so every consumer benefits:

- valac used the gsize path below `--target-glib=2.80`, for type
  registration and for regex literals (`patches/vala-pointer-once.patch`).
  Autotools release tarballs ship C that an older valac generated, so the
  build valac's setup hook deletes `*_vala.stamp`/`*.vala.stamp` before
  configure and make regenerates it. libgee's 1,318 test cases pass.
- gtkdoc-scangobj's scanner program switched on GTypes and masked the
  static-scope bit with `&` (`patches/gtk-doc-scangobj-gtype.patch`).

Packages with their own copies take per-package patches: libmbim (boxed
types and mkenums templates), Cogl (`get_gtype` macros and templates),
libgsf and vala-gen-introspect (switches).

## Found by Fil-C: gpgscm rebased a string port cursor across buffers

GnuPG's test interpreter (`tests/gpgscm/scheme.c`, from TinyScheme) grows
a string port with `curr -= start - str`. The address lands in the new
buffer, but the pointer still derives from the old one, freed on the next
line, so the next write trapped (`t-child.scm`), as in FFmpeg's flashsv2
above. `patches/gnupg-gpgscm-port-realloc.patch` writes
`str + (curr - start)`.

## `rep; bsf` is rejected in inline assembly

libgcrypt's OCB mode counts trailing zeros with
`asm ("rep;bsfl %k[low], %k[ntz]" ...)` (the `tzcnt` encoding) even with
`--disable-asm`, and FilPizlonator stops the program on it ("unsupported
mnemonic for safe inline asm: rep"); gnupg's `t-protect` hit it. Upstream
Fil-C's libgcrypt port guards this, Keccak's and `longlong.h`'s asm with
`ASM_DISABLED`; `ports/patch/libgcrypt-1.12.2.patch` is that port rebased.

## `mlock` on non-mmapped memory is a safety error

`mlock` of a `malloc` block stops the program ("cannot perform this
operation on something that was not mmapped") instead of failing with an
errno. The GnuPG family's configure probe (`GNUPG_CHECK_MLOCK`) mlocks a
`malloc`ed page, so it concluded mlock was broken; libgcrypt then never
locked its secure memory and `GCRYCTL_INIT_SECMEM` failed (`t-secmem`,
`t-sexp`). The secure memory pool itself is mmapped, which `mlock` accepts,
so the libgcrypt port presets `gnupg_cv_have_broken_mlock=no`.

## Found by Fil-C: two of Vala's own tests

With the port's valac, Vala 0.56.19's test suite (1,435 programs built at
`-O0`) passes except the D-Bus tests, which need a session config in the
sandbox (they pass given one), and two that Fil-C stops:

- `methods/varargs-delegate-without-target` calls `string foo (void *)`
  through a `string (*)(void)` delegate, so the callee reads an argument
  that was never passed ("argument size mismatch").
- `objects/property-array`: `_vala_array_dup` adds a NULL terminator only
  for reference-type elements, so copying an `array_null_terminated`
  array of nullable structs (`Manam?[]`) drops the terminator and the next
  `_vala_array_length` reads past the copy. A Vala codegen bug
  (`generate_array_dup_wrapper`), worth reporting upstream; not patched.
## Inline assembly spelled as `.byte` or alignment directives is refused

FilPizlonator validates each inline instruction, so raw opcode bytes and
assembler directives stop the program when the code runs:

```c
__asm__ volatile(".byte 0x0f, 0x01, 0xd0" : "=d"(d), "=a"(a) : "c"(0)); /* xgetbv */
__asm__(".p2align 5");
```

libdeflate's CPU detection used the first form, so every compression,
decompression and checksum call trapped (6 of its 8 tests). Spelling it
`xgetbv` works (`patches/libdeflate-xgetbv.patch`, as for FLAC). p7zip
bundles an older zstd whose loop-alignment `.p2align` directives stopped
7-Zip on any zstd archive; `patches/p7zip-zstd-p2align.patch` skips them
under `__FILC__`, as `ports/patch/zstd-1.5.7.patch` does for zstd itself.

## ALSA's 0.9 API needs symbol versions

`ALSA_PCM_OLD_HW_PARAMS_API` makes `<alsa/pcm_old.h>` bind
`snd_pcm_hw_params_get_rate_min` and friends to `@ALSA_0.9` with `.symver`.
The Fil-C alsa-lib is built `--without-versioned`, so those references do
not resolve and the link fails (TiMidity++). Porting the caller to the
1.0 API fixes it (`patches/timidity-alsa-new-api.patch`). The unversioned
library exports only the 1.0 functions under the plain names, so a
caller that loses its `.symver` would silently call the wrong ABI.

Opening an ALSA PCM device through the default configuration also stops the
program: `snd_config_hooks` loads its hook libraries with `snd_dlopen`, which
calls `dladdr1` for the library's own path, and Fil-C reports `dladdr1 not
yet supported`. TiMidity++ with `-Os` hits it; file output (`-Ow`) works.

## Found by Fil-C: pointers in TiMidity++'s `long` event values

TiMidity++'s `CtlEvent` carries values as `long`, and `CTLE_NOW_LOADING`
and `CTLE_PROGRAM` store string pointers there. Even `-Ow` (write a WAV)
trapped in the dumb interface when it printed the file name.
`patches/timidity-ctl-event-pointers.patch` adds pointer union members for
those two fields and uses them in the playback code and the interfaces
Nixpkgs builds (dumb, ncurses). The other interfaces still read pointers
from the integers.

## Found by Fil-C: small bugs in mhash's and libcdio's tests and code

- mhash's `hmac_test` and `keygen_test` `memset` a buffer right after
  freeing it (`patches/mhash-test-use-after-free.patch`).
- libcdio's `iso9660_ifs_fuzzy_read_superblock` runs `strstr` over a
  2352-byte frame buffer that a raw read fills completely, so it reads past
  the end (`check_fuzzyiso.sh`; `patches/libcdio-fuzzy-superblock-nul.patch`).
- libcdio keeps `iso_rock_statbuf_t`, an in-memory struct with a
  `char *psz_symlink`, inside `#pragma pack(1)` regions, which puts the
  pointer at offset 29. Every ISO 9660 stat trapped on the misaligned
  pointer store. `patches/libcdio-rock-statbuf-unpacked.patch` lays that
  struct out naturally under Fil-C.

## Fil-C C++ uses libc++

Nixpkgs builds Linux C++ against libstdc++, so packages that rely on
libstdc++ behaviour fail only here. libc++ 19 removed the
`std::char_traits` base template, and SFML 2.6 uses
`std::basic_string<Uint8/16/32>` in its public `sf::String` API.
`patches/sfml2-libcxx-char-traits.patch` defines traits for those types in
`String.hpp`, after the FreeBSD port. libc++'s `<string.h>` also brings in
`uint64_t`, which broke p7zip's own `typedef UInt64 uint64_t`
(`patches/p7zip-hash-stdint.patch`).

## Cross-compilation defaults that break Fil-C builds

The Fil-C package set is a cross build with an empty target prefix, so
some Nixpkgs recipes misbehave:

- p7zip's recipe replaces `CC=gcc` with `CC=${targetPrefix}gcc` when
  cross-compiling, leaving `gcc`, which does not exist (`Error 127`). The
  port passes `CC=clang CXX=clang++`.
- Autoconf's `AC_FUNC_MALLOC` cannot run its probe, assumes `malloc(0)`
  returns NULL and renames `malloc` to `rpl_malloc`, which mhash does not
  define. The port sets `ac_cv_func_malloc_0_nonnull=yes`.
- minizip builds from `zlib.src`, and the Fil-C zlib is pinned to 1.3, which
  lacks the `ints.h` that Nixpkgs' patch installs. minizip now builds from
  Nixpkgs' own zlib source.
## Pointers stored at unaligned addresses

A pointer's capability lives in the shadow word of an 8-byte-aligned
slot, so storing a pointer at an address that is not 8-byte aligned is a
safety error ("alignment requirement of 8 bytes not met"), even where x86
would allow it. Two ports hit this at run time:

- parted's `GuidPartitionTableHeader_t` is packed and keeps a `Reserved2`
  pointer after the 92-byte on-disk header, at offset 92, so every GPT
  operation stopped. `patches/parted-gpt-aligned-reserved2.patch` pads the
  in-memory struct and takes the on-disk size from the padding's offset.
- GSL's moving-window Qn accumulator carves a `ringbuf` (which starts with
  a pointer) out of its workspace after `5*n` ints, so it was misaligned
  for odd windows, which is undefined behaviour in C as well.
  `patches/gsl-movstat-aligned-state.patch` reorders the workspace and
  rounds `deque_size`, which has the same problem for even windows.

## Inline assembly with branches is refused

Besides the `"cc"` clobber above, the safe inline assembly accepts only
straight-line instructions. potrace's `bsf`/`bsr` helpers jump over a
fallback `movl` (`jnz 0f`), and configure enables them on any x86
compiler, so potrace and mkbitmap stopped on the first bitmap. The port
selects the portable versions under `__FILC__`.

## The libc include directory precedes packages' `-isystem` directories

The wrapper adds Fil-C's glibc headers with `-isystem`, so they are
searched before any `-isystem` directory a package adds. A native compiler
searches libc after all of them. gnulib replacement headers break when a
package adds its `lib/` with `-isystem`: recode 3.7.15 does this for its
warning setup, got glibc's `fcntl.h` instead of gnulib's, and failed on
`O_BINARY`. The port configures with `--disable-gcc-warnings`, which uses
`-I`. Passing the libc directory with `-idirafter` in `compiler/filc.nix`
would match native behaviour but changes every Fil-C derivation.

## Found by Fil-C: fstrm's option parser reads past its table

`check_or` in fstrm's bundled `libmy/argv.c` scans ahead from an option
for `ARGV_OR` markers, testing entry `+2` before checking whether entry
`+1` is `ARGV_LAST`. For the last option in the table (fstrm_replay's
`-r`), that reads one element past the array.
`patches/fstrm-argv-check-or-bounds.patch` tests the nearer entry first.

## gold does not resolve a library's symbols through its DT_NEEDED chain

Fil-C links with gold. When an executable links a shared library that is
missing one of its own dependencies, GNU ld still resolves the library's
undefined symbols through the DT_NEEDED entries of the other libraries
on the line. gold reports them as undefined instead. ticcutils links
`icu-uc` and `icu-io` but calls ICU regex and transliterator functions
from `icu-i18n`, which only `libicuio` depends on, so every program linking
libticcutils failed; libfolia has the same gap. The LanguageMachines ports
add `icu-i18n` to their `PKG_CHECK_MODULES`.
## `abort()` ignores a SIGABRT handler

POSIX `abort()` raises SIGABRT, so an installed handler runs first (and
the process still terminates if it returns). Fil-C's `abort()` stops the
program with `filc user error: abort(3) called.` without raising, while
`raise(SIGABRT)` does run the handler:

```c
signal(SIGABRT, handler);  /* allowed: sigaction returns 0 */
abort();                   /* handler never runs; SIGTRAP-style panic */
```

glog's `striplog*` tests catch `LOG(FATAL)`'s abort this way to exit
normally, so CTest sees an exception where it expects a failure, and the
port excludes them. The fix belongs in the fork's glibc `abort.c`: raise
SIGABRT (under the usual rules) before stopping. That is a libc change,
so it rebuilds everything built with Fil-C; not done here.

The refused signals (SIGSEGV, SIGBUS, SIGILL, SIGFPE, SIGTRAP) make
`sigaction` fail with `ENOSYS`. glog's `InstallFailureSignalHandler`
CHECKed every `sigaction`, so any program calling it aborted at startup;
`patches/glog-filc-refused-signals.patch` skips the refused ones.

## `__builtin_readcyclecounter` is not lowered

Clang reports `__has_builtin(__builtin_readcyclecounter)`, but calling it
stops the program (`Unhandled intrinsic: llvm.readcyclecounter`), while an
inline `rdtsc` with `"=a"`/`"=d"` outputs works:

```c
int main(void) { return (int)__builtin_readcyclecounter() & 0; }
```

Lowering the intrinsic to the same `rdtsc` should be straightforward in
FilPizlonator. bc-decaf's RNG and benchmark prefer the builtin; its port
uses the asm path.

Inline asm is otherwise narrower than Clang accepts: bc-decaf's PIC
`cpuid` saves `%rbx` by hand (`mov %%rbx, %[r]; cpuid; xchg`), which is
rejected ("cpuid output ebx not covered by output constraint or
clobber") though the plain `"=b"` form works, and its x86_64 field
arithmetic passes memory operands (`"*m"`), which Fil-C never supports.
The port uses the plain `cpuid` and decaf's portable `arch_ref64`
arithmetic (`patches/bc-decaf-filc-x86-asm.patch`).

## Found porting capstone: integer handles and pointer options

capstone's handle type `csh` is a `size_t` holding the `cs_struct`
address, so every call after `cs_open` trapped (all 24 tests).
`patches/capstone-handle-ptrtable.patch` registers handles in a
`zexact_ptrtable` and decodes them wherever the library turns a `csh` back
into a pointer; handle values stay the addresses, so the API and FFI
bindings are unchanged. `cs_option` also takes pointer-valued options
(`CS_OPT_MEM`, `CS_OPT_SKIPDATA_SETUP`, `CS_OPT_MNEMONIC`) as `size_t`,
and the caller's cast drops the capability before the library sees it.
The patch adds a Fil-C-only `cs_option_ptr(csh, cs_opt_type, void *)`;
consumers that set those three options must call it instead.

## Frame-slot coloring is cubic in simultaneously live pointers

FilPizlonator assigns frame "lowers" slots by greedy coloring of an
interference graph, and for each value it tried index after index,
checking every neighbor with a hash lookup each time. With many pointers
live at once this dominates compile time:

```c
void f(void) {
  void *p0 = malloc(1); /* ... */ void *p1999 = malloc(2000);
  sink(p0); /* ... */ sink(p1999);
}
/* clang -O1 -c: 500 pointers 1.0 s, 1000 4.3 s, 2000 41 s;
   -O0 with 2000: minutes and 2.8 GB */
```

Asio's `unit/execution/any_executor.cpp` compiles in 10 s at `-O0`, but
at `-O2` (after inlining) it ran for over an hour at 5.7 GB in the asio
check, and gdb samples were all in `computeFrameIndexMap`'s coloring
loop; the port drops that one test. Doxygen's flex-generated
`scanner.cpp` takes about 30 minutes. The 50-minute parser above may be
the same. The always-live
explicit locals from the GC-roots fix make the graph denser still.
`patches/fil-c/filpizlonator-frame-coloring-linear.patch` (not compiled
yet) collects the neighbors' indices once per value and takes the lowest
free one: the same assignment, in time linear in the edges.
## Module-level asm other than symbol directives crashes the compiler

FilPizlonator parses file-scope `asm` itself and accepts only its symbol
directives (`.symver`, `.filc_weak`, `.filc_alias`, ...). Anything else
hits `llvm_unreachable("Error parsing module asm")` after printing the
whole module, rather than a diagnostic:

```c
__asm__(".previous");   /* UNREACHABLE executed at FilPizlonator.cpp:419 */
```

PulseAudio's `PA_WARN_REFERENCE` emits `.section .gnu.warning.SYM`,
`.asciz` and `.previous` this way. The libpulseaudio port already turned
the macro off, but the full `pulseaudio` (daemon and modules) did not get
it; the port now targets `pulseaudio`, which `libpulseaudio` overrides.

## Inline asm that saves a register it clobbers is rejected

FilPizlonator checks x86 inline asm against its constraints, so asm that
saves and restores a register by hand is refused when it runs. The LZMA
SDK's PIC cpuid (in PhysicsFS) does this with `%rbx`:

```c
__asm__ __volatile__("mov %%rbx, %%rdi; cpuid; xchg %%rbx, %%rdi"
                     : "=a"(a), "=D"(b), "=c"(c), "=d"(d) : "0"(0));
/* cpuid output ebx not covered by output constraint or clobber */
```

`"cpuid" : "=a", "=b", "=c", "=d"` works under Fil-C even with `-fPIC`; the
physfs port selects that variant.

## Inline asm with a pointer output is rejected

Crypto++'s `SecureWipeBuffer` clears memory with `rep stos` and passes the
destination as a `"+D"(p)` in-out operand, which is "inline assembly with
pointer return type". `CRYPTOPP_DISABLE_ASM` removes it, but not the
x86-64 `mulq`/`adcq` word arithmetic in `integer.cpp`, which also uses an
`"g"` operand (unsupported constraint `imr`). The port defines
`CRYPTOPP_DISABLE_ASM` in `config_asm.h` for `__FILC__`, so programs using
the headers agree, and multiplies through `unsigned __int128` instead.

## Hand-written assembly: take the portable C path

The sarcasm assembler accepts only annotated functions, so packages with
perlasm or yasm kernels need their C fallbacks: LibreSSL
`-DENABLE_ASM=OFF`; isa-l configured as an unknown CPU (`CPU=""`), which
builds the `*_base` C functions without multibinary dispatch; btrfs-progs
without `crc32c-pcl-intel-asm_64.S` and without the SSE4.2 CRC32C, which
is `.byte`-encoded inline asm. btrfs-progs also passes
`-Wa,--compress-debug-sections` when assembling, which sarcasm refuses.

## Fil-C's glibc has no `__wmemset_chk`

The user glibc drops `memcpy_chk`, `memmove_chk`, `mempcpy_chk`,
`memset_chk` and `wmemset_chk` from `debug/Makefile`'s routines, as
upstream Fil-C does. The compiler turns fortified `memcpy` and friends into
its own checked copies, but glibc's `wchar2.h` wrapper calls `__wmemset_chk`, so any fortified
`wmemset` fails to link (`undefined reference to 'pizlonated___wmemset_chk'`).
isa-l's igzip hit it (its configure adds `-D_FORTIFY_SOURCE=2`); the port
builds it unfortified. Adding `wmemset_chk` back to the routines, whose C
file is still there, would fix it, and would rebuild everything.

## The GNUstep Objective-C runtime is out of reach

gnustep-libobjc (libobjc2) needs `objc_msgSend` and the block trampolines
in assembly, and generates `eh_trampoline.S` by compiling C++ to assembly.
Beyond that, Clang's GNUstep 2.x ABI emits classes, selectors and
categories into `__objc_*` sections and passes their
`__start_`/`__stop_` bounds to `__objc_load`; under Fil-C those become
undefined `pizlonated___start___objc_selectors` and so on (see the
`__start_`/`__stop_` finding above). The port marks it broken.
## Module-level assembly crashes the compiler

A top-level `asm("...")` with directives FilPizlonator does not parse
(`.section`, `.globl`, labels, `.quad`, ...) is not a diagnostic but a
crash: the pass prints `Invalid directive: .section` and `Error parsing
module asm`, dumps the module and reaches `UNREACHABLE` at
`FilPizlonator.cpp:419`:

```c
asm(".section .qtversion, \"aG\", @progbits, tag, comdat\n.previous");
int main(void) { return 0; }   /* clang -c: UNREACHABLE, exit 134 */
```

An empty `asm("")` compiles. Qt 5's `<QtCore/qversiontagging.h>` emits a
`.qtversion` section like this in every file that includes QtCore outside
QtCore itself, so the first such file (QtDBus) crashed.
`patches/qt5-no-version-tagging.patch` disables the tag under `__FILC__`;
the header is installed, so Qt's users get the same.

## `syscall()` stops the program for `waitid`, `clone`, `open` and `inotify_init1`

Fil-C's `syscall()` passes some numbers through (`futex`, `gettid`) and
refuses others with `filc user error: unsupported syscall: 247` and a
trap, rather than failing with `ENOSYS`. Seen: `waitid` (247), `clone`
(56), `open` (2) and `inotify_init1` (294); the libc wrappers of the same
calls work. Qt's forkfd probes `waitid(P_PIDFD, ...)` and forks with
`clone(CLONE_PIDFD)` through `syscall()`, so every `QProcess` start
stopped; `patches/qt5-forkfd-fork.patch` makes it take its `fork()`
fallback.

## `rdrand`/`rdseed` intrinsics and non-canonical `cpuid` stop the program

`_rdrand64_step` compiles, but reaching it stops the program with
`filc safety error: Unhandled intrinsic: ... @llvm.x86.rdrand.64()`
(`_rdseed64_step` too). CPUID is lowered only in the canonical form with
all four outputs, `asm("cpuid" : "=a", "=b", "=c", "=d" : "a", "c")`;
the PIC-friendly `xchg %rbx, %1; cpuid; xchg %rbx, %1` that Qt uses (and
XGETBV spelled as `.byte 0x0f, 0x01, 0xd0`) is refused at run time
("thwarted a futile attempt to violate memory safety"). Qt probes CPU
features when QtCore starts; `patches/qt5-cpu-probe.patch` uses the
canonical forms and masks out RDRAND/RDSEED so `QRandomGenerator` reads
the kernel's generator.

## Section attributes on data are ignored

`__attribute__((section(".name")))` on a global array has no effect: the
data lands in `.data.rel.ro` and the output has no such section.

```c
__attribute__((section(".qtmetadata"), used))
static const unsigned char md[] = "QTMETADATA !...";
/* readelf -S: no .qtmetadata; the bytes are in .data.rel.ro */
```

Qt 5 finds a plugin's metadata by its `.qtmetadata` section, so every
plugin was "not a plugin" (no platform plugin, so no GUI program started).
`patches/qt5-plugin-metadata.patch` searches the whole file for the
`QTMETADATA` marker when the section is missing, as Qt does on non-ELF
platforms. This is probably the same root as the missing
`__start_`/`__stop_` symbols above.

## Found porting Qt 5: pointers derived from another object's address

Qt 5's `QArrayData` (behind `QByteArray`, `QString` and `QVector`) finds
its elements at `this + offset`. `fromRawData` makes a small header whose
offset reaches the caller's buffer, so the computed pointer carried the
header's 24-byte capability and the first read of the buffer trapped
(`ptr >= upper` in QCborStreamReader, reading plugin metadata).
`patches/qt5-raw-data.patch` stores the raw pointer after such headers,
marked by an offset of 1. `QMutexLocker`, `QReadLocker`/`QWriteLocker`
(lock address plus a "locked" bit in a `quintptr`), `QMapNodeBase`
(parent plus colour bit) and `QModelIndex` (internal pointer as
`quintptr`) lost capabilities the usual way; `patches/qt5-pointer-fields.patch`
makes them pointers and sets the bits with pointer arithmetic.

## `prctl` string arguments must be passed as pointers

`prctl(PR_SET_NAME, (unsigned long)name, 0, 0, 0)`, the usual spelling,
passes the name as an integer; it has no capability, so the runtime's
`zsys_prctl` traps reading it ("cannot read pointer with null object").
Passing `name` itself through the varargs works. Every `QThread` names
itself this way (`patches/qt5-thread-name.patch`).

## `futex(FUTEX_WAKE_OP)` stops the program

`syscall(SYS_futex, ...)` handles `FUTEX_WAIT` and `FUTEX_WAKE` (with or
without `FUTEX_PRIVATE_FLAG`), but `FUTEX_WAKE_OP` stops the program with
`unsupported futex op: 133`. Qt 5's `QSemaphore` uses it on 64-bit Linux
to wake single- and multi-token waiters at once, so the first contended
`release()` (a blocking queued call into Qt's D-Bus thread) died;
`patches/qt5-semaphore-futex.patch` uses Qt's single-word scheme.

## Found porting Qt 5: the QML engine's NaN-boxed values

QtQml's V4 engine keeps every JavaScript value in a `quint64`: doubles
XORed with a mask, integers and booleans tagged in the high bits, and heap
pointers in the low 48 bits, copied in and out with `memcpy`. Values also
travel as `ReturnedValue`, a `typedef quint64`, through every runtime call.
The integer carries no capability, so the first heap object read through a
value trapped. `patches/qt5-declarative-v4-pointers.patch` makes
`ReturnedValue` (and the value's storage) a union whose first member is a
`char *` under `__FILC__`: copies are pointer copies, the tag tests read the
bits, and `m()`/`setM()` use the pointer member. Plain integer stores (tags)
leave the slot's previous capability behind, which is harmless because the
tag tests reject them before any dereference. The same patch makes
`QJSValue::d`, `PropertyKey`, `QFlagPointer`/`QBiPointer`,
`QQmlNotifierEndpoint::senderPtr`, sparse-array node parents and
`QQuickItem`'s JS-wrapper factory (which returned the wrapper as `quint64`
through `qt_metacall`) pointer-typed, and derives the GC's chunk and
persistent-value page addresses with pointer arithmetic rather than
masking integers.

Two more pieces of the engine needed changes. `EngineBase` is
`#pragma pack(1)` (for the JIT, which is off), which put pointers after a
`qint32` at offsets that are 4 mod 8 ("alignment contradiction" in
`ExecutionEngine`'s constructor); it is unpacked under Fil-C. And the
bytecode dumper, one ~540-line function with a case per instruction
(`QV4_SHOW_BYTECODE` only), did not finish compiling in 25 minutes at
4 GB, with or without computed gotos; it is left out. The patch also
makes the interpreter dispatch with a `switch` instead of computed gotos;
it then compiles in minutes (the computed-goto version was not timed).
