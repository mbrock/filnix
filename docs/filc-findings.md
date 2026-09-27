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
and `DOCTEST_CONFIG_NO_POSIX_SIGNALS`.

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

## A pointer at a misaligned offset in a constant crashed the compiler

```c
struct ext { unsigned len; void *ptr; } __attribute__((packed));
static char buf[4];
const struct ext e = { sizeof buf, buf };
```

failed `Assertion '!(Offset % WordSize)'` in `computeConstantRelocations`
(BlueZ's MIDI test, through ALSA's `snd_seq_ev_ext`). The fork falls back to
the run-time initializer, which stores the pointer like any misaligned store
(`checks.packed-pointer`). Loading `e.ptr` later still traps, as misaligned
pointer loads do.

## Linker-generated `__start_`/`__stop_` section symbols are not visible

Code that collects descriptors in a named section and walks it with
`__start_SECTION`/`__stop_SECTION` fails to link: the references become
`pizlonated___start_SECTION`, which the linker does not define. ELL, BlueZ
(`patches/bluez-no-debug-section.patch`) and weston's test runner use this
pattern; the ports disable pattern-selected debug output or register the
entries from constructors.

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

## `accept` and `recvfrom` reject a length pointer with a null address

`accept(fd, NULL, &len)` stops the program ("cannot write pointer with null
object") in `handle_returned_addr`, which checks the address buffer for
`*len` bytes whenever the length pointer is non-null. Linux ignores the
length when the address is null, and NSPR's `PR_Accept(fd, NULL, ...)`
relies on that; `recvfrom` shares the helper. The NSPR port passes no length
when it wants no address (`patches/nspr-null-peer-address.patch`).

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
the bit with pointer arithmetic. oneTBB's tbbmalloc is a different problem: it
carves objects out of raw `mmap` chunks, which have no per-object capabilities,
so the port builds without it.

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

## Open: an exception object freed during unwinding in Nix's tests

`nix-util-tests --gtest_filter=decompress.decompressInvalidInputThrowsCompressionError`
stops in `landing_pad` with "cannot read pointer to free object": the
personality routine reads the in-flight exception after it has been freed.
The test decompresses invalid bzip2 data through libarchive, whose read
callback throws and catches an `EndOfFile` internally before Nix throws the
`CompressionError`. A standalone program following the same libarchive
calls does not reproduce it. The other 688 tests pass; the test is excluded.

## Found by Fil-C: pointer rebasing across buffers in FFmpeg's flashsv2

`libavcodec/flashsv2enc.c` copies its frame blocks to key blocks and rebases
their pointers with `key_blocks[i].enc += (s->keybuffer - s->encbuffer)`. The
address lands in `keybuffer`, but the pointer is still derived from
`encbuffer`, which is undefined behaviour in C; Fil-C refused the read
(`fate-vsynth1-flashsv2`). The port writes
`keybuffer + (enc - encbuffer)`. FFmpeg 8.1 also stores its `av_log`
callback in an `atomic_uintptr_t`, dropping the function pointer's
capability.

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
