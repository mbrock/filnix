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

## Unsupported: `sigaltstack`, `llvm.debugtrap`, `ptrace`, `seccomp`

doctest's self-tests use the first two, strace needs `ptrace`, and
libseccomp's tests call `seccomp` (syscall 317). Nix is built without
seccomp filtering.

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

## Custom allocators and pointer tagging lose capabilities

oneTBB's tbbmalloc carves objects out of raw mmap chunks, and its
`queuing_rw_mutex` sets a flag bit in queue pointers kept in
`std::atomic<uintptr_t>`. PulseAudio's `pa_atomic_ptr_t` also stored pointers
as `uintptr_t`. These are expected Fil-C porting work rather than bugs; the
ports build without tbbmalloc and keep the pointers in pointer-typed atomics,
setting tag bits with pointer arithmetic.

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
