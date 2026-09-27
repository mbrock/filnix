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

## `dlopen` of a bare soname ignores the caller's RUNPATH

`dlopen("libnss_dns.so.6662")` fails in a Fil-C program even though the
library sits in the Fil-C sysroot's lib directory and that directory is in
the program's RUNPATH. Nix preloads nss_dns this way and warns, which NixOS's
nix.conf check turns into an error; the Nix port passes libc's full path
instead. Adding the sysroot lib directory to the loader's trusted
directories would fix NSS module loading in general.

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
