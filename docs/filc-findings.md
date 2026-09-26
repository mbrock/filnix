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
