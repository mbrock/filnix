# Upstream Fil-C's test suite

Fil-C's own tests (`filc/tests` in the Fil-C repository, run there by
`filc/run-tests`) are about 7,300 directories, each a small program with a
`manifest` that says what must happen: exit 0, a Fil-C trap (exit 42), a
crash, a compile or link failure, and which strings the output must or
must not contain. `tests/filctests.py` builds them with nanofil and checks
them as `run-tests` does:

```sh
git clone https://github.com/mbrock/fil-c ~/fil-c   # at lib/filc-staging.json's coreRev
FILCC=/tmp/filcc/bin/clang SWIPL=/tmp/swipl/bin/swipl \
  nanofil/tests/filctests.py ~/fil-c -j 24           # about 12 minutes on swa
```

Only tests whose sources are all C run (nanofil compiles nothing else).
filcc preprocesses each `.c`, nanofil compiles it, `as` assembles it, and
filcc links, with `filc/tests/utils.c` and the manifest's libraries.
`run-tests` runs each program four ways (GC rage mode, scribbling and
verifying, stop-the-world, release); this runs only the first,
`FUGC_RAGE_MODE=1`. `--cc filcc` builds the same tests with filcc, which
shows which failures belong to the environment: five do (two static links
that the Nix glibc toolchain refuses, a `-la` library path, a symver
script, a packed union clang refuses at -O2).

## Results

Staging at fil-c `b24cd9552c09` (deluge 7b9ca2bdbb21), November 2026:

| | tests |
|---|---:|
| in `filc/tests` | 7,325 |
| skipped: C++, assembly or LLVM IR sources | 1,302 |
| skipped: another platform (`only-on-platform`) | 506 |
| skipped: `skip` in the manifest | 4 |
| run | 5,491 |
| pass | 4,006 |
| refused by nanofil | 1,387 |
| trap with a different message | 38 |
| link error | 40 |
| spurious trap | 11 |
| wrong output or exit status | 8 |
| diagnostic differs | 1 |

**No test that must trap ran to completion.** Every test whose manifest
expects a Fil-C trap or a crash trapped or crashed under nanofil, or was
refused at compile time.

### Safety triage

Filip Pizlo's triage for this suite: what matters is a program that
crashes (a signal, not a Fil-C panic) or that exits normally where the
suite demands a panic. A different panic where one is due does not.
`filctests.py` reports these as `crash` and `missed trap`. With
`--modes all`, all four of run-tests' ways to run (GC rage mode,
scribbling and verifying, stop-the-world, release), there are:

- no missed traps;
- two crashes of nanofil's: `dividebyzero` and `unsigneddividebyzero`
  die with SIGFPE (below);
- one crash that is not nanofil's: `jit_hello_loop3` dies with SIGTRAP,
  rarely and only when scribbling, and so does filcc's build of it (1
  in 30 runs);
- two runs over the three-minute limit when scribbling
  (`hashtablegctest`, `fannkuchredux`), not yet compared with filcc's
  times.

### Refused (1,387)

nanofil refuses C it does not lower, with a diagnostic
([reject.sh](../tests/reject.sh)). Nearly all are SIMD:

- 656 inline asm of instructions nanofil cannot check (upstream checks
  SSE, AVX, AVX-512 and x87 asm instruction by instruction; nanofil
  accepts only the fixed-register forms of [asm-fixed.md](asm-fixed.md)).
- 426 x86 intrinsics (`__builtin_ia32_*`, mostly AVX-512 masked loads,
  stores and narrowing moves).
- 224 vectors of 32 or 64 bytes, or a vector passed to an external or
  variadic function ([vector-access.md](vector-access.md) takes up to
  16 bytes).
- 35 `__int128`.
- The rest, one to nine tests each: top-level asm other than
  `.symver`, `__atomic_store` and `_Atomic` structs, `ifunc`,
  `__builtin_frame_address` and `__builtin_return_address`, weak
  thread-locals and aliases of thread-locals, `_Complex` literals
  (`1.0fi`), `__builtin_set_flt_rounds`, `__rdtsc`, `va_arg` of `char`.

### Link errors (40)

- 38 call Fil-C intrinsics that filcc expands inline and no library
  defines: `zcallee` and `zcallee_closure_data` (the called function
  object, which arrives in `%rsi`), `zis_readonly` (the lower's aux
  flags), `zargs`, `zreturn` and `zstack_pointer`. Each needs an IR
  operation, so they wait for the IR owner.
- 2 are environment (static links).

### Traps with a different message (38)

The program traps where it must, but the message differs from filcc's,
so `output-includes` fails. Most (vibemove, zmemmove_union, cloningfail2)
are copies that nanofil hands to the runtime's `zmemmove`, which reports
"cannot read source pointer ..." where filcc's inline check reports
"cannot read pointer ...". Others report a narrower check first (`uaf`:
"cannot write pointer to free object" for filcc's "cannot access"), and
`stackdumpbug` wants a file and line in the stack trace, which nanofil
does not emit.

### Spurious traps (11)

- `ptrtointtoptr`, `intcast2`, `intcast2O0`: a pointer rebuilt from an
  integer has no capability unless the cast sees the source pointer
  ([ub.md](ub.md), *A pointer rebuilt from integers*). filcc's optimizer
  folds these round trips first.
- `unionstoragecopy`: a capability that travels through memory a struct
  or union declares as integers. nanofil copies an object word by word
  as its type declares it (c_lower's `copy_object`), so a pointer stored
  in a `long` member loses its capability; filcc copies the words with
  their capabilities. `byval-copy-test` (wrong exit) checks the same for
  by-value struct arguments.
- `ptrchaos2`, `ptrcaschaos2`: ten threads push onto a list through a
  racing `foo *volatile head`, and the reader traps with "ptr >= upper".
  A guess, not yet checked: a racing load pairs one store's address with
  another's capability, which filcc's pointer stores never let a reader
  see. filcc runs both to the end.
- `musttail`: `__attribute__((musttail))` is an ordinary call in nanofil,
  so ten million mutually recursive tail calls overflow the stack, a
  Fil-C stack-overflow trap.
- `bug282b` (forced unwinding through a closure) and `hiddenvisibility`
  (`dlopen` of a `-fvisibility=hidden` library fails) are not yet
  diagnosed.

### Wrong output or exit status (8)

- `dividebyzero`, `unsigneddividebyzero`: since deluge (upstream
  2de132744209, *Kill UB harder*), filcc defines `x / 0` and `x % 0` as
  0, `MIN / -1` as `MIN` and `MIN % -1` as 0. nanofil's `idiv` still
  raises SIGFPE, as [ub.md](ub.md) records for 0.687. The same commit
  masks shift amounts and makes `ctlz`/`cttz` of 0 the width.
- `_longjmpfail1`, `longjmpfail4`, `siglongjmpfail1`: a non-volatile
  local changed between `setjmp` and `longjmp`, whose value C leaves
  indeterminate (7.13.2.1p3); filcc keeps the value at `setjmp`, nanofil
  the latest ([setjmp.md](setjmp.md)).
- `forcedunwindccleanup`: `cleanup` handlers do not run during a forced
  unwind (`pthread_exit`).
- `stackscan`: wants file, line and column in `zstack_scan`'s frames.
- `byval-copy-test`: above.

### Diagnostic differs (1)

`initmisalignedptrfail` refuses the misaligned pointer initializer as
filcc does, but the message does not name the object.

## Fixed by this suite

The first run passed 3,747; these fixes, in c_parse, c_types and
c_lower, add 260:

- `zmemmove_union`, `zmemmove_builtin` and `zmemmove_builtin_volatile`
  from `filc_test_support.h`, which filcc lowers as its builtin memmove,
  are the runtime's `zmemmove`, and `zhas_union` is a no-op (246 tests).
- Equal string literals of a unit are one object, as clang merges them:
  `p == "hello"` and weak-map keys (9 `weakmap*` tests, `struct`).
- An asm label on a declaration names the later definition too
  (`void foo(void) asm("bar"); void foo(void) { ... }` defines `bar`).
- Constructors and destructors run in declaration order, not symbol
  order (`exittest`).
- `__attribute__((musttail)) return f(x);` and other GNU attributes that
  begin a statement parse as statement attributes, not as a declaration.
  `musttailroot` and `sharedlowersargs` now pass: under GC rage mode a
  nanofil callee keeps its arguments alive after a filcc caller has
  popped its frame, as the callee-rooting ABI of deluge requires
  ([abi-findings.md](abi-findings.md), *Callees root their arguments*).

## Next

In order of tests gained per change:

1. Report memmove traps with filcc's messages, by checking both ranges
   inline before calling `zmemmove`, as filcc does (about 30 tests).
2. The intrinsics of *Link errors* (38 tests, IR operations).
3. Deluge's defined division, shifts and bit counts, in the interpreter,
   `const_eval` and the backend, with ub.md updated.
4. Copying capabilities with the words of integer-typed members, if the
   campaign wants filcc's union and struct transport (ub.md).
5. `__int128` (35 tests) and real `musttail`.

The SIMD inline asm and intrinsics (about 1,300 tests) are out of scope
for now.
