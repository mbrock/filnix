# Nonlocal returns in the Fil-C backend

## IR contract

```prolog
ins(t(D), w, setjmp(Kind), [Buf, SaveMask])
```

`Kind` is `setjmp`, `'_setjmp'`, or `sigsetjmp`. The operation has its
own `op_kind`, `setjmp`, takes `[p,w]`, returns `w`, and is valid only in
Fil-C mode. `SaveMask` must be `c(0)` for the first two kinds. QBE text
spells these `%r =w setjmp %buf, 0`, `%r =w _setjmp %buf, 0`, and
`%r =w sigsetjmp %buf, %mask`; parsing/printing preserves the term.

The C frontend recognizes resolved direct function symbols after ordinary
argument checking/conversion, including symbol renames. Taking a setjmp
function's address is rejected. The interpreter and plain backend refuse
nonlocal returns with explicit diagnostics rather than approximate them.
The longjmp family uses ordinary Fil-C calls.

## Frame and snapshot design

Nanofil keeps pointer addresses in native temporary slots and their
lowers in the scanned Fil-C frame. The runtime's jmpbuf restores lowers,
but native `_longjmp` does not roll back native stack memory. In a loop,
the same temporary slot can therefore contain a later address when its
lower is restored to an earlier capability. Merely disabling mem2reg does
not prevent this tearing.

Every setjmp-capable function reserves three additional scanned lowers:
an immutable payload snapshot, a transient jmpbuf root, and a weak map
**last**. Both call and non-call function origins set `has_setjmps=1`;
their lower counts agree and `num_stack_auxes=0`. After pushing the frame
and rooting incoming arguments, the prologue creates and roots the weak
map, even if execution has not reached its first setjmp.

Each dynamic setjmp:

1. Stores a call-capable origin, allocates a fresh snapshot, and roots
   its payload lower immediately.
2. Copies the full eight-byte contents of every `t` and phi `shadow`
   payload slot into the snapshot. Thread, aux, return-buffer and frame
   bookkeeping, all lowers and the transient jmpbuf slot are excluded.
   These are raw bytes, not stored flight pointers; they need no aux or
   pointer barrier.
3. Calls `filc_jmp_buf_create(thread, kind, mask)`, which captures all
   lowers, including the snapshot root. The runtime barriers the saved
   lowers and keeps their objects marked while the jmpbuf is reachable.
4. Roots the returned special payload before any helper, stores its
   flight pointer into the user's buffer with ordinary checked pointer
   storage, and registers it as a weak-map key with invalid pointer 1 as
   the value. The transient root remains live through native `_setjmp`,
   then is cleared on either return so later snapshots do not retain a
   chain of otherwise dead jmpbufs through this scratch root.
5. Calls real native `_setjmp` **in the current body**, never in a wrapper
   or through a Fil-C thunk. EAX is a native int, not the Fil-C AL exception
   flag/RDX result convention.
6. On initial zero return, writes the result. On a nonzero return, loads
   the runtime-restored snapshot root, restores every saved payload slot
   without calls, polls or checked user accesses, and only then writes
   the full EAX result. Restoration uses RDX/RCX and preserves EAX.

Each buffer keeps its own snapshot alive through its saved lowers. Multiple
setjmps in the same frame share the map, not a mutable snapshot. Repeated
jumps, two active destinations and loop-reexecuted instructions therefore
restore coherent addresses, lowers, scalars and phi slots.

## Optimizations and C locals

Public promotion and copy-elimination entry points leave any containing
function unchanged, even if its setjmp is unreachable. Escape analysis
treats intrinsic operands as escaping; alias analysis makes no pointer
fact for its word result. Neither analysis moves instructions. Future
register allocation or motion must preserve this returns-twice barrier:
no live value may exist only in a register across it.

**Compiler temporaries and phi slots get their setjmp-time values. C
locals do not necessarily roll back.** All C locals in these functions,
including volatile and address-taken locals, remain in heap-backed memory
because promotion is disabled; their contents keep intervening changes.
C permits changed nonvolatile automatic locals to become indeterminate,
so the differential C test does not inspect them. Unchanged nonvolatile
locals remain usable. The native IR regression, not a C test invoking
indeterminate values, asserts temp/phi rollback.

## Review and coverage

Before implementation, Oracle reviewed the pinned pass/runtime and
nanofil's backend/optimizers. Verdict: **sound in principle**, conditional
on eager map initialization, final-lower placement, matching origin
metadata, strong jmpbuf rooting through helpers, fresh immutable
temp/shadow-only snapshots, safepoint-free restoration, full integer return
preservation, and guards at the public optimizer entry points. These are
implementation invariants, not assumptions to relax after tests pass.

- `tests/c/prog/setjmp.c`: nested calls, zero-to-one conversion, two live
  destinations, repeated jumps, exact nonzero returns, unchanged
  nonvolatile locals, changed volatile/address-taken locals and pointee
  memory, forced GC, and sigsetjmp mask preservation/non-preservation.
  Signal-set manipulation is a clang-built companion; the setjmp callers
  and nonlocal-control flow are compiled by nanofil and filcc separately.
- `tests/c/prog/setjmp-expired.c`: jumping to a returned frame must trap.
- `tests/filc/setjmp.ssa`: loop-overwritten pointer/scalar/phi rollback,
  with collection while only saved lowers retain the earlier objects;
  invalid, readonly and misaligned destination buffers; and a longjmp
  through a setjmp-capable frame before its first setjmp executes.
- `tests/unit.pl`: exact parser/printer round-trip, kind/mask/class
  validation, Fil-C mode discovery, optimizer preservation and explicit
  interpreter rejection. The native tests run on both Prolog hosts,
  with and without `-O`, including scribble/verify GC stress.

Asynchronous signal-handler jumps are not a newly promised interface.
No runtime, GC, compiler toolchain or pin is changed.
