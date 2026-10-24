# Nonlocal returns in the Fil-C backend

## IR contract

```prolog
let(tmp(D), w, setjmp(Kind), [Buf, SaveMask])
```

`Kind` is `setjmp`, `'_setjmp'`, or `sigsetjmp`. The operation has its
own `op_kind`, `setjmp`, takes `[p,w]`, returns `w`, and is valid only in
Fil-C mode. `SaveMask` must be `const(0)` for the first two kinds. IR text
writes the term as it is, for example
`let(tmp(r), w, setjmp(sigsetjmp), [tmp(buf), tmp(mask)])`.

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

## Staging 0.687 design

The target is staging `af813053ecb5`, not Fil-C 0.686. Each static setjmp site
has one ordinary scanned snapshot root and one jmpbuf root. All jmpbuf
roots are **last**, at the highest lower indices. Both call and non-call
origins use the 48-byte layout: two flag bytes at 32, two padding bytes,
`u32 num_setjmps` at 36, `u32 num_stack_auxes=0` at 40, four trailing
padding bytes. Their lower and static-site counts agree.

After pushing the frame and rooting incoming arguments, the prologue
allocates every site's payload snapshot once and roots each before the
next allocation. All snapshot roots are therefore initialized before any
setjmp captures lowers. They remain constant throughout the invocation,
including across jumps to other sites. Lazy allocation into ordinary
lowers would be wrong: a jump to an earlier site could restore a null or
obsolete snapshot root while retaining a later site's jmpbuf. Eager
initialization avoids an additional non-restored root protocol.

Each dynamic setjmp:

1. Stores a call-capable origin and loads this site's existing snapshot.
2. Copies the full eight-byte contents of every `t` and phi `shadow`
   payload slot into the snapshot. Thread, aux, return-buffer and frame
   bookkeeping, all lowers and every hidden jmpbuf slot are excluded.
   These are raw bytes, not stored flight pointers; they need no aux or
   pointer barrier.
3. Calls `filc_jmp_buf_recreate(thread, &lowers[site], kind, mask)`.
   The helper creates and roots the jmpbuf on first use, then overwrites
   it on subsequent executions of that static site. It captures and
   barriers the current lowers, keeping their objects marked.
4. Stores the returned special payload's flight pointer into the user's
   buffer with ordinary checked pointer storage. The persistent site
   lower roots it through every helper and native `_setjmp`; it is never
   cleared. There is no weak map or transient jmpbuf lower.
5. Calls real native `_setjmp` **in the current body**, never in a wrapper
   or through a Fil-C thunk. EAX is a native int, not the Fil-C AL exception
   flag/RDX result convention.
6. On initial zero return, writes the result. On a nonzero return, loads
   the runtime-restored snapshot root, restores every saved payload slot
   without calls, polls or checked user accesses, and only then writes
   the full EAX result. Restoration uses RDX/RCX and preserves EAX.

The runtime locates active destinations by scanning the final
`num_setjmps` lowers and skips those slots when restoring. A buffer from
an earlier iteration aliases the same site's jmpbuf and resumes the
**latest** execution, as upstream #335 requires. Its snapshot is likewise
overwritten on every execution of that site. Different sites have
independent snapshots; jumping to one does not roll back another site's
snapshot contents or jmpbuf. Restored payloads and ordinary lowers thus
come from the same site execution, including repeated jumps after
collections and jumps between independently active destinations.

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

Before implementation, Oracle reviewed the staging pass/runtime and
this design: **approved, no memory-safety blocker**. Required invariants:
eager stable snapshot roots, final
per-site jmpbuf lowers, matching origin metadata, persistent jmpbuf rooting
through helpers, per-site reusable temp/shadow-only snapshots,
safepoint-free restoration, full integer return preservation, and guards
at the public optimizer entry points. These are implementation invariants,
not assumptions to relax after tests pass.

- `tests/c/prog/setjmp.c`: nested calls, zero-to-one conversion, two live
  destinations, repeated jumps, exact nonzero returns, unchanged
  nonvolatile locals, changed volatile/address-taken locals and pointee
  memory, forced GC, and sigsetjmp mask preservation/non-preservation.
  Signal-set manipulation is a clang-built companion; the setjmp callers
  and nonlocal-control flow are compiled by nanofil and filcc separately.
- `tests/c/prog/setjmp-expired.c`: jumping to a returned frame must trap.
- `tests/filc/setjmp.ir`: latest-site pointer/scalar/phi restoration,
  with collection while saved lowers retain the snapshot's objects;
  invalid, readonly and misaligned destination buffers; and a longjmp
  through a setjmp-capable frame before its first setjmp executes.
- `tests/unit.pl`: exact parser/printer round-trip, kind/mask/class
  validation, Fil-C mode discovery, optimizer preservation and explicit
  interpreter rejection. The native tests run on both Prolog hosts,
  with and without `-O`, including scribble/verify GC stress.

Asynchronous signal-handler jumps are not a newly promised interface.

## Staging signal-mask recreation fix

Staging [af813053ecb5](https://github.com/mbrock/fil-c/commit/af813053ecb5a5ff27292bfede8d3a9e870d4c8e)
fixes the runtime defect present in `35faf87`: `filc_jmp_buf_recreate`
now assigns `did_save_sigmask` on every execution from the current kind
and policy, just as a fresh buffer would. A same-site `sigsetjmp` 1→0
transition no longer restores an earlier mask; 0→1 captures the current
mask. Plain `setjmp` follows the current `zmake_setjmp_save_sigmask`
policy in both directions; `_setjmp` never saves a mask. Oracle approved
the runtime change with no memory-safety blockers. Buffer identity,
rooting and lower restoration are unchanged.

Fil-C's `setjmp_sigmask_recreate` regression covers both directions for
`sigsetjmp` and plain `setjmp`, and fails against the old runtime.
Nanofil's `tests/c/prog/setjmp.c` also exercises both `sigsetjmp`
transitions at one static site, with collection before the jump, through
both nanofil and filcc. Nanofil needs no workaround or site-identity change.
