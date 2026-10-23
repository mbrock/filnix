# Fil-C ABI findings at the filnix pin

The [handoff](handoff.md) was read at Fil-C `cec28ab` (2026-10-22). filnix
builds Fil-C 0.686, core revision `163fae5`
([lib/filc-upstream.json](../../lib/filc-upstream.json)). nanofil must link
against the toolchain filnix actually ships, so everything below was checked
at `163fae5` by reading its source and compiling the probes in
[probes/](../probes/) with `nix build .#filcc`. Rerun them with
`nanofil/probes/run.sh`.

To read the sources at the pin, build the small reference checkout (about
6.5 MB: the design docs, `FilPizlonator.cpp` and its helper passes, the
clang pipeline and driver files, and the runtime):

```sh
nix build -o /tmp/filc-ref .#lib.x86_64-linux.filc-ref-src
# /tmp/filc-ref/libpas/src/libpas/filc_runtime.{h,c}
# /tmp/filc-ref/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp
# /tmp/filc-ref/{Manifesto,gimso_semantics,invisicaps_by_example}.md
```

The full checkouts in [lib/sources.nix](../../lib/sources.nix) are for
building; `filc0-src` alone is about 1.6 GB.

## Pin differences that matter

Between `163fae5` and `cec28ab`, the parts the handoff relies on are
unchanged: thread layout, calling conventions, object header, and the
check, load and store sequences. These differ:

- **Function origin layout.** At the pin, `filc_function_origin` ends with
  `bool can_throw, can_catch, has_setjmps; unsigned num_stack_auxes`. At
  `cec28ab`, `has_setjmps` became `unsigned num_setjmps`, and setjmp lowers
  became the highest frame slots instead of a weak-map lower. The origin is
  data that nanofil emits, so its layout is pin-specific. Emit it from one
  table keyed to the pin, and recheck it when the pin moves.
- `cec28ab` also adds allocation that cannot exit for small allocas, a
  different `setjmp` runtime entry (`filc_jmp_buf_recreate`), and
  "may free" now defined as "may write memory". None of these matter while
  nanofil rejects `setjmp` and allocates outline.

## Open questions from the handoff, answered

**Struct arguments and returns.** Clang classifies structs by SysV rules
before the pass runs. The pass only sees the result (from `abi.ll`):

| C | Fast signature seen by the pass |
| --- | --- |
| `long take_small(struct {long a, b;})` | `(i64, i64)`, symbol `FI1598`, the same as `long f(long, long)` |
| `long take_withptr(struct {char *p; long n;})` | `(ptr, i64)`; the pointer field travels as a flight pointer |
| `struct {long a, b;} ret_small(long)` | returns `{i1, i64, i64}` (`FI146`) |
| `struct {char *p; long n;} ret_withptr(char *)` | returns `{i1, flight_ptr, i64}` |
| `struct {long a, b, c;} ret_big(long)` | `sret` becomes a leading flight-pointer argument, and the return is `{i1}` (`FI2528`) |
| `long take_big(struct {long a, b, c;})` | `byval`, so generic only (`FI0`); the function object's `fast_entry` is 0 |

So nanofil's frontend must do the SysV struct classification itself. That
means splitting a struct of 16 bytes or less into scalars, with pointer
fields as pointer class. Larger returns become an sret pointer, and larger
arguments force the generic convention.

**Pointer pairs across R9 and the stack.** They do split. In
`ext5(long, char *, char *)` (`abi2.s`, `call5` and `def5`), the
registers are RDI = thread, RSI = callee lower, RDX = the long, and
RCX:R8 = first pointer. R9 holds the second pointer's address, and its
lower goes in the first stack slot. Pairs are not kept together. Each
half takes the next GPR, then the next 8-byte stack slot. This is plain
SysV assignment of a flattened `(ptr, ptr)` list.

**`has_exception`.** It comes back in AL. Every caller and thunk tests
only `testb $1, %al`. Callees zero EAX, but paths through a `select`
define only AL. Rule: write 0 or 1 to AL, and read only bit 0.
Integer results come back in RDX (and RCX for a second element), and a
pointer comes back as RDX:RCX. Getters return in RAX:RDX.

**Does free collapse bounds?** Yes. `free_impl` in `filc_runtime.c` sets
`object->upper = lower`, then sets `FILC_OBJECT_FLAG_FREE` in `aux` with a
CAS, panicking if it is already set. Global, special and mmap objects
cannot be freed. Note that the write check still tests FREE together with
READONLY (`testb $6, -2(lower)`). So skipping only the not-freed check
when bounds are checked is sound, but write checks remain.

**Can string literals skip the getter?** Clang does not skip it. Each
literal gets `pizlonatedDO_.str` with header
`{upper = DO + 16 + size rounded up to 8, aux = 0x0003 << 48}` (GLOBAL | READONLY, no aux
array), a 16-byte cache and a getter that calls
`filc_global_initialization_start`. That call only pushes the object onto
`filc_global_variable_roots`, so the collector scans it for pointers.
`fugc_mark_fast` in `fugc.h` returns "already marked" for any GLOBAL
object and never touches it. Function objects already rely on this: their
getters just return `FO+16` and they are never registered. A pointer-free
GLOBAL | READONLY object therefore needs no registration, and can be
referenced directly with a RIP-relative `lea`. This is the reading, not yet
a GC stress test. The same argument covers any readonly global whose
pointers all target other GLOBAL objects. Only globals that can come to
hold heap pointers need registration.

**Callers root arguments.** The pass states it outright (comment above
`mustTailArgsRootedByCaller`): "Fil-C callers root the objects they pass
as arguments; callees do not root their incoming arguments (except byval
ones)." The callee still stores lowers of values it derives, for example
`p + i` inside `sum_loop`'s loop.

## Sequences observed at the pin

These are clang's output at `-O2`, and they are what nanofil's inline paths
should reproduce.

- **Entry:** `cmpq %rsp, (%rdi); jae filc_stack_overflow_failure`.
- **Frame push:** `frame = {parent = thread->top_frame, origin, lowers[N]}`
  on the stack, then `thread->top_frame = &frame` (offset 16). Lowers that
  have not been written yet are zeroed. Restore the parent before every
  return.
- **Pollcheck:** `testb $14, 8(%rdi); jne slow`, where the slow path calls
  `filc_pollcheck_slow(thread, origin)`.
- **Read check (S bytes):** `lower != 0`, `ptr >= lower`,
  `ptr + S <= upper` (`upper = -16(lower)`). A failure calls
  `filc_optimized_access_check_fail(ptr, lower, &check_origin)`.
- **Write check:** also `testb $6, -2(lower)` (READONLY | FREE).
- **Pointer load:** check 8-byte alignment, then
  `auxp = -8(lower) & 0xFFFFFFFFFFFF`. If `auxp` is 0, the lower is 0.
  Otherwise `w = auxp[ptr - lower]`, and if `w & 1`, the word is an atomic
  box and the lower is the 8 bytes at `(w & ~1) + 8`. Then load the address from `ptr`.
- **Pointer store:** check alignment and write permission. If `auxp` is 0,
  `auxp = filc_object_ensure_aux_ptr_outline(thread, lower - 16)`. If the
  stored lower is not 0 and `filc_current_marking_state` (GOT, 32-bit) is
  not 0, call `filc_store_barrier_for_lower_slow(thread, stored_lower)`.
  Then store the lower to `auxp[ptr - lower]` and the address to `ptr`.

**Static data layouts at the pin**

| Struct | Size | Fields |
| --- | --- | --- |
| `filc_origin_node` + `filc_function_origin` | 40 | `function`, `filename`, `u32 num_lowers_ish`, pad, `personality_getter`, `u8 can_throw, can_catch, has_setjmps`, pad, `u32 num_stack_auxes` |
| `filc_origin` | 16 | `origin_node`, `u32 line`, `u32 column` |
| `filc_optimized_access_check_origin` | 24 + 8n | `u32 size`, `u8 alignment, alignment_offset, needs_write`, pad, `scheduled_origin`, `semantic_origins[]` (NULL-terminated) |
| Function object | 40 | `{FO+16, (FO+16) + 0x0083 << 48}`, then `fast_entry`, `generic_entry`, `u64 signature` |

The function object's aux flags `0x0083` are GLOBAL | READONLY |
special type FUNCTION (`1 << 7`).

**Generic entry.** `{i1, i64 ret_size} generic(thread, callee_lower,
args_size)`. Arguments arrive in `thread+128` (data) and `thread+384`
(aux), and results go back the same way. An entry must check
`args_size` and call `filc_cc_args_check_failure(actual, expected,
origin)` when it is too small.

## Globals, getters and indirect calls (for M4c)

Read in `filc_runtime.{h,c}` and `FilPizlonator.cpp` at the pin, and
checked against `filcc -S` output.

**Aux flag bits** (`aux >> 48`): GLOBAL 0x1, READONLY 0x2, FREE 0x4,
MMAP 0x8, GLOBAL\_AUX 0x10 (the aux array is static, so it is not
marked), WEAK\_KEY 0x20; special type in bits 7–10 (function = 1), log2
alignment in bits 11–15. Clang's globals use 0x0001 (no pointers), 0x0011
(pointer-holding, aux = `DA_g`), 0x0003 (string literals), and 0x0013 for
a readonly global that holds pointers.

**A global `g`** is `DO_g: {upper = DO_g + 16 + size rounded up to 8,
aux}` followed by the payload, plus a 16-byte cache `GP_g` holding a
`filc_ptr {ptr, lower}` (zero until initialized). A pointer-holding global
also has `DA_g`, a zeroed aux array as large as the payload.

- The **getter** `pizlonated_g(thread, origin)` returns ptr in RAX and
  lower in RDX. Its fast path loads both cache words and takes the slow
  path if either is 0. The slow path calls
  `filc_global_initialization_start(thread, origin, &GP_g, DO_g)`.
- `start` writes `origin` into `thread->top_frame->origin` when it is
  not NULL, so **the caller must have its frame pushed**. It checks the
  stack limit, takes the initialization lock, and registers `DO_g` in
  `filc_global_variable_roots`. It returns true only to the initializer.
- The initializer runs
  `filc_execute_constant_relocations(thread, DO_g, relocs, n)`. Each
  24-byte relocation is `{u64 offset, u32 kind, pad, target}`: kind 0 is
  a getter, kind 1 is a constexpr node `{u32 op = 0 (add immediate), u32
  left_kind, left_target, u64 offset}`. Each one writes the address into
  the payload and the lower into the aux array at the same offset. It
  asserts both slots are still 0, so pointer slots in the static
  initializer must be emitted as 0. Then the initializer calls
  `filc_global_initialization_end(thread)`, which publishes the cache.
- Nested getters run from relocations get `origin = NULL`. A getter can
  run arbitrary initialization code, so a call to a getter is a safepoint
  like any other call: everything live must be in the frame first.

**Calling through a function pointer** (`checkFunctionAndGetLower`, and
the thunk clang emits for each external callee): lower ≠ 0, ptr equal to
the aux pointer of lower (a function object's aux points to its own
payload), and special type function, i.e. `aux & 0x0780 << 48 == 0x0080 <<
48`. Otherwise call `filc_check_function_call_fail(ptr, lower)`. Then, if
the signature word at lower + 16 is the call site's, call `*(lower + 0)`
(the fast entry), with RSI = lower. If not, marshal the arguments into
`thread + 128` (data) and `thread + 384` (lowers), call `*(lower + 8)`
(the generic entry) with RDX = argument bytes, and if no exception,
require the returned size to be at least the return's size, calling
`filc_cc_rets_check_failure(got, want, origin)` otherwise. The inline
buffers hold 256 bytes each. Larger argument lists use outline buffers,
which nanofil does not need while calls stay at 16 words or fewer.

## Verified end to end

[probes/link/add2.s](../probes/link/add2.s) is hand-written GNU `as`
assembly. It contains an implementation, an alias, a getter, a function
object and a generic entry for `long add2(long, long)`. Linked with a
clang-built Fil-C `main`:

```text
direct 42 indirect 1337
filc safety error: argument size mismatch (actual = 8, expected = 16).
```

The direct call resolves to our strong `pizlonatedFI1598_add2` over
clang's weak thunk. The indirect call goes through our getter and function
object checks. A call through a wrong prototype (`FI135`) takes the
generic path into our entry, which rejects it. Code emitted outside clang
can participate fully in the Fil-C ABI, using GNU `as` and nothing else.
