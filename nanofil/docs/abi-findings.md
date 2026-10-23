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

## Structs as values (for M4d)

Probed with `filcc -O1 -S` at the pin; the generic-entry layout matches
`pizlonated1ET<sig>`/`2ET<sig>`, clang's shared generic helpers.

- **Each eightbyte of a struct or union of 16 bytes or less is one word**
  of the signature: a ptr word (digit 7) if a pointer starts there, an
  i64 word (digit 0) otherwise, even when the eightbyte is short. So
  `struct {int; char}` is one i64, `struct {int; int; char *}` is (i64,
  ptr), and `union {char *; long}` is ptr. Arguments are those words in
  order: `take_mix(struct mix)` is `FIP11839` with the packed ints in RDX
  and the pointer in RCX:R8. A one-word struct return is the same as a
  scalar return: `struct {char *}` and `char *` are both `FI1073`.
- **Returns of two words with no pointer** come back like a scalar pair:
  `struct {long, long} f(long)` is `FIP146` (ret digits [0, 0]), with
  AL = has_exception and the words in RDX:RCX.
- **Returns with a pointer field** need more than two return registers,
  so they come back **in memory**. The caller passes a buffer in RDI, so
  the thread moves to RSI, the callee's lower to RDX and the argument
  words start at RCX (then R8, R9, the stack). The callee writes
  `has_exception` as a byte at buf+0 and the slots from buf+8, a pointer
  being address then lower: `{char *p; long n}` is `{p@8, lower@16,
  n@24}`, `{char *p, *q}` `{p@8, lo@16, q@24, lo@32}`. The caller tests
  `cmpb $0, buf`. The signature still encodes just the result words:
  `{ptr, i64}` = `FI1084`, `{i64, ptr}` = `FI1154`, `{ptr, ptr}` =
  `FI1161`.
- **Larger returns are an sret pointer argument**, exactly as if written
  by hand: `struct {long a, b, c} f(long)` has the signature of `void
  g(struct three *, long)`, `FI2528`. The caller allocates the object.
- **Larger arguments are byval**: `take_three(struct three)` is `FIP0`
  and reads its argument from the generic buffers. nanofil rejects them.
- **Generic return of a struct**: word i (an eightbyte) at thread+128+8i
  with its lower at thread+384+8i, and the returned size is 8 × the
  number of words (16 for a two-word struct); callers check for at least
  that much. A generic entry for a buffered return calls the fast entry
  with a buffer on its own stack and copies the slots out.

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

## Variadic definitions and va_list

Verified against the same `163fae5` reference checkout, and clang's
`-S -emit-llvm` output for `tests/c/variadic.c`:

- Clang retains x86-64's `__builtin_va_list`: an array of one 24-byte,
  8-aligned record `{unsigned gp_offset, fp_offset; void
  *overflow_arg_area, *reg_save_area;}`. Fil-C uses only the first word
  as a capability-bearing cursor, **not** the native SysV register-save
  protocol. The other words remain unused. Array decay, array stride,
  sizeof and alignment must still be those of clang's record.
- `FilPizlonator.cpp:usesVariadicCC` selects signature zero for a function
  using `va_start` (not for a fixed-signature helper merely using
  `va_arg`). Its function object has fast entry NULL, generic entry
  `pizlonatedFIP0_name`, signature 0. Calls still use call-site-signature
  thunks; the mismatch sends them through the generic entry. All scalar
  arguments occupy eight payload bytes each, including int; a pointer's
  lower occupies the corresponding auxiliary slot, not another payload
  slot.
- Entry lowering around lines 17283–17323 computes the fixed-prefix
  size, calls `filc_promote_args_to_heap(thread, incoming_size)`, roots
  its lower in a dedicated frame slot, and retains snapshot + fixed size
  for every `va_start`. Promotion must precede body calls, even calls
  before the first start or on paths not executing start. The helper
  copies inline or outline CC data/aux into a readonly heap object,
  resolving boxed auxiliary entries. Its source is
  `filc_runtime.c:promote_cc_to_heap` (around 6214–6260); incoming
  pointees are rooted by the caller, and the helper tracks the new
  snapshot during allocation/copying.
- Intrinsic lowering around lines 7950–7969 makes start a checked
  pointer store, copy a checked pointer load and store, and end a no-op.
  Copying the cursor gives independently advancing lists.
- `VAArgInst` lowering around lines 14308–14342 calls
  `filc_get_next_ptr_bytes_for_va_arg(list_address, size, alignment)`.
  For int these are 4/4; for long and pointer, 8/8. The runtime helper
  (around 2468–2530) loads the list pointer with capability/alignment
  checks, aligns its cursor up to max(alignment, 8), checks the requested
  read against the cursor capability, checks write access to the list,
  and updates only its address (the lower stays unchanged). It returns
  **payload address and auxiliary-slot address**, not a flight pointer.
  These must be consumed immediately without a safepoint. A pointer
  load resolves a tagged atomic box if present and roots the loaded
  lower; integers load just their requested bytes.

**Checking means exactly what the pinned implementation checks.** There
are no scalar type tags: the helper cannot distinguish int from pointer
or signed from unsigned. An integer argument read as a pointer has no
capability and traps on dereference; reading a pointer as an integer
reads its address bits. It would be incorrect to promise a scalar
type-mismatch trap that clang-built Fil-C does not implement.
Also, promotion uses the allocator's 16-byte-rounded bounds, not a
separate logical argument end. A single eight-byte fixed argument with
no extras can leave eight readable padding bytes. Exhaustion tests use
a 16-byte incoming argument area and read at offset 16, so their first
missing argument is genuinely out of bounds in both compilers.

Nanofil keeps `func/5` unchanged: `va_args c(N)` marks an eager snapshot,
and `va_arg list_address` reads and updates its list in memory. The
backend's generic adapter promotes once, then passes the snapshot as a
hidden pointer argument to a private fast body. There is no safepoint
between promotion's return and the body's prologue rooting that lower.
The normal fast-body return code and existing generic result marshalling
handle scalar, pointer and buffered struct returns. Nonvariadic assembly
is unchanged. Escape analysis treats va_arg's list as accessed and
escaping, so `-O` cannot promote its storage out of memory.

Oracle reviewed snapshot lifetime, caller rooting, helper bounds and
alignment, and the adapter design **before implementation**. Its required
invariants were eager promotion using original incoming size, a dedicated
snapshot root before the first body safepoint, no safepoint while
unpacking helper results, and generic routing for recursive/same-module
calls too. Its two caveats were the absent scalar type tags and rounded
allocation bounds described above.

Verification:

- Before the change, `tests/c/variadic.c` failed at `__builtin_va_arg is
  not supported`; the interop fixture failed at `unsupported instruction
  va_args`. The old source tree was rerun from an archive, not inferred
  from the patch.
- The C difftest compares interpreter, nanofil and clang for int, long,
  pointers, independent va_copy cursors, repeated start, calls before
  start, a passed va_list, indirect calls, fixed pointers across the
  register/stack split, pointer-bearing struct returns, exhaustion and
  a forged pointer dereference. Runs pass normally and with `-O`, also
  under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`.
- `tests/filc/run-c.sh variadic` links seven cross-compiler cases: both
  call directions, passing lists both ways, pointer return, exhaustion,
  and a function-pointer call. It forces collections before and after
  extracting a pointer and passes with scribble/verify, at both levels.
  The first collection precedes even the va_args instruction, exercising
  the hidden entry root alone. Reducing nsum's emitted origin lower
  count from four to three (excluding that hidden root without changing
  the stored pointer) made case 0 fail with exit 133 and `filc safety
  error` under scribble/verify. The unmodified assembly passes.
- GNU hello 2.12.3 was configured using the pinned filcc with
  `--disable-nls` and built with `make V=1`. Reusing make's flags with
  `clang -E` reproduced the old errors at `lib/fcntl.c:209` (start) and
  `lib/version-etc.c:208` (arg). Both preprocessed translation units now
  compile with `nanofil cc` and assemble with GNU as. Replacing those
  two objects in libhello.a and relinking produced working `hello` and
  `hello --version`, including `--version` under scribble/verify. Make's
  relink log confirmed it reused the nanofil objects, without compiling
  them again with clang.
- Existing accepted fixture/program assembly outputs were compared
  byte-for-byte against the unchanged compiler: 27 identical outputs.
  The full Nix check covers both Prolog hosts, the existing corpus and
  the new variadic tests.

## Dynamic alloca and unreachable

At the pinned reference source, `FilPizlonator.cpp:14155` lowers an LLVM
`AllocaInst` to `allocate(Size, Alignment)`, including dynamic array
sizes. `allocate` at line 2745 returns `flightPtrForObject` for the new
runtime object. This is a GC allocation with its own capability, not a
raw stack adjustment. nanofil's `__builtin_alloca(n)` uses the existing
`alloc(16)` IR instruction at the call site (not hoisted), which calls
`filc_allocate_with_alignment(thread, n, 16)` and roots the returned
flight pointer just like every other `p` temporary. No new IR or check
elimination is involved. `tests/c/prog/alloca-bounds.c` writes the last
valid byte of a dynamic 32-byte allocation, then traps on byte 32 in both
nanofil and clang builds, also under the GC verification environment.
The runtime's `prepare_allocate_object` rounds sizes up to `FILC_MINALIGN`
(16 bytes), so the capability for a 37-byte request covers 48 bytes in
both compilers; byte 37 is not a valid bounds-trap probe at this pin.

The pass's `UnreachableInst` case at line 14392 calls the runtime error
helper with `llvm unreachable instruction`. nanofil instead uses its
existing `hlt` terminator, emitted as `ud2`: executing it stops rather
than falling through, but does not produce clang's diagnostic text.
