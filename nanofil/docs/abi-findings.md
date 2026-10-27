# Fil-C ABI findings at the filnix pin

Nanofil requires **staging Fil-C 0.687**, core revision `af81305` of
`mbrock/fil-c` branch `filnix-staging`
([lib/filc-staging.json](../../lib/filc-staging.json)). There is no 0.686
compatibility path. The original probes below were established at
`163fae5`; their emitted ABI contracts were rechecked against staging's
pass and runtime. The [handoff](handoff.md) is historical, not the target.
Rerun [probes/](../probes/) with `nanofil/probes/run.sh` and
`FILCC=/tmp/filcc/bin/clang` after building `.#filcc-staging`.

To read the sources at the pin, build the small reference checkout (about
6.5 MB: the design docs, `FilPizlonator.cpp` and its helper passes, the
clang pipeline and driver files, and the runtime):

```sh
nix build -o /tmp/filc-ref .#lib.x86_64-linux.filc-staging-ref-src
# /tmp/filc-ref/libpas/src/libpas/filc_runtime.{h,c}
# /tmp/filc-ref/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp
# /tmp/filc-ref/{Manifesto,gimso_semantics,invisicaps_by_example}.md
```

The full checkouts in [lib/sources.nix](../../lib/sources.nix) are for
building; `filc0-src` alone is about 1.6 GB.

## Staging differences that matter

Read the complete pass/runtime changes from `163fae5` to `35faf87`.
Upstream `43d345a81212` is the ABI break: 48-byte function origins and
per-static-site setjmp lowers/recreation replace the weak map. See the
setjmp section below. Thread fields nanofil uses, signatures, fast/generic
calling conventions, object headers, getter interface, access checks,
pointer aux loads/stores, allocation and scalar va_arg helpers retain
their emitted contracts. Staging adds thread fields only after existing
CC buffers; nanofil does not emit the changed unwind/fiber state.

The named staging changes were verified, not assumed harmless (their
rebased commits at this pin differ from the earlier branch IDs):

- **Descriptor local alias** (`d249619`, now `f708c342`): binds clang's
  descriptor to its module's implementation; no descriptor layout or
  entry signature change. Nanofil's existing function objects still work.
- **Getter cache** (`51e7f8c`, now `671bf4da`): optional module-private
  caller optimization. Getter arguments/results and initialization remain
  compatible; nanofil continues calling getters, without this cache.
- **Aggregate varargs** (`df06cdc`, now `0ded64b`): new aggregate packet
  lowering/intrinsic, not a scalar packet ABI change. Nanofil rejects
  aggregate va_arg and unnamed aggregate arguments; scalar varargs retain
  the same helper/packet contract.
- **Safepoints/may-free** (`e714461`): changes clang's analysis and adds
  non-exiting allocation helpers. Nanofil retains conservative roots,
  outline allocation and fresh access/aux checks, not cached not-free or
  aux facts across helpers/polls. No changed runtime calling sequence is
  required for what it emits.

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

The interpreter's [lifetime contract](lifetime.md) records the verified
libc wrapper, null/base-pointer validation, zero-sized objects, readonly
heap snapshots, shared alias invalidation and the boundary with GC. It
also documents the Oracle review and native/interpreter regression gates.

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
| `filc_function_origin` (including base node) | 48 | `function`, `filename`, `u32 num_lowers_ish`, pad, `personality_getter`, `u8 can_throw, can_catch`, pad to 36, `u32 num_setjmps`, `u32 num_stack_auxes`, pad to 48 |
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
  and reads its argument from the generic buffers. See *Byval
  arguments* below for what nanofil does with them.
- **Generic return of a struct**: word i (an eightbyte) at thread+128+8i
  with its lower at thread+384+8i, and the returned size is 8 × the
  number of words (16 for a two-word struct); callers check for at least
  that much. A generic entry for a buffered return calls the fast entry
  with a buffer on its own stack and copies the slots out.

## Byval arguments

Verified at the staging pin (FilPizlonator `argInfosForFunction`,
`iterateArgs`, `loadCC`, `storeCC`, and probes compiled with `-O2`).
A struct or union of SysV class MEMORY (over 16 bytes, or packed with
misaligned members) is a `byval` argument, and:

- **Any byval parameter makes the function generic-only**:
  `computeSignature` returns the generic signature 0 for a non-direct
  argument, so the function object has `fast_entry` 0 and signature 0,
  the generic entry is `pizlonatedFIP0_f`, and `pizlonatedFI0_f` is its
  alias. Callers of a byval function always go generic: direct external
  calls through the weak `pizlonatedFI0_f` thunk (getter, function
  check, then a tail jump to `*8(lower)`), indirect calls straight to
  the generic entry with RDX = the packet size.
- **Packet layout** (`iterateArgs`): each argument starts at an offset
  aligned to max(8, its ABI alignment) and advances by its alloc size;
  the total rounds up to 8. Payload at thread+128+off, aux at
  thread+384+off, inline up to 256 bytes. `take2(long, struct{long;
  char *; long}, long)` needs 40 bytes: the entry tests `cmpq $39, %rdx;
  jbe` and calls `filc_cc_args_check_failure(actual, 40, origin)`. A
  17-byte struct takes 24 bytes. So for alignment up to 8, a byval
  struct's eightbytes are consecutive 8-byte cells, the same cells a
  caller fills when it passes those eightbytes as separate words.
- **Caller** (`storeCC`): it copies the struct into a fresh heap object,
  zeroes payload and aux buffers on its stack, and demotes the object
  into them with `filc_demote_word_aligned_already_checked_heap_to_stack_without_exiting`
  (types with pointers) or `filc_demote_already_checked_heap_to_stack_without_exiting`,
  which write each pointer word's lower into the aux cell. Then both
  buffers are copied to the thread.
- **Callee** (`loadCC`): it copies the packet to its stack and calls
  `filc_promote_already_checked_stack_to_heap_without_exiting(thread,
  payload, aux, size rounded to 8)` (the `_with_alignment_` variant
  above 16), which returns a new heap object carrying payload and aux.
  That object is the parameter, rooted by the callee.
- **Variadic calls** put a byval struct in the packet the same way:
  `callv(fmt, big24, long, small16)` passes 56 bytes. An aggregate
  `va_arg` reads with `filc_get_next_ptr_bytes_for_va_arg(size)`.

nanofil reaches the same packet without a new IR form. A byval argument
is lowered as its eightbytes, one IR argument each, with a pointer
eightbyte as class `p`; a call carrying them is not generic-only by
itself, but it calls a generic-only callee through the thunk or the
dispatch, whose generic path writes each word and its lower to the
cell clang's demotion would. A function with a byval parameter also
takes the entry snapshot (`va_args`, unbound), so `filc_abi` makes it
generic-only exactly like a variadic function: its generic entry
promotes the whole packet to the heap (`filc_promote_args_to_heap`,
capabilities included) and passes the words to the private body, which
roots the snapshot. A small struct passed past a prototype's `...` goes
as its eightbytes too, as clang coerces it. A function of more than 16
words is generic-only as well, and its packet may use the outline
buffers (below). An aggregate `va_arg` reads one cell per eightbyte (a
pointer one with its capability).

## Structs with float members

Verified at the staging pin with `-O2` probes and `-emit-llvm`. Clang
classifies a struct or union of 16 bytes or less per eightbyte, as the
SysV psABI says (3.2.3), and FilPizlonator keeps the resulting scalar
types, so the fast signature has their digits:

| C type | fast form |
| --- | --- |
| `struct {float a;}` | one `float` (digit 1): `r_f1` returns `{i1, float}`, `FI269` |
| `struct {double a, b;}` | two `double`s: returned in XMM0 and XMM1 (`{i1, double, double}`, `FI436`), passed as two `double` arguments |
| `struct {long a; double b;}` | `{i1, i64, double}`: RDX and XMM0; arguments `i64, double` |
| `struct {double a; char *p;}` | `{i1, double, flight_ptr}`: XMM0, then RDX:RCX |
| `struct {double a; float b;}` | `double, float` |
| `struct {float a; int b;}` | one `i64` (a mixed eightbyte is INTEGER) |
| `struct {float a, b;}`, `{float a, b, c;}` | `<2 x float>` for the first eightbyte, which has no signature digit: the function is generic-only (`FIP0`), as a caller or as a callee, argument or result |

Integer words of a returned pair go in RDX then RCX and float words in
XMM0 then XMM1, whatever their order in the struct. In the generic
packet each eightbyte is one 8-byte cell, a float one holding its bits.
nanofil's `abi_eightbytes/4` gives each eightbyte the IR class `s`, `d`,
`l` or `p` accordingly, a pair of floats `l` (its bytes); a function
taking or returning such a pair takes the entry snapshot so it is
generic-only too, and `progtest.sh`'s `// signatures` mode compares
every exported `pizlonatedFI<Sig>_` name with clang's.

**More than 16 argument words, or 256 bytes of packet.** A call with
more than 16 fast words has the generic signature 0. A packet past the
256 inline bytes continues in the thread's outline buffers:
`cc_outline_buffer` at thread+640, `cc_outline_aux_buffer` at +648, and
their size at +656; `storeCC` first calls
`filc_thread_ensure_cc_outline_buffer_slow(thread, size - 256)` when the
size is short. nanofil's generic call paths do the same, and its call
sites with more than 16 words use a signature no object has, so they
always go generic.

**Distinct thunks for distinct word lists.** Every direct call of more
than 16 words has that one never-matching signature, so the weak thunk
it goes through cannot be named by signature alone: two calls to one
callee with different word lists (a variadic one, say, or `printf` with
18 and then 24 words) would share one thunk, sized for whichever came
first, and the second call's callee would read past its packet.
`filc_abi:call_symbol_signature/4` names such a thunk
`pizlonatedFIN<R>_<A>_<f>` instead, R and A being the bijective
base-11 values of the whole result and argument digit lists. Only
nanofil makes these weak hidden thunks; no definition exports such a
name. `tests/c/prog/wide-varargs.c` is the regression test.

## x87 long double

Verified at the staging pin with `-O2` probes (`-S` and `-emit-llvm`):

- `sizeof(long double)` is 16, `_Alignof` 16, `LDBL_MANT_DIG` 64. Data
  holds the 80-bit value in its first 10 bytes and zeros after: `0.1L`
  is `.quad 0xcccccccccccccccd` then `.short 0x3ffb`, padded to 16.
- A load or store is a 10-byte access with 8-byte alignment (the check
  is `addq $-10` against the upper bound and `testb $7`), then `fldt`
  or `fstpt`.
- **Fast convention.** Signature digit 3 (`FilPizlonator.cpp`'s x87
  digit). An argument goes on the native stack in a 16-byte slot: the
  caller writes `fstpt (%rsp)`, the callee reads `fldt 16(%rbp)`, beside
  integer words in registers: `ld(long double, int)` is `FI2000`, with
  the int in EDX. A result comes back in ST0 beside `has_exception` in
  AL: `long double f(long double *)` is `FI1069`, and a struct of one
  long double is returned as `{i1, x86_fp80}`, also in ST0 (`FI537`).
- **Generic convention.** A long double is one 16-byte cell: the
  generic entry of `ld(long double, int)` checks a 24-byte packet, reads
  the value with `fldt 128(%rdi)` and the int at thread+144. A cell
  holding one starts at a 16-aligned offset: after an `int`, a long
  double is at +16. A generic return writes `fstpt` at thread+128,
  zeroes bytes 138–143 and the aux word at +384, and returns size 16.
- **Structs.** A struct or union holding a long double is SysV class X87
  or MEMORY. As an argument it is generic-only (`FIP0`), as is any
  function taking one; a 32-byte one returns through sret.
- **Variadic.** `va_arg(ap, long double)` is
  `filc_get_next_ptr_bytes_for_va_arg(ap, 16, 16)`, then `fldt` from
  the returned address. A variadic call's packet holds each long double
  in a 16-aligned 16-byte cell; clang calls even a variadic callee
  through a `pizlonatedFI<Sig>` thunk whose generic fallback lays the
  packet out so. An aggregate `va_arg` of a struct of long doubles takes
  its size at alignment 16 at once.

nanofil (float.md, *x87 long double*) keeps long double values in the
IR class `x` and never puts one in the fast convention. A function
taking or returning one, or a struct holding one, is generic-only, and
its long double words are the 16 bytes as two `l` words at a
16-aligned packet offset, after a zero pad word when needed. A clang
caller's FI thunk finds no matching signature and uses the generic
entry, and nanofil's calls of clang functions go generic through
nanofil's own thunks. `tests/c/prog/ldouble.c` checks both directions
against clang, directly, indirectly, variadically and with wrong
prototypes, under FUGC_SCRIBBLE and FUGC_VERIFY too.

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

Nanofil keeps `func/5` unchanged: `va_args const(N)` marks an eager snapshot,
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
Variable length arrays lower the same way: an `alloc` of the run-time
size where the declaration is reached, which is what clang's dynamic
`alloca` becomes under the pass (`tests/c/vla.c` traps one past a
16-byte array in nanofil, the interpreter and clang alike).
The runtime's `prepare_allocate_object` rounds sizes up to `FILC_MINALIGN`
(16 bytes), so the capability for a 37-byte request covers 48 bytes in
both compilers; byte 37 is not a valid bounds-trap probe at this pin.

The pass's `UnreachableInst` case at line 14392 calls the runtime error
helper with `llvm unreachable instruction`. nanofil instead uses its
existing `unreachable` terminator, emitted as `ud2`: executing it stops rather
than falling through, but does not produce clang's diagnostic text.

## Scalar floating point (M9)

Checked against `filc-ref-src` at the pin, not upstream head:

- `FilPizlonator.cpp:1130–1143` assigns fast type digits **float = 1,
  double = 2** (integer = 0, pointer = 7). The existing bijective base-11
  signature formula applies: `float(float)` is FI269; `double(double)`
  is FI403. `normalizeArgType` (6074) only widens small integers: floats
  retain their type and are never normalized to integer words.
- `fastFunctionTypeForSignature` (13503) prepends thread and callee
  lower, and returns `{i1 has_exception, float|double}`. Scalar floats
  use the independent SysV XMM0–7 argument bank and return in XMM0,
  with the exception flag in AL. They consume no integer argument
  register. Stack overflow from either bank follows source order;
  pointer halves still split across R9 and stack. These transformed
  fast functions are not variadic: SysV's vector-count AL applies only
  to ordinary plain variadic calls, not Fil-C generic calls.
- `iterateArgs` (6030) rounds each generic argument position to eight
  bytes. `storeCC` (6516–6543) zeroes the entire payload and aux buffers
  before typed stores. Thus an outgoing s slot is low four payload
  bytes plus four zero bytes and eight zero aux bytes; d is eight
  payload bytes and eight zero aux bytes. Generic fallback reinterprets
  bits, without numeric conversion. Preserve argument/result size checks.
- Ordinary scalar memory stores differ from generic marshalling:
  `storeValueRecurseAfterCheck` (2551) stores only payload for types
  without pointers. A float overwrite leaves any previous aux alone,
  like an integer store. No pointer barrier or aux allocation is needed.
  Loads/stores check four/eight bytes at alignment one, including the
  existing write permission checks; s must not read eight bytes.
- `va_arg` (14308–14340) uses type size/alignment, then immediately
  loads the payload. `filc_runtime.c:2468–2530` rounds alignment up to
  eight, checks the read and cursor write, and advances the cursor.
  Passing 4/4 for s or 8/8 for d to the existing checked helper works;
  ignore its aux result and consume payload before a safepoint. C
  default argument promotion still passes float as double.

Safety boundaries: float bits in private eight-byte slots carry no
capability. Generic outgoing slots must clear aux even after an earlier
pointer argument. Ordinary float stores must not create capabilities.
Mixed-call adapters retain caller-rooted pointer arguments, and variadic
adapters retain the promoted snapshot's root. Save incoming XMM arguments
before calling getters, which may clobber them. Test returned AL before
using RAX as a float-bit scratch register. An independent reviewing
subagent (Oracle) checked the implemented sequences against the pinned
pass/runtime: **no soundness blockers found**, scoped to scalar s/d and
the existing integer/pointer tuple returns, including buffered tuple
returns with float arguments. It verified zero generic aux/padding,
payload-only ordinary stores, AL handling, independent banks, XMM saves
before getters, caller roots and the promoted snapshot's lifetime. Its
suggestion to retain an executable buffered-return regression is covered
by the buffered-return interop cases below.

Reproducible coverage:

- `tests/fixtures/float.ir`: arithmetic, NaN/unordered comparisons,
  casts, signed and unsigned conversions (including above 2^63),
  s/d memory and static data, phis and simultaneous GPR/XMM spills.
- `tests/filc/run-c.sh float`: clang ↔ nanofil scalar parameters and
  returns, mixed spills, direct and indirect calls, generic bitwise
  mismatch in both directions, zero single-precision padding, attempted
  float-to-pointer forgery (traps), double va_arg in both directions,
  short varargs and invalid memory accesses (trap), and buffered tuple
  returns with float arguments through fast and generic adapters.
  The harness forces collections while pointer arguments/snapshots are
  live; run with `RUN_ENV='FUGC_SCRIBBLE=1 FUGC_VERIFY=1'` on both hosts.
- Both new modules fail on the pre-M9 backends after the IR grammar
  lands: `backend cannot emit $floats` and `Fil-C backend cannot emit
  $nfloat`. A plain SysV nine-double variadic probe gives 45 on both
  hosts; planting AL=0 gives 9, catching a missing vector-register count.
- Scratch native differential checks: 368 arithmetic/comparison/unsigned
  conversion bit patterns agree with QBE (including NaNs, infinities,
  subnormals and signed zero), and 896 conversion cases agree with C and
  QBE, on both hosts. Existing accepted fixture and C input assembly
  remains byte-identical (35 inputs).

## Setjmp and longjmp

Verified in staging `35faf87`, not inferred from libc conventions:

- `FilPizlonator.cpp:3439` assigns `Setjmps[CI] = FrameSize++` after
  all ordinary/stack-aux slots; origins at 1764–1782 encode the count.
  The type at 16695 has `{node, ptr, i8, i8, i32, i32}`, agreeing with
  `filc_runtime.h:465–521` and the 48-byte table above.
- Lowering at 8583–8603 calls `filc_jmp_buf_recreate(thread, &slot,
  kind, mask)`, stores its flight pointer into the user buffer and calls
  **native `_setjmp` in the caller**. No weak-map helper remains in this
  path. Kind numbers remain setjmp=0, _setjmp=1, sigsetjmp=2.
- `filc_runtime.c:7981–8064` allocates/root-initializes a site's jmpbuf
  once, reusing its identity thereafter. Every execution overwrites its
  saved lowers with barriers and updates its native destination. All
  user buffers from that site alias its latest execution (#335).
- `filc_native_zlongjmp` (8066–8139) searches the highest `num_setjmps`
  lowers for the exact jmpbuf, rejects expired destinations with
  `cannot longjmp unless the setjmp destination is on the stack.`,
  unwinds intermediate frames and restores ordinary lowers, **skipping
  the site slots**. Native stack payload slots are not restored.
- Staging `af813053ecb5` resets the signal-mask policy on every recreation,
  fixing same-site mask 1→0 reuse without changing this ABI; see
  [setjmp.md](setjmp.md). Both toggle directions are regression-tested.

Nanofil's approved IR, conservative payload snapshot, optimizer barrier,
Oracle review conditions and test coverage are in [setjmp.md](setjmp.md).

## Safepoints between a check and its access

Verified at the pin for [pizlonation.md](pizlonation.md), which has the
details:

- `filc_object_ensure_aux_ptr_outline` can exit (a safepoint): for an
  object larger than `FILC_MAX_BYTES_BETWEEN_POLLCHECKS` it zeroes the new
  aux between `filc_exit_with_allocation_root` and
  `filc_enter_with_allocation_root` (filc_runtime.c:2575-2590), and
  `filc_exit` runs deferred signal handlers and the pollcheck callback
  (filc_runtime.c:1231-1266). `filc_store_barrier_for_lower_slow` does
  not exit (`barrier_impl`, filc_runtime.c:2278).
- `free_impl` sets `upper = lower` and the FREE flag but keeps the aux
  pointer (filc_runtime.c:3172-3195). Frame lowers are marked with plain
  `marker.mark` (filc_runtime_inlines.h:459), so a freed object a frame
  still roots is not reclaimed; heap references to freed objects are
  redirected to `filc_free_singleton` (fugc.h:162-170).
- `filc_allocate` exits only for sizes above
  `FILC_MAX_BYTES_BETWEEN_POLLCHECKS` (filc_runtime.c:2919, 2954-2957).

## Nonescaping LocalExplicit storage

Verified against the same staging pin, not inferred from heap lowers:

- `FilPizlonator.cpp:17626-17655` gives each nonescaping alloca a
  payload and separate aux. `alignedAllocaSize` rounds physical storage
  to `GCMinAlign` (16); payload alignment is at least 16, aux alignment
  is 8. LocalExplicit adds one word before aux for its count header.
- `initializeNonescapingAlloca` (8276) stores the physical word count,
  records `AuxAlloca` in an `ExplicitStackAux` frame entry, and zeroes
  both payload and aux. LocalNaked instead replicates individual lowers
  into ordinary frame roots. Nanofil uses only LocalExplicit, initializes
  before publishing the root, and retains exact logical bounds.
- `filc_runtime.h:425` defines `filc_stack_aux` as `size_t num_lowers`
  followed by `void *lowers[]`. The origin's special root range is
  `[num_lowers_ish - num_setjmps - num_stack_auxes,
  num_lowers_ish - num_setjmps)` (2189-2206).
- `filc_mark_outgoing_ptrs_in_frames` (filc_runtime_inlines.h:413-460)
  distinguishes that range **before** converting a lower to a heap
  object. It skips null stack-aux roots, otherwise scans precisely the
  header's word count. Registering the native aux address as an ordinary
  heap lower is invalid; it is not a heap object with a hidden header.

Nanofil's ABI product carries `local(Name,Size)` storage descriptors and
distinct `stack_aux(Name)` root keys. `origin(Which,Catch,Roots,Setjmps,Locals)`
states both suffix counts. Local payload/aux never enter the temporary
alias pool; the origin remains correct across calls and pollchecks.
The exact IR, lifetime and conservative selection policy are in
[m5.md](m5.md#nonescaping-local-storage).
