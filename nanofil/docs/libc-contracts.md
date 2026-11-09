# Native libc contracts for Campaign 7

This is the trusted external-call boundary for `hi.c` and the **56
distinct libc names** in the [Hello census](trap-census.md), plus `puts`
and the all-object `fcntl` obligation. It is a specification with native
counterexample probes, not a proof of libc or of Hello. It changes no
Prolog/Rocq execution rule: `external_call` still models only `free`.
Campaign 4 can turn each row's precondition, footprint, result and
failure alternatives into an external-call relation, without treating
an unimplemented call as success.

## Trusted entry and host boundaries

The trusted libc boundary includes the pinned launcher, libc/TLS
initialization and host-exit completion (mbrock's decision), not only
functions called after main begins. These are **named specifications**
in [HiArtifact.v](../rocq/theories/HiArtifact.v), not proved native
implementations or new global Rocq axioms:

| Trusted contract | Successful observation / guarantee | Native counterexample probe |
| --- | --- | --- |
| `HiProgram R.trusted_entry_contract` | A successful eligible launch supplies the exact ready runtime state and entry memory, readable argv/environment vectors, the module's checked literal, opaque libc/TLS/stdio validity, and a well-formed nonwide stdout with its actual registration inventory. | [libc-entry.c](../tests/c/prog/libc-entry.c): fresh re-execs with empty/nonempty environments and empty/high-byte strings; writable NULs; errno and initial streams; initialized TLS and usable libc in a constructor before main. |
| `HiProgram R.trusted_host_contract` | An explicit completion witness at the exact ready soft/hard handoff permits one low-byte process-exit observation. The finished state remembers the handoff snapshot, not native postmortem memory. | [libc-exit.c](../tests/c/prog/libc-exit.c): fresh-exec main return −1, exit(258), _Exit(−2), and _exit(513), checking wait status and exact descriptor bytes; soft handlers precede buffered flush, hard exit does neither. |

Entry satisfaction is directional: a successful eligible native launch
supplies this image; it does not say every satisfying tuple is natively
constructible. The `startup_at` component is a **readable projection**,
not a proof of writable strings, complete TLS layout or initialization
write footprints. The probe checks some stronger native facts. Copying
still requires the native `argc + 1` int arithmetic to fit, before size
multiplication; readable `startup_at` alone is not that precondition.
Resource refusal or unfinished startup is not a successful entry, and
the contract does not claim startup always succeeds. Eligible application
constructors and retained callbacks require their own valid contracts;
the trust boundary cannot make arbitrary user code safe. In particular,
the entry inventory is not assumed empty merely because hi.c registers
no handlers.

The host contract retains a separate **actual completion witness**:
readiness and a handoff phase alone do not establish native termination.
Host handlers, loader finalization and host stdio are inside the trusted
boundary. Its current observation interpretation projects host-only
activity to the final process-exit event; descriptor bytes in the probe
are not `StreamBytes` acceptance events or a durability promise. A host
callback re-entering modeled Fil-C is not silently hidden by this
projection: its effects/observations require an additional contract.
Richer host-prefix coverage, blocking/resource behavior and universal
termination are not proved here. Completion leaves the remembered
outstanding obligations untouched; neither soft nor hard completion
proves delivery, and hard exit requires no flush or empty pending list.

The native probes are finite counterexample evidence for these trusted
specifications, **not universal native satisfaction proofs**. Rocq
derives application-only nonfailure and the witnessed terminal step
from the predicates. Conditional puts/shutdown composition is proved in
`Selected.v`; native lifecycle satisfaction and coverage remain separate
obligations.

## Trusted selected shutdown boundary

`Selected R.selected_contract` and `Selected R.boundary` in
[Selected.v](../rocq/theories/Selected.v) name the trusted lifecycle segment
interface for the [pin below](#pin-notation-and-common-obligations). It is
parameterized by the actual native representation, selection and footprint
specifications. The logical `SelectedChecks.specs` is **not** that pinned
native instance. No new Rocq axiom or native implementation theorem is added.

The selected boundary owes three separate obligations:

- **Independent admission:** eligible startup inventory and retained pending
  and active callback authority establish source-state validity, action
  selection and ABI/preconditions before any invocation exists. Token
  distinctness does not make arbitrary callbacks safe.
- **Native satisfaction:** each selected native segment obeys its declared
  memory permissions, resource outcomes, control transfers and observations.
  Internal registry traversal/unlink/retirement and done/lock work belong
  before the next genuine logical cutpoint, not silent outer callback actions.
- **Coverage:** applicable finite native observations map to normal segments,
  unfinished/resource observations or the separately witnessed host boundary.
  This must include behavior for which no normal invocation exists. The
  current partial-output vocabulary does not prove coverage of arbitrary
  mixed native segments; a missing case stays an open obligation.

Host-only projection may not hide modeled callback re-entry, output or control
transfers. Callback specifications remain prerequisites, including for
callbacks that register further callbacks or recursively exit. The existing
[libc-exit.c](../tests/c/prog/libc-exit.c) probe checks handler ordering,
re-registration/re-entry, retained argument lifetimes, block boundaries and
soft/hard status/flush distinctions; [libc-output.c](../tests/c/prog/libc-output.c)
checks finite output/error cases. These are finite evidence, not universal
coverage, callback-dispatch or native-satisfaction proofs.

The `admitted_without_behavior` control keeps an inhabited source's validity,
selection and preconditions while replacing only its segment-prefix predicate
with `False`. Admission still holds, but no prefix or invocation exists.
Consequently neither independent admission nor the absence of invocations can
discharge this boundary's coverage obligation. The conditional hi composition
theorem consumes supplied witnesses; it cannot manufacture the missing ones.

## Pin, notation and common obligations

The pin is `lib/filc-staging.json`'s core revision
[`18b6663a2785`](https://github.com/mbrock/fil-c/commit/18b6663a2785c8eba6cc2a544a7711e19fc448c7),
Fil-C glibc 2.44 (`runtime/filc-glibc.nix`) and the flake's toolchain.
Sources can be read without building a compiler:

```sh
nix build -o /tmp/filc-ref .#lib.x86_64-linux.filc-staging-ref-src
nix build --impure -o /tmp/libc-source --expr '
  let f = builtins.getFlake (toString ./.);
      pkgs = import f.inputs.nixpkgs { system = "x86_64-linux"; };
  in (import ./lib/sources.nix { inherit pkgs; variant = "staging"; }).user-glibc-src'
```

Libc paths below are relative to `projects/user-glibc-2.44/` in the
second tree. Runtime paths are relative to `libpas/src/libpas/` in the
first. Sources of the contracts are C17 library clauses, POSIX/GNU API
semantics, and these pinned implementations; tests are independent,
finite evidence, not a replacement for that trust.

- `R(p,n)` / `W(p,n)`: the capability, not just the address, permits
  reading / writing the n bytes beginning at p in a live object; a
  typed cell additionally has its type's alignment and width. Zero
  length does not license an arbitrary forged pointer: use a live
  pointer, possibly one-past, unless a row explicitly permits null.
- `S(p)` is `R(p,k+1)` for some k with p[k] the first NUL. `WS(p)` is
  the corresponding aligned wide string. No bound on k is imposed by
  the entry contract. `B(p,n)` requires readable bytes through the
  first NUL if it occurs before n, otherwise n readable bytes.
- `H(p)` means a live heap **base**, owned by the caller for release;
  it is not a local/global/interior pointer. A stream or descriptor is
  an opaque live libc object, not a raw address with enough bytes.
- Every call uses its declared Fil-C ABI, including the return channel.
  Variadic arguments must supply every selected argument with the
  promoted type/width the callee consumes. Too few argument bytes can
  raise `ArgumentSize`; an incompatible return channel `ReturnSize`.
  Equal ABI widths alone do not establish C type correctness.
- A run starts with no installed signal handler and no other program
  thread, and excludes interposed libc. Locale, argv and
  environment values are otherwise unrestricted. I/O may fail, block,
  or be partial; allocation may refuse. The probes' C locale and short
  strings are fixtures, **not** hypotheses of `never_panics`.

### No asynchronous program execution

No libc contract may admit installing a signal handler or starting another
program thread, directly or through a callback or trusted host boundary.
`signal`, `sigaction`, `pthread_create` and `aio_*` are outside contract
coverage; `timer_create` and `mq_notify` with `SIGEV_THREAD` are excluded
as well. Reaching such an unsupported external call ends the covered run:
it is not a successful call, nor permission to continue under the safety
theorems. Entry must establish the no-handler/no-other-program-thread
premise, including for application constructors.

The runtime safepoint describes the collector alone. The collector does
not free objects; signal handlers and additional program threads would
execute program code, not collector actions. This exclusion is therefore
a premise of the runtime-based theorems, not merely a probe convention.
It does not exclude the synchronous `atexit`/`__cxa_atexit` callbacks below,
whose targets and effects must satisfy their own contracts. See
[runtime-axioms.md](runtime-axioms.md) for the entry and collector boundary.

### Memory invariants shared with Campaign 3

Every returning row preserves **identities** (`ids` / `persists`): an
old object remains present, unchanged as a region or emptied/freed;
none is deleted, moved in place, shrunk in place or retagged. Allocation
creates only **fresh** identities, with the runtime's alignment,
nonoverlap, address-space and zero-initialization guarantees. Returned
interior pointers keep their source capability. A new raw address is
never authority to a different old object.

Between allocations, byte and stored-capability writes are **kept**:
inside live objects available to the call. Each row names those roots
and any release. Roots include explicit arguments **and** the reachable
libc state: errno/TLS, standard streams, locale/conversion caches,
getopt state, environment and exit registrations. These roots must be
present in the future initial memory/environment relation; they are not
permission to havoc all program memory. Cells storing pointers update
their capabilities as well as bytes. No row grants writes to unrelated
caller objects. Collector bookkeeping follows [runtime-axioms.md](runtime-axioms.md).

Strict `Runtime.kept m m'` itself excludes new identities. Thus an
allocating call must be a composition of `fresh` allocation steps and
`kept` segments, **not** a claim of `kept` for its entire transition.
`realloc`, `fclose` and `iconv_close` end objects but retain their old
identities. Cache replacement also ends rather than erases identities.
Callbacks compose their own contracts; they are not hidden exceptions
to these invariants. No row breaks these three conditions. Startup
establishes initial memory rather than being a returning memory step;
termination has no post-state, but its prefixes obey the conditions.

### Traps: admissible inputs versus violations

With every precondition met, including reachable libc state and
callback contracts, the trusted claim is **no capability panic**.
`OutOfMemory`, `TooBig`, and native stack exhaustion remain possible
resource endings for calls that allocate (including internal scratch,
formatting, TLS and callback frames). They are not panics. Do not replace
them with mandatory null results: `axiom-address.c` observes both
allocation diagnostics. API errors below are ordinary results, not UB,
unreachable, or a stuck external call.

The following failure codes in the tables enumerate the capability
checks a violated memory/ABI premise can reach, not a promise that
**every** out-of-contract C call traps, nor an exact first diagnostic:

| Code | Fil-C model reasons |
| --- | --- |
| `R` | `NullCapability`, `OutOfBounds` (also a freed alias), `Misaligned` for typed loads |
| `W` | `R` plus `Readonly` for stores |
| `V` | `ArgumentSize`, `ReturnSize` at ABI boundaries; selected pointer arguments also use `R`/`W` |
| `F` | `InvalidFree`, `DoubleFree` (bad heap base/lifetime) |
| `C` | `NotAFunction`, `ArgumentSize`, `ReturnSize`, plus the callback's own trap set |
| `—` | no argument-induced capability trap in this row |

An incorrect scalar domain, format syntax, overlap, opaque handle or
conversion-state representation is **outside the contract** even if
this pin happens not to check it. It cannot be used as an axiom for
trap-freedom; UB and unreachable must still be ruled out. The codes are
not a new executable semantics for those invalid C cases. Early forms
of a memory check have the same obligation, not a new exemption.

## 1. Byte/string regions (12 Hello names)

No mutation except the named destination or fresh allocation; no
release. Source pointers may alias where the API permits it. Comparisons
promise a sign, not precisely −1 or +1. Character searches compare the
argument converted to unsigned char (string searches as C specifies).

| Name | Precondition | Guarantee / footprint | Violated checks |
| --- | --- | --- | --- |
| `strlen` | `S(s)` | first-NUL offset; reads through NUL | R |
| `strnlen` | `B(s,n)` | min(first-NUL offset,n); never needs byte n | R |
| `strchr` | `S(s)` | first match including NUL, or null; same object | R |
| `strrchr` | `S(s)` | last match including NUL, or null; same object | R |
| `strcmp` | `S(a), S(b)` | unsigned-byte lexicographic sign, zero iff equal | R |
| `strncmp` | `B(a,n), B(b,n)` | sign of first difference before n or a NUL; n=0 gives zero | R |
| `memchr` | `R(s,n)` | first matching byte among n, or null; same object | R |
| `memcmp` | `R(a,n), R(b,n)` | unsigned-byte lexicographic sign of n bytes | R |
| `memcpy` | `R(s,n), W(d,n)`, nonoverlap | copies bytes; complete aligned pointer slots retain source authority; returns d | R,W |
| `mempcpy` | same as memcpy | same copy, returns d+n (possibly one-past), not new authority | R,W |
| `memset` | `W(d,n)` | n bytes set to low byte of c; clears metadata for every touched pointer word, even a partially touched word; returns d | W |
| `strdup` | `S(s)` | fresh owned writable copy including NUL, or allocation refusal; does not retain ownership of s | R |

Probe: [libc-regions.c](../tests/c/prog/libc-regions.c). It checks bounded
nonterminated arrays, asymmetric copies with neighbouring sentinels,
comparison signs, missing NUL, short destination and a search-result
alias after free. strnlen additionally stops at short-object NULs with
SIZE_MAX, handles unaligned high bytes (128 and 255) through the end of
an explicitly aligned 16-byte allocation, and permits
zero-count live writable/read-only one-past pointers. Its Rocq contract
in [ExternalCalls.v](../rocq/theories/ExternalCalls.v) requires readability
only through the consumed bytes (including an early NUL), not the entire
maximum; zero count still requires live authority. The contract is pure,
nonallocating and independently inhabited, not a native termination proof.
Pinned strnlen delegates to memchr; generic and multiarch implementations
need not read only bytewise, so these probes do not prove universal native
satisfaction of that API premise. The probe also copies a complete stored pointer and clears
its authority with a one-byte memset that leaves its address unchanged.
The auxiliary footprint is word-granular within the containing live
object, not restricted to n shadow bytes; arbitrary partial pointer
copies need the runtime's smidgen/boxing relation before formal use.
Source: `string/` and `filc_runtime.c` `memset_impl_specialized`,
`memmove_aux_loop_body`, `memmove_smidgen`. Runtime-only `zmemmove` needs the same two
ranges but permits overlap; it is not a 57th libc import.

The additive Rocq `memset_contract` separates exact byte and auxiliary
frames. It requires canonical int and size_t, a live Obj covering the
destination bytes, and, for positive counts, an eight-aligned object base.
The destination itself may be unaligned. Base alignment is an explicit
conservative model premise, not an extra runtime axiom: native auxiliary
rounding is relative to the object's lower bound, while model slots use
absolute alignment. The internal writable permission hull rounds its start
down but not its end up; its writability is derived from the byte authority
and base alignment. Prefixes and completions still preserve all raw bytes
outside the requested interval, even before the destination inside that hull.
Only aligned slots intersecting a nonempty fill may change; completions
clear them to CNone and repeat the converted low byte in the byte interval.
No capability is imported from auxiliary memory; returning d retains exactly
its original address and capability. Regions and world remain unchanged,
without allocation, release, ownership transfer, resource ending or event.

Zero count has an empty byte and auxiliary footprint, including at an
unaligned live one-past pointer, and needs no base-alignment premise. Its
live-Obj admission is deliberately stronger than the native empty path,
which returns before checking null, Ro or expired authority. Rejection by
this conservative contract is not a claim that those native calls trap.
The input-only logical result constructs an invocation, and existing effect
theorems preserve readiness and identities. Native probes distinguish byte
repetition, preceding-slot clearing with unchanged raw pointer bits,
neighbouring capability preservation, exact word endpoints and zero counts.
They do not instantiate universal native coverage or termination. Large
paths contain internal filc_exit/filc_enter safepoints, where the collector
may rewrite unrelated stored capabilities to freed objects; their relation
to this exact logical frame remains an explicit native-coverage obligation.

The additive Rocq memcpy/mempcpy/memmove contracts share original-snapshot
bytes and auxiliary words. A complete destination word imports precisely
the original translated source slot when in phase; partial smidgens and
out-of-phase transfers clear authority. This includes partial self-copies;
there is no general self-copy no-op law. Byte nonoverlap is required for
memcpy/mempcpy, not memmove, and does not require disjoint auxiliary hulls.
The source span licenses only complete-slot reads, never source writes;
the destination pointer supplies its own return authority. Positive counts
require aligned object bases but permit unaligned starts. Native lower/box
correspondence is an explicit representation obligation, not an extra
capability constructor or permission to reassemble pointer fragments.
Ready fixtures and arbitrary-completion controls distinguish overlap
directions, Ro/Obj preservation, CNone overwrites, partial/self/phase effects,
neighbours, adjacent bytes, zero and a one-past mempcpy return. Native rows
exercise pointer-array overlaps, an end-return copy and unchanged-bit
fragment/phase copies that lose usable authority. Internal auxiliary
allocation may fail or exit/re-enter even for small counts, so universal
resource and collector-prefix coverage remains uninstantiated. These are
logical effect/nonvacuity results, not native execution or termination
proofs. String-copy auxiliary effects require separate source evidence.

The Rocq strlen contract requires a live object capability through the
first NUL, even for an empty string, and returns its exact offset as a
canonical size_t. It frames the entire memory and world. Its read-locality
theorem identifies the object's region/life and precisely the bytes through
that NUL; auxiliary slots and other memory are not dependencies. Under
runtime readiness this domain is equivalent to the existing checked
list-string predicate used by puts, without changing puts's premises.
Additional probe rows check high bytes and unaligned starts through an
aligned 16-byte allocation's final-byte NUL, including length zero at that
byte. The pinned generic strlen can load before the argument (downward
alignment) and beyond its logical terminator. These finite probes neither
prove universal native satisfaction nor identify the linked implementation;
the logical read footprint is not a native byte-load trace.

The Rocq memchr contract requires the full readable span independently of
the result, compares the canonical int's low byte, and returns the first
matching pointer with exactly the input capability, or null. Additional
probe rows check competing high-byte matches (including negative int
conversion), binary zero, a last-readable-byte hit, an exact-bound miss
and zero count at a live allocation's end. Pointer equality in these finite
native checks alone does not establish capability equality; the model's
postcondition states that stronger trusted requirement explicitly.

The Rocq memcmp contract shares memchr's full-span `readable_bytes`
premise for both inputs, permitting overlap. Its result promises only
the unsigned lexicographic sign in a canonical signed-int representation,
not a fixed magnitude. Public invocation fixtures admit distinct nonunit
results of each sign. Native rows distinguish signed-char comparison,
last-difference comparison, stopping at binary zero and reading beyond
the count; they also cover identical/overlapping spans and live one-past
zero counts. These are finite checks of the trusted API specification,
not a bytewise implementation model or universal native-satisfaction proof.

The Rocq strncmp contract instead uses independent early-NUL bounded-string
premises. Its logical comparison window includes the earlier terminator
when present, excludes byte n, and is proved readable through both input
capabilities. It reuses the sign-only result specification; public calls
permit both signs with magnitude 512. Native rows check huge bounds with
short strings, differing bytes after a shared NUL, a terminator versus a
nonzero byte, unsigned ordering, exact-count allocation ends, overlap and
zero-count one-past pointers. The independent premises are conservative,
not the weakest operational domain. Wider native loads remain a separate
implementation obligation; neither native termination nor universal
contract satisfaction follows from these finite observations.

The Rocq strcmp contract independently requires both complete terminated
strings. Its comparison window includes the earlier NUL; this does not
waive the longer string's remaining admission obligations. The identity-keyed
input footprint is each referenced region/life plus its bytes through its
own NUL, with no auxiliary-slot dependency. Completions preserve all memory
and world, returning only the unsigned-byte order's signed sign with any
canonical int magnitude. Public controls permit ±512 and reject wrong signs.
Native rows distinguish shared NULs, strict prefixes, overlap, empty strings,
distinct equal aligned allocation-end strings, a final-byte difference and
an earlier opposite unsigned difference. Pinned generic strcmp can load
before its second argument when aligning and merge words beyond the logical
comparison dependency; these are trusted native-satisfaction obligations,
not guarantees established by the finite probe or a termination proof.

The Rocq strchr contract requires a complete terminated string independently
of an early match, plus a canonical int word. It returns the first low-byte
match including NUL, with exactly the source capability, or null. Its read
dependencies are the source identity's region/life and bytes through NUL,
not auxiliary slots. Its zero-size capability source permits only copying
the source pointer's authority, not importing an auxiliary slot; this is
distinct from its nonempty logical read footprint. No ownership transfers,
and the returned capability is invalidated when the source lifetime ends.
Every completion preserves memory/world and has no observations or resource
or exit ending. Public invocation controls distinguish first from later
matches and reject correct-address capability amplification/loss. Added
native rows check 511, -1, 0 and 256 conversions, aligned/interior final-byte
NULs, empty strings and a nonzero byte only after the first NUL; the existing
repeated-match and freed-result controls remain. Pinned generic strchr
delegates to strchrnul, which aligns downward and scans words. Loads before
the argument or beyond the logical dependency interval remain trusted
implementation obligations; these finite observations prove neither
universal native satisfaction nor termination.

The Rocq strrchr contract shares strchr's independently terminated input,
canonical int and count-free pointer-result ABI, but returns the last
low-byte match through NUL. A hit retains exactly the source capability;
a miss is canonical null. The read dependencies are the same identity/life
and complete string bytes, independent of the zero-size capability source;
there are no auxiliary dependencies, writes, allocations, release,
observations, resource or exit endings. No ownership or lifetime extends
with the returned pointer. Constructive input-only invocation existence and
exact pointer uniqueness do not prove native execution or termination.
Public controls distinguish first from last, conversion, empty/NUL searches,
false hits and capability substitution. Native rows distinguish repeated
matches, an empty suffix from high bytes before it, and a byte only after an
early NUL, using a dedicated aligned final-NUL array. Pinned generic strrchr
calls memrchr over `strlen(s) + 1`: both the forward length scan and the
backward word scan (with rounded endpoints and masked boundaries) can load
outside the logical dependency interval. Universal native satisfaction and
implementation selection remain trusted obligations, not probe conclusions.

## 2. Heap lifetime (5)

All fresh results satisfy the runtime axioms. Requested size is a
**minimum** capacity, not necessarily the capability's exact upper:
`filc_prepare_allocate_object` rounds to `FILC_MINALIGN` (16 here);
`filc/include/stdfil.h` explicitly documents that `malloc` forwards to
`zgc_alloc`. The tests cross 16-byte bounds, not malloc(3)'s padding.

| Name | Precondition | Guarantee / footprint | Violated checks |
| --- | --- | --- | --- |
| `malloc` | unsigned byte count n | fresh owned storage of at least n bytes, or refusal; no old caller object changes | — |
| `calloc` | unsigned counts a,b | detect multiplication overflow (null/ENOMEM); otherwise allocate product, zero bytes and pointer metadata, or resource refusal | — |
| `realloc` | p=null or `H(p)` | positive-size success allocates fresh storage, copies at least min(old requested size,n), ends old lifetime; null API failure leaves old allocation live; resource trap has no return | F |
| `reallocarray` | same heap premise | detect a×b overflow (null/ENOMEM, old p intact); otherwise realloc(p,a×b) | F |
| `free` | p=null or `H(p)` | null no-op; otherwise empties bounds for every alias; no caller payload bytes/capabilities changed | F |

Zero-size allocation grants no right to dereference any byte. A
zero-size realloc is not a proof that p remains live: callers must not
reuse old aliases. The positive-size theorem must split failure and
success, not assume realloc always extends p in place. Native
`finish_reallocate` allocates then frees even on shrink. Probe:
[libc-heap.c](../tests/c/prog/libc-heap.c), and
[axiom-address.c](../tests/c/prog/axiom-address.c) for resource failures.
Sources: `malloc/reallocarray.c`, `filc_runtime.c` `finish_reallocate`,
`object_for_deallocate`, `free_impl`, and stdfil.h's GC allocation API.

## 3. Output and streams (9, plus puts)

Format contracts require a readable narrow/wide NUL-terminated format,
valid conversion syntax, all promoted arguments including positional
arguments and `*` widths/precisions, readable selected `%s`/`%ls` ranges,
and aligned writable selected `%n` cells of the length-modified type.
A finite precision bounds string reads as the API specifies; do not
require a NUL past that bound. `%p` does not read its pointee. Output
buffer and input format/string ranges must not overlap where prohibited.
Locale is reachable read state, errno and stream internals are writable
state. Stream operations may allocate/free internal buffers. A caller
buffer installed with setvbuf must remain live through close/flush.

| Name | Precondition beyond the format contract | Guarantee / footprint | Violated checks |
| --- | --- | --- | --- |
| `puts` | `S(s)`, live byte/unoriented stdout | writes s without NUL then newline; nonnegative or EOF; may orient/update stdout, buffer, errno | R,W |
| `fputs` | `S(s)`, live byte/unoriented stream | writes s without NUL or added newline; nonnegative or EOF | R,W |
| `printf` | live byte/unoriented stdout | formatted bytes and selected `%n` stores; byte count or negative on error | R,W,V |
| `fprintf` | live byte/unoriented stream | same, on supplied stream | R,W,V |
| `sprintf` | `W(d,L+1)` for full rendered byte length L, representable return count | writes output and terminating NUL, returns L; selected `%n` stores; never a bounded-output API | R,W,V |
| `wprintf` | live wide/unoriented stdout, wide format contract | wide output and selected `%n`; wide-character count or negative | R,W,V |
| `error` | narrow format contract; live stderr, program-name string and optional error-print callback | diagnostic, error counter and stream state; status=0 returns, nonzero follows exit contract | R,W,V,C |
| `fclose` | exclusively live owned stream (not already closed) | flushes then consumes stream and libc-owned buffers even on error; does not free a caller's setvbuf buffer; zero or EOF | R,W,F |
| `ferror` | live stream | reads error indicator; zero or nonzero, no clearing | R |
| `__fpending` | live stream | count currently pending output (wide units for a wide stream); not a flush | R |

Probe: [libc-output.c](../tests/c/prog/libc-output.c) covers hi.c's exact
`puts("hello")`, `%n`, destination NUL, stream state, `/dev/full`, and
unterminated puts; [libc-wide.c](../tests/c/prog/libc-wide.c) exercises
wprintf on an initially unoriented stdout. An I/O error may happen at
flush/exit, not the original buffered call. Sources: `libio/ioputs.c`,
`iofputs.c`, `iofclose.c`, `ferror.c`, `__fpending.c`,
`stdio-common/vfprintf-internal.c`, `vsprintf.c`, `misc/error.c`.

## 4. Argument parsing (3) and all-object fcntl

| Name | Precondition | Guarantee / footprint | Violated checks |
| --- | --- | --- | --- |
| `getopt_long` | nonnegative argc; readable/writable argv pointer array of argc+1 with null sentinel; `S(argv[i])`; `S(optstring)`; readable sentinel-terminated option records and names; each flag and nonnull longindex writable int; initialized/reset getopt state | returns option value, −1, '?' or ':'; updates getopt state, optional index/flag and **may permute argv cells**; optarg aliases an argument or null | R,W |
| `optarg` | initialized getopt state | readable/writable pointer cell; returned string only borrowed from current argv, no allocation or ownership transfer | R,W on access |
| `optind` | initialized/reset parsing state; index consistent with argv | readable/writable int; denotes next argument after parser mutation, not a constant | R,W on access |
| `fcntl` (not a final import) | command appropriate optional promoted int or pointer; for pointed structures correct typed readable/writable fields, including capability transfer; descriptor integer may be invalid | command-specific fd state/result; −1/errno on errors such as EBADF; never reads an absent optional argument for F_GETFD | R,W,V |

Probe: [libc-options.c](../tests/c/prog/libc-options.c): permutation,
borrowed optarg, null longindex, unknown option and F_GETFD/F_SETFD.
This probes only those fcntl commands; record-lock/other structure
commands need their own contract instance before use in a proof.
Sources: `posix/getopt.c`, `getopt1.c`, Linux fcntl wrappers. argv
permutation is within a live pointer array, so it satisfies kept only
when stored capabilities, not just raw bytes, follow the permutation.

## 5. Locale and characters (12)

Locale transitions can update TLS/table pointers, allocate caches and
invalidate **borrowed results** of earlier locale queries; callers must
copy strings they need beyond that validity window. Neither a successful
setlocale nor the environment is restricted to C/ASCII by the contract.

| Name | Precondition | Guarantee / footprint | Violated checks |
| --- | --- | --- | --- |
| `setlocale` | valid category, locale=null query or `S(locale)` | borrowed NUL string naming resulting locale or null refusal; changes locale state only on success | R |
| `nl_langinfo` | supported string-valued nl_item in current locale (Hello uses CODESET) | borrowed readable string for that item, not caller-owned; GNU internal non-string items need a different result contract | — |
| `__ctype_b_loc` | initialized locale/TLS | readable pointer cell to unsigned-short table valid at indices −128 through 255; no out-of-range indexing; negative compatibility entries do not extend C's isalpha domain | — |
| `__ctype_get_mb_cur_max` | initialized locale | current positive maximum multibyte character length; may change with locale | — |
| `mbrtowc` | s=null reset or `R(s,n)`; output null or writable wchar_t; ps=null internal state or writable valid mbstate_t; state initially zero or previous valid continuation for this locale | 0 for NUL, bytes consumed, −2 incomplete, −1/EILSEQ invalid; output only when a character completes, state can change on partial input; after invalid input reinitialize state before reuse | R,W |
| `mbrtoc32` | analogous, writable char32_t output | analogous conversion; at this pin forwards to mbrtowc, whose wchar_t is UTF-32; a portable contract may additionally admit standard −3 pending-output results | R,W |
| `mbsinit` | ps=null or readable valid mbstate_t | nonzero for null/initial state, zero otherwise; no mutation | R |
| `iswalnum` | WEOF or valid wint_t wide character | nonzero iff alphanumeric in current locale; WEOF false | — |
| `iswprint` | same domain | nonzero iff printable; WEOF false | — |
| `iswspace` | same domain | nonzero iff space; WEOF false | — |
| `iswcntrl` | same domain | nonzero iff control; WEOF false | — |
| `wcwidth` | valid wchar_t character in current locale | column count, 0 for NUL, −1 for nonprintable; not the encoded byte length | — |

Probe: [libc-locale.c](../tests/c/prog/libc-locale.c). It checks negative
ctype indices and 255, refusal, writable conversion outputs/state,
zero-input incomplete versus NUL, invalid encoding and null resets. It
also checks exact stable query/refusal name pointers, canonical C storage
after freeing a separate POSIX input, empty selection under an explicitly
C environment and a borrowed-name setter input.
Sources: `locale/setlocale.c`, `nl_langinfo.c`, `ctype/ctype-info.c`
(table offset 128), `wcsmbs/mbrtowc.c`, `mbrtoc32.c`, `mbsinit.c`,
and `wctype/`. Returned locale data is not promised writable or immortal.

[Locale.v](../rocq/theories/Locale.v) gives `setlocale` an additive trusted
Rocq contract with exact W/P-to-P ABI and a nonnull current-name invariant.
Null queries preserve exact pointers/capabilities, memory, runtime and
world, with no writes/releases/requests. Setters distinguish null refusal,
nonnull success and witnessed runtime resource ending. Refusal retains
logical names, codec and borrow epoch, but may change internal represented
state; a terminal resource ending has no such rollback guarantee.
The unchanged-memory refusal witness proves conservative specification
inhabitation, not native refusal or native progress.

Current names, persistent internal readable sources, writable roots and
exclusive release identities are separate. Every future world-held
capability must be delegated, including a name not returned until a later
query. The internal pool admits canonical built-in names without deriving
authority from unrelated caller objects; writable access does not grant
exclusive release ownership. Borrow validity is logical and epoch-scoped,
without rewriting Obj capabilities to Ro. Same-epoch pointer, text and
codec preservation does not yet cover other locale API borrows such as
`nl_langinfo` tables.

Initialized coherent serialized locale/environment/TLS representation,
Iris separation, safepoint stability and native coverage remain independent
obligations. The contract describes ready logical segment endpoints, not
every internal native cutpoint: ALL commits categories sequentially, and
`setname` can free before installing a replacement. No native termination,
universal satisfaction or new runtime axiom is claimed.

## 6. Conversion descriptors (3)

| Name | Precondition | Guarantee / footprint | Violated checks |
| --- | --- | --- | --- |
| `iconv_open` | `S(tocode), S(fromcode)` | fresh owned live conversion descriptor, or `(iconv_t)-1`/errno; unsupported name is EINVAL; descriptor reaches allocated conversion state/modules | R |
| `iconv` | successfully opened, not closed descriptor; ordinary case: typed RW inbuf/inbytesleft/outbuf/outbytesleft cells, `R(*inbuf,*inbytesleft)`, `W(*outbuf,*outbytesleft)`, nonoverlap | converts prefix; updates cursor **capabilities** and counts by consumed/written bytes, changes descriptor state; appends no NUL; error may follow partial success; E2BIG no room, EILSEQ bad sequence, EINVAL incomplete sequence | R,W |
| `iconv_close` | live successfully opened descriptor, exclusive release right | closes/frees descriptor and reachable owned state; returns status; aliases are no longer usable | R,W,F |

For iconv reset, inbuf=null or *inbuf=null: input count/range is not
required. With an output cursor, require its writable cells/range to
flush shift bytes; with outbuf=null or *outbuf=null, reset without
emitting bytes. No promise that a reset flush always fits or writes
zero bytes in a stateful encoding. Invalid handles do not get the
ordinary EINVAL-input guarantee. Probe:
[libc-iconv.c](../tests/c/prog/libc-iconv.c) checks partial conversion,
all four cells, two-byte output, sentinels, unsupported encoding,
EILSEQ/EINVAL and null reset. Sources: `iconv/iconv*.c`, `iconv/gconv*.c`.

## 7. Process endings/failures (4)

| Name | Precondition | Guarantee / footprint | Violated checks |
| --- | --- | --- | --- |
| `exit` | all retained exit handlers/arguments and live streams satisfy their contracts | invokes pending handlers in reverse registration order then stream cleanup; terminates with low exit-status byte; callback/cleanup prefixes are observable | C plus callback/stream traps |
| `_exit` | integer status | terminates with low status byte; no atexit handlers or stdio flush | — |
| `abort` | none | deliberate abnormal termination; **not** a capability panic; this pin's zerror emits `filc user error: abort(3) called.` then SIGTRAP | — |
| `__assert_fail` | readable assertion/file/function strings (function may be null as supported by glibc), line integer; usable stderr | diagnostic then abort; no normal return | R,W |

Probe: [libc-exit.c](../tests/c/prog/libc-exit.c) distinguishes exit,
_exit, abort and assert. A SIGTRAP alone is **not** a panic classifier:
the probe checks user-error versus safety-error text. Source:
`stdlib/exit.c`, `abort.c` (zerror), `assert/assert.c`,
`sysdeps/unix/sysv/linux/_exit.c`. UB, unreachable, and a hypothetical
stack-canary failure are not justified by these termination contracts.

## 8. Startup and callbacks (3)

| Name | Precondition | Guarantee / footprint | Violated checks |
| --- | --- | --- | --- |
| `__libc_start_main` | native launcher ABI; well-formed argc/argv/environment, valid init/main/finalization functions and loader state | establishes libc/TLS, initial program-name and stream roots; Fil-C entry wrapper supplies capabilities for argv/environment; runs main, then exit on its result | C plus main/init/exit traps |
| `__cxa_atexit` | callable `void(void*)` target and valid opaque DSO tag; argument may be null, otherwise **retain its capability and required lifetime until invocation**, not merely registration | registers function/argument/tag in reachable exit state; 0 success, nonzero failure; may allocate; registration does not itself read the argument's payload or invoke callback | C on later invocation |
| `__cxa_finalize` | null for all or matching DSO tag; every selected pending callback meets its call contract | invokes each matching pending handler once in reverse registration order, marks consumed; effects are composition of callback contracts, possibly nonreturning | C plus callbacks |

`atexit(void(void))` is a source-level adapter to __cxa_atexit; do not
require the user's no-argument handler to have a void-pointer signature.
Probe: [libc-exit.c](../tests/c/prog/libc-exit.c) checks real registration,
argument access, a freed retained argument, DSO selection and double-finalization; entry is exercised
through the **real launcher**, not by recursively calling start_main.
Sources: `stdlib/cxa_atexit.c`, `cxa_finalize.c`, `atexit.c`,
`csu/libc-start.c`, runtime startup wrapper. User callback safety remains
a caller obligation; libc cannot promise that an arbitrary handler
never panics.

## 9. Exposed state (5)

| Name | Precondition | Guarantee / footprint | Violated checks |
| --- | --- | --- | --- |
| `stdout` | initialized process; not closed/replaced without updating ownership | readable/writable pointer cell to live stream and reachable buffering state; cell authority is separate from the mutable pointee's authority | R,W on use |
| `stderr` | same | readable/writable pointer cell to independent live diagnostic stream root; no promise of successful output | R,W on use |
| `__errno_location` | initialized live thread | aligned writable int cell, stable for that thread's lifetime, aliases errno; changes on API errors, need not be cleared on success | — |
| `program_invocation_name` | initialized entry; caller preserves a valid borrowed string if replacing cell | readable/writable pointer cell to borrowed NUL string derived from argv[0], or empty fallback if absent; no independent allocation/ownership promise | R,W on access |
| `program_invocation_short_name` | same | borrowed basename pointer, may alias inside full name's object | R,W on access |

Probe: [libc-entry.c](../tests/c/prog/libc-entry.c), plus stream/error
probes. It traverses argc+1 and environment sentinel arrays, reads their
strings using actual capabilities, checks program-name aliases, reversibly
replaces both name pointers (including an empty suffix borrowed from argv),
swaps and restores the two stream pointer cells, and writes errno.
Volatile cell accesses keep those writes observable in optimized builds.
Sources: `csu/`, `misc/init-misc.c`, `csu/errno-loc.c`,
`libio/` initial streams. Tests do not exhaust all legal entry vectors;
the entry contract includes empty argument strings and an empty
environment, with arbitrary lengths/content within ABI and allocation
bounds, not just these sample command lines. The selected native
`filc_start_program.c` boundary asserts `argc >= 1`, so an empty **argv
vector** is not a successful entry at this pin. Its `argc + 1` is an
int expression before checked size multiplication; constructing that
array additionally requires `argc < INT_MAX`. `Startup.v` separates
the readable entry facts from this copying-arithmetic obligation.
Its `exposed_pointer_cell` and `libc_globals_bound` distinguish actual
cell identities, access and decoded values from pointee validity;
`startup_frame_libc_globals` preserves them through successful copying.
`copied_startup_main` supplies the defined two-parameter main's actual
frame at the resulting ready runtime state. The entry projection does
not prove native launcher adequacy, opaque FILE/TLS validity, ownership
of borrowed name strings, or equality with the launcher's copied argv[0].

## Native evidence and remaining work

All nine `libc-*.c` programs are ordinary `tests/c/prog` fixtures with
hand-derived `.expected` answers. Existing globs include them in plain,
optimized, GC-stress and alternative-check modes; no new fleet step or
runtime dependency is needed. `libc-probe.h` isolates violations in a
child and requires SIGTRAP **and** a Fil-C safety diagnostic, so a raw
crash/user abort cannot pass a negative capability test. `-fno-builtin`
keeps reference libc calls rather than constant-folding their answers.

A temporary wrong-result implementation of mempcpy copied the right
bytes but returned d instead of d+n. Both native builds agreed, yet
progtest rejected it against `.expected` (`copy returns end and preserves
neighbours: no`, exit 1). The mutant is not retained. This checks that
agreement alone cannot bless a contract with the wrong result pointer.

```sh
export FILCC=/tmp/filcc/bin/clang SWIPL=/tmp/swipl/bin/swipl
python3 nanofil/tests/watch.py --label libc-contracts -- \
  nanofil/tests/progtest.sh nanofil/tests/c/prog/libc-*.c
NANOFIL_OPT=-O RUN_ENV='env FUGC_SCRIBBLE=1 FUGC_VERIFY=1' \
  python3 nanofil/tests/watch.py --label libc-contracts-optimized-gc -- \
  nanofil/tests/progtest.sh nanofil/tests/c/prog/libc-*.c
```

Probe coverage is **per contract instance**, not exhaustive coverage of
every encoding, format, getopt table or fcntl command. In particular
resource refusal is not forced for each libc-internal allocation;
invalid opaque handles, mismatched C types of equal ABI width and all
locale cache invalidations are not a promised trap API. The model must
state the contracts, expose their state roots and trace events, compose
callbacks and linking, then prove every call site's premises for every
well-formed entry. These tests neither discharge those obligations nor
make Hello `never_panics`.
