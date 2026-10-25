# The interpreter's explicit-free lifetime oracle

`interp.pl` models explicit deallocation so a pass that reuses a memory
check across `free` can be distinguished from the program it transformed.
This is a deterministic, single-threaded subset: no asynchronous handlers,
reclamation, or collector rewriting of capabilities. It is not a proof
that check elimination or moving checks across safepoints is safe.

## Ground truth at staging af81305

The source is the pinned staging revision
[`af813053ecb5`](https://github.com/mbrock/fil-c/commit/af813053ecb5a5ff27292bfede8d3a9e870d4c8e).
Build the small reference tree with
`nix build -o /tmp/filc-ref .#lib.x86_64-linux.filc-staging-ref-src`.
The runtime paths below are relative to `libpas/src/libpas/` there.

| Source | Rule |
| --- | --- |
| `projects/user-glibc-2.44/malloc/malloc.c:3138–3144` in the pinned repository | `__libc_free` immediately delegates to `zgc_free`. This libc file is not part of the small reference tree. |
| `filc_runtime.c:3925–3953` | `free_with_checks` returns immediately for address zero, regardless of the lower. `filc_native_zgc_free` calls it. |
| `filc_runtime.c:3851–3892` | A nonzero pointer must carry an ordinary object, not special, GLOBAL or MMAP, and its address must equal its lower. READONLY is not rejected. |
| `filc_runtime.c:3165–3199` | `free_impl` sets `upper = lower`, then sets FREE with a CAS preserving the aux pointer. An already set FREE flag causes a safety panic. |
| `filc_runtime.c:2828–2835, 2872–2902` | Heap payload size rounds up to 16, including in the header's upper bound. Zero stays zero, but the allocation still has a header and identity. |
| `filc_runtime.c:6237–6249` | Argument snapshots are ordinary readonly heap objects. An empty packet instead returns null; it is not an allocated zero-sized object. |
| `filc_runtime.h:169–187` | GLOBAL and READONLY are different properties. Freed objects retain the information needed by an access racing with free. |
| `fugc.h:155–171, 210–222`; `filc_runtime.c:213–219` | Collection may redirect a stored dead lower to the GLOBAL, READONLY, FREE singleton. The interpreter does not perform this rewrite. |

`gimso_semantics.md`'s capabilities section explicitly requires shared
identity: freeing through one pointer changes the bounds observed by all
other pointers with that capability. Copying bounds into pointer values
would not implement that rule.

## Memory, identity and invalidation

The memory value remains `mem(Bytes, Regions, Next, Aux)`. Bytes and Aux
are assocs; Aux maps an aligned slot address to its stored capability.
Regions contains `region(Base, End, Kind, Life)`:

- `Base` is stable, non-reused identity. Capability lookup uses Base,
  never the live allocation that happens to contain the pointer's address.
- `Kind` is `heap`, `global` or `stack`. Fil-C IR `alloc` and nonempty
  argument snapshots are heap objects; static data is global. `stack`
  describes plain-mode allocations and the named Fil-C locals added by
  [local storage](m5.md), whose exact identities die with their invocation.
- `Life` is `live` or `freed`, independently of whether End equals Base.
  A live zero-sized heap allocation can be freed exactly once.
- Free changes just End and Life, to Base and `freed`. It preserves
  Bytes, Aux, Next, and every other region. No alias list needs updating.

Pointer values remain `ptr(Address, Cap)`. `obj(Base)` and `ro(Base)`
consult shared current bounds. Their rights tags are canonical for each
published object: snapshot initialization uses a private writable pointer
before publishing only its readonly pointer. No supported operation
upgrades readonly authority. Injected memory-using test arguments must
name registered objects and obey this invariant.

Loading a pointer from a live holder checks the holder, not its pointee.
The result can carry a dead capability. Likewise, storing a dead pointer
does not dereference it. An integer store over that slot changes address
bytes but preserves its stored lower; changing those bytes to a new
object's address cannot revive the old capability.

Every ordinary access and explicit check reads current bounds. Since IR
accesses and checks have positive size, a freed object's empty bounds
produce `trap(out_of_bounds)` before permission/alignment checks. A raw
access performs the same oracle check but uses `raw_res/2` to report
`unchecked(out_of_bounds)`: a stale proof is a pass bug, neither UB nor a
newly inserted runtime trap. The validator still rejects a check separated
from its access by a call; deliberately invalid IR can be run to test
the oracle without making that IR compilable.

## The supported external call

Only `call(void, global(free), [arg(p, P)])` is interpreted as libc free,
and only when the module does not define the symbol. A module-defined
function named `free` is called normally, whatever its signature. Data
named `free` produces `trap(not_a_function)`, rather than invoking libc.
This assumes ordinary linking to the pinned libc, without interposition.

| Argument | Outcome |
| --- | --- |
| Known zero address with a supported capability | No effect, normal void return |
| Exact base of a live ordinary heap object, including zero-sized or readonly | Invalidate that object, normal void return |
| Exact base of an already freed heap object | `trap(double_free)` |
| Nonzero address without a capability, global/function object, interior/one-past/wrong-object address | `trap(invalid_free)` |
| Unresolved external capability or unregistered injected object identity | `nanofil_error`, an unsupported execution |

Kind and exact-address validation precede the double-free test. A dead
object's interior pointer therefore gives invalid-free, not double-free.
The trap categories do not promise the runtime's exact diagnostic text,
especially after collection may have changed a stored lower to the free
singleton.

Unsupported call signatures, indirect external function values and other
external calls remain explicit interpreter errors. In particular this
does not add malloc, realloc, mmap or a general libc emulator. An
unresolved symbol's `ptr(0, ext(Name))` is a placeholder, not a known null
pointer: it cannot take free's zero-address shortcut. Executions using
unresolved external address bits, even after `ptoi` erases that provenance,
remain outside the oracle's domain.

## The memory-helper boundary stays intact

The instruction interpreter need not inspect Regions. It uses
`access_res/7` for current access authority and `free_res/4` for
invalidation. Existing `load_res/6`, `pointer_access_load/5`, `store_res/7`,
`access_store/7` and `raw_res/2` retain their interfaces. The low-level
byte/Aux helpers are post-check operations, not independent authority to
access memory. Aux entries remain capability identities, not copied bounds.

Plain allocations retain exact sizes and die on function return. Fil-C
heap bounds now match the runtime's rounding; global layout keeps its
existing eight-byte rounding. The free/invalidation change itself did
not change native rooting or proof adjacency. The later local-storage
pass adds exact-sized stack objects and distinct stack-aux roots; its
invocation cleanup preserves this same current heap state.

## Review and evidence

Oracle reviewed this contract before implementation. Its required
adjustments were adopted: resolve module functions/data before the libc
adapter; reject unresolved external placeholders before null handling;
limit the adapter to its exact signature; keep lifetime independent of
empty bounds; preserve canonical rights; and distinguish an empty argument
snapshot from an allocated zero-sized object. Generic return conversion
was deliberately not reused: return-size validation after a side-effecting
callee requires sequencing beyond this narrow adapter.

`tests/filc/basic.ir` adds alias invalidation through another function,
live holders of dead pointers, integer overwrites, null/forged pointers,
interior/one-past/double frees and rounded/zero allocation boundaries.
`tests/unit.pl` checks their precise outcomes before and after pizlonation,
plus readonly heaps versus globals/functions, symbol resolution, unsupported
calls, stored-lower non-laundering and rejected stale proofs for integer
and pointer loads/stores. Existing plain use-after-return and backward
integer queries remain controls.

Five new unit tests failed before implementation. Afterwards all 67 unit
tests pass and the expanded native fixture compares 37 runs, none
incomparable. Scratch mutations independently leaving a freed object live,
clearing Aux on integer stores, and intercepting a module's own `free`
each fail the tests. These mutations were removed. The full
`nix build .#checks.x86_64-linux.nanofil` gate includes native interoperation,
GC-stress programs and both optimization settings; it passes. GC stress
checks the unchanged native implementation, not a newly modeled collector.

Seven additional scratch native comparisons passed at both optimization
levels: empty/nonempty snapshots, freeing global/function/wrong-object
pointers, and zero addresses carrying global/function capabilities.
`tests/snapshot.sh` reports 1,014 outputs byte-identical to the preceding
compiler; the lifetime work changes the oracle, not emitted assembly.
