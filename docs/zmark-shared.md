# zmark_shared: pointers inside shared mappings

A staging-only prototype of an opt-in Fil-C rule. It lets processes that share
a mapping (PostgreSQL's main segment, nginx's slab pool) store pointers into
that mapping and read each other's pointers. Background is in the report
["Shared-memory servers on Fil-C"](https://ampcode.com/artifacts/shared-memory-servers-on-fil-c-postgresql-nginx-apache-7766ec05-1e1a-4ea2-a028-3a5199472d5a),
approach B.

- Runtime: `patches/fil-c/runtime-zmark-shared.patch` (libpizlo, `stdfil.h`)
- Pass: `patches/fil-c/filpizlonator-zmark-shared.patch` (FilPizlonator)
- Both apply only when `sources.variant == "staging"` (`runtime/libpizlo.nix`,
  `compiler/filc0.nix`). The release toolchain is unchanged.
- Regressions: `tests/zmark-shared.nix` (`checks.staging-zmark-shared`)
- Opt-in at compile time: code that loads or stores pointers in a marked
  mapping is compiled with `-fzmark-shared`. Everything else, including the
  whole staging world, is compiled as before (see "Opt-in: -fzmark-shared").

## The problem

`mmap(MAP_SHARED)` and `shmat` allocate an ordinary Fil-C object and map
the shared pages over its payload. Only the payload is shared. The object
header and its aux array, which holds the capabilities of pointers stored in
the object, are private to each process. After fork, a pointer stored into the
mapping by one process has its capability only in that process's aux, and the
other processes read the address without a capability, or with a stale one,
and trap. This is an availability problem, not a safety hole.

## The rule

`void zmark_shared(void *p)` marks the mapping that starts at `p` with
`FILC_OBJECT_FLAG_SHARED` (flag bit 64, previously free). Call it right after
`mmap` or `shmat` and before forking. Call this marked object O. From then on,
O's bytes hold addresses only:

| Operation on O | Behavior |
| --- | --- |
| Pointer load: plain, atomic, volatile, aggregate, the old value of a CAS or exchange | (address, O's capability), or no capability if the address is null |
| Pointer store: plain, atomic, CAS, exchange | panics unless the value is null or has O's capability. Only the address word is written |
| memcpy/memmove out of O | each whole copied word gets the capability a load would give it. Partially copied words get none |
| memcpy/memmove into O | bytes only; nothing is checked (see below) |
| zcall argument buffers read from O | same as loads |
| `va_arg` from a va_list kept in O | pointers get no capability (fails safe; see F2) |
| aux creation (`ensure_aux` and anything that calls it) | panics. A marked object never has an aux |
| munmap, shmdt of the whole mapping | frees O as today. Capabilities derived from O refer to a freed object and trap |
| Partial munmap, mremap | as today. The pages leave or are replaced. A moving mremap returns a new, unmarked object |

`zmark_shared` panics unless `p` is the start of a live, non-special mmap
object with no aux. It also panics unless `/proc/self/maps` shows the whole
range as a shared (`s`) mapping. That second check is a usage guard, not a
safety check. Marking an already marked object does nothing. The flag is
never cleared.

## Invariants

1. **A marked object never has an aux.** `zmark_shared` sets the flag with a
   CAS on the aux word only while its pointer part is null. Aux creation
   (`ensure_aux_ptr_slow_size_specialized`) CASes the same word and panics
   when the flag is set. The two exclude each other. So "flag set" implies
   "aux pointer null", and `filc_aux_is_shared` tests both.
2. **No shared byte is ever read as runtime metadata.** O's header sits
   before its page-aligned payload, on a private page. The shared pages cover
   exactly `[lower, upper)`. Capabilities, boxes and aux arrays all live in
   the private GC heap. With no aux there are no boxes, and no lower or box is
   ever read through O.
3. **A capability loaded from O is O or nothing.** Every load path takes the
   capability from the loader's own header for O, never from the bytes. That
   includes the inline loads, the atomic outlines, both CAS functions,
   exchange, every runtime memmove and copy, and zcall demotion.
4. **Opt-in.** Only `zmark_shared` sets bit 64. An object without it,
   including every unmarked shared mapping, takes exactly the previous paths.

## Why a loaded pointer cannot exceed the segment's authority

Assume the other writers are hostile: native processes, Fil-C processes that
did not mark, or stray integer stores. Whatever they write, the loading
process reads only an address. It pairs that address with O, the object it
already held a capability for in order to perform the load. Every later access
through the result is bounds-checked against O's lower and upper, and is
refused once O is freed. So the worst a hostile writer can do is choose an
address. Addresses inside O give access the reader already had. Addresses
outside O trap on access. Such a writer cannot make the reader use a
capability that it did not already hold.

Neither the store-side check nor a range check on loads contributes to
safety. The first prototype gave no capability to addresses outside
`[lower, upper]`. The Oracle showed that this was unnecessary and broke tagged
pointers (nginx's `ngx_slab_page_t.prev`), so out-of-range addresses now
keep O's capability and trap only if dereferenced (F1). The typed-store
check stays as a diagnostic: a private or function pointer stored into O
could never be used again, even by the process that stored it, since it
would read back with O's capability. Panicking at the store points at the
bug.

## Fork

The flag lives in the private header and is copied by fork, like the rest of
the header. Mark before forking, and every child has a marked O. If only
some processes mark, which needs marking after fork, each process follows
its own header. A process that marked trusts no bytes. A process that did not
mark keeps today's semantics, where its aux gives at most the capability
that the process itself stored, so this case opens no hole either. Marking
after fork fails if this process already stored a pointer into O, because O
then has an aux.

## GC

O has no aux, so the collector traces nothing out of it and its payload is
never a root. A capability loaded from O is O itself, and O is live because
the loader holds it. Stores into O record nothing for the collector, so they
need no store barrier. Copies out of O into a heap object barrier O before
they write the destination's lowers, and again after each pollcheck in long
copies. munmap frees O as usual. A capability that a process derived from O
before the munmap then refers to a freed object and traps.

## What is refused, and why

- Storing a private heap pointer, a function pointer, or a pointer to another
  mapping into O panics. No other process could use it, and the storing
  process could not use it after reading it back either. This check applies
  to typed pointer stores, CAS and exchange only. Copies into O are not
  checked: Fil-C keeps a word's capability across integer stores, so integer
  data routinely carries a stale capability (PostgreSQL's heap tuples reuse
  palloc chunks whose first word was a freelist link), and a copy-in check
  panicked on the first `PageAddItemExtended`. Readers never trust the bytes,
  so the check was a diagnostic only.
- Marking a mapping that already holds a stored pointer panics, because its
  aux would hold capabilities that the rule would have to drop or trust.
- Marking anything that is not the start of a live mmap/shmat object panics:
  malloc memory, an interior pointer, or a private mapping.
- Cross-segment pointers, such as a pointer stored in a DSM segment that
  points into PostgreSQL's main segment, are refused. A wider rule that looks
  up the capability from the address among all shared mappings would allow
  them, but it relaxes provenance. Not done.

## Opt-in: -fzmark-shared

The compiler half is opt-in per function, so ordinary code pays nothing:

- `clang -fzmark-shared` gives every function it emits the string attribute
  `filc-zmark-shared`. FilPizlonator emits the paths in "Compiler cost" only in
  functions with the attribute (`-mllvm -filc-zmark-shared` forces them
  everywhere). It strips the attribute from the lowered function. Helpers the
  pass makes itself never get the paths.
- A function without the attribute is lowered exactly as before the zmark
  patch: it never tests the shared flag and calls the ordinary ensure-aux.
- The pass runs in the compile step (Fil-C's PipelineStart callback, after its
  own inliner), so the choice is fixed per function before LTO. An inlined
  callee is lowered as part of its caller and follows the caller's flag.
- The runtime half is always present in the staging runtime. `zmark_shared()`
  stays the per-mapping runtime opt-in. There is no environment toggle.

**Mixed programs are sound.** Code compiled without the flag that touches a
marked object fails safe:

- Its inline pointer loads find a null aux and give no capability.
- Its inline pointer stores and capability-carrying inline copies call the
  ordinary ensure-aux, which panics on a marked object. The message says that
  such code must be compiled with `-fzmark-shared`. This includes small
  inlined copies of plain data whose source words carry stale capabilities
  (the heap-tuple pattern), so every file that loads, stores or copies into a
  marked mapping needs the flag (Oracle D1).
- Runtime entry points it calls (out-of-line memmove, atomic and CAS outlines,
  zcall) follow the rule whatever the caller was compiled with: O's capability
  or none.

None of these can produce a capability other than O's, because the runtime
invariants (a marked object never has an aux; capabilities come only from the
loader's header for O) do not depend on how any caller was compiled.

## Compiler cost

These paths exist only in functions compiled with `-fzmark-shared`.

The aux word that the inline paths already load holds the flags.

- Pointer loads from an object with an aux are unchanged.
- Pointer loads from an object with no aux used to produce (address, null)
  with no memory access. They now load the header's aux word (monotonic),
  test the shared bit, and select O's lower or null with no call. The address
  is loaded once, and the null test uses that same address, so a racing
  writer cannot make a load return (address, no capability) (Oracle N1).
- Pointer stores test the aux base once more after EnsureAuxPtr. It is null
  only for a marked object, and then the store goes to a cold call to the
  atomic outline, which performs the store-side check.
- Small inline memmoves with a heap side test that side's aux and flags
  first, and send marked objects to the runtime copy before any byte moves.

Measurements are below.

## Oracle review

A reviewing subagent read the change (fil-c fork commit 5f517b9ef336, the
first version) against the runtime, the pass and the GC. It covered the
inline load path and cached `AuxBaseVar`s, atomics and boxes, every memmove
and copy path, munmap/mremap/shmdt, fork, metadata, GC, and opt-in. Verdict:
**the rule is sound, and so is this implementation as far as the review
could check.** It found no path where a load from O yields a capability other
than O's or none. Findings and resolutions:

| # | Finding | Kind | Resolution |
| --- | --- | --- | --- |
| F1 | The range check on loads dropped the capability from valid out-of-range pointers (tagged pointers, `p - k` bases). The check is not needed for safety | fail-safe but wrong | Removed. Any non-null address gets O's capability. A test stores a pointer tagged with bit 60 and uses it after masking the tag |
| F2 | `va_arg` and zcall demotion read a source in O with no aux, so pointers lost their capability | fail-safe but wrong | zcall demotion now derives O's capability. A va_list stored in shared memory is documented as unsupported (pointers come back with no capability) |
| F3 | Copy-in checks only aligned, whole, in-phase pointer words, so the documented "panics" overstated it. Safety does not depend on the check | fail-safe but wrong | First kept as a diagnostic. Removed after PostgreSQL showed it panics on ordinary integer data with stale capabilities: copies into O are bytes only (fork 237c2bcbe22a) |
| F4 | The new flag tests read the aux word with a plain load while other threads CAS it | quality | The flag loads are now monotonic |
| F5 | Pointer loads from objects without an aux now pay a header load and a branch | cost | The shared load is an inline select, not a call. Measured below |
| F6 | The `/proc/self/maps` check races with MAP_FIXED/mremap, and requiring "no aux" rejects aux arrays that hold only nulls | quality | Commented as a usage guard, not a safety check. The no-aux requirement stays |

The Oracle did not run reproducers in the first review (its build waited on
the Nix daemon). In a second review of the fixes (fork 14a1f5363596) it ran
its own reproducers at -O0 and -O2. It confirmed F1 to F4 resolved, and the
CFG and phi changes correct, and found one new issue:

| # | Finding | Kind | Resolution |
| --- | --- | --- | --- |
| N1 | The inline load tested a second load of the address for null, while the program used the first. A writer racing NULL to a valid address made 4647 of 50M loads return (address, no capability) | fail-safe but wrong (availability) | The address is loaded once per edge, and the select uses that value (fork 49045c3fd094). The `race` case measures it: 0 bad loads at -O0 and -O2, against 398019 and 80 before |

A third review of 49045c3fd094 found the N1 fix sound and the CFG and phi
changes correct. Its own race run gave 0 bad loads in 50M at -O0 and -O2.
One optional quality note remains:

| # | Finding | Kind | Resolution |
| --- | --- | --- | --- |
| Q1 | The single address load is plain. Under LLVM rules, a racing plain load is `undef`, and two uses of it could in theory disagree. The only outcomes are still (null, O) or (address, none) | quality, no safety impact | Not applied. `freeze` on the loaded address would remove it at no runtime cost; current codegen uses one register |

A fourth review covered the removal of the copy-in check (fork
237c2bcbe22a). It found the change sound: every copy into O still copies
the bytes, none creates or reads an aux for O, the copy-out direction is
unchanged, and a race with `zmark_shared` still panics in `ensure_aux`.

| # | Finding | Kind | Resolution |
| --- | --- | --- | --- |
| Q2 | If an LLVM pass rewrote a memcpy into O as pointer-typed loads and stores, a stale capability on integer data could hit the typed-store check | quality, unverified, fail-safe | Not seen in PostgreSQL. The store-side decision below would cover it |

A fifth review covered the compile-time opt-in (fork 2257aff0d3e1,
12d3effc7903). Verdict: sound. Each function gets either the reviewed zmark
lowering or the original one, and each is sound against the patched runtime,
so mixing them on one marked object (other files, libraries, nanofil code,
inlining before the pass, LTO) cannot give a load any capability other than
O's or none, nor read shared bytes as metadata. `AuxBaseVar` is per function,
so nothing is cached across the boundary. Pass-generated helpers touch no heap
pointers in O, so keeping them unflagged is correct. Functions clang emits
without the attribute (thunks, outlined clones) are lowered unflagged, which
costs availability only. Its own mixed-build reproducers at -O0 and -O2 matched.

| # | Finding | Kind | Resolution |
| --- | --- | --- | --- |
| D1 | An unflagged file's small inlined memcpy of plain data into O panics when a source word carries a stale capability, though the file stores no pointer | availability, docs | stdfil.h and the panic message now say that stores and copies need the flag (fork ec3c00ea4da2) |

The Oracle also noted that the store-side check is a diagnostic: readers never trust
the bytes, so writing the address only, without the cold outline call, would
be equally sound and much smaller. That is an owner decision; see
Measurements.

## Regressions

`checks.staging-zmark-shared` runs `tests/zmark-shared/run.sh` at -O0 and
-O2, plus the hash-table stress test. `zmark.c` and `hashtable.c` are compiled
with `-fzmark-shared`; `unflagged.c` is compiled without it and linked in. Case by case:

| Case | What it shows | Patched (-O0, -O2) | Stock staging |
| --- | --- | --- | --- |
| postfork | shm.c: the child reads a pointer the parent stored after fork | pass | traps (null object) |
| postfork-nomark | an unmarked segment still traps as today | pass | pass |
| unmarked | an unmarked mapping keeps private capabilities, as today | pass | pass |
| store-private, store-func, store-other, store-atomic-private, cas-private | storing a malloc pointer, a function pointer, or a pointer into another mapping (plain, atomic, CAS) panics | pass | no panic |
| atomics | 4 processes push and pop a lock-free stack with CAS and exchange | pass | fails |
| memmove | memmove out of O gives O's capability per word | pass | traps |
| race | a writer flips a slot between NULL and a valid address under plain loads (N1) | pass, 0 bad loads | fails |
| memmove-in-small, memmove-in-big, memmove-in-deref | copying a private pointer, and integer data with a stale capability, into O succeeds; both read back with O's capability, and dereferencing the private address traps | pass | fails |
| munmap-deref, munmap-load | after munmap, using an old pointer or loading one traps | pass | pass |
| mark-aux, mark-private, mark-malloc, mark-interior | zmark_shared refuses an object with aux, a private mapping, malloc memory, an interior pointer | pass | no panic (macro stub) |
| hostile, hostile-private, hostile-end, hostile-call | raw byte writes of arbitrary addresses load with O's capability only, and using them outside O or as a function traps | pass | fails |
| native | a native (gcc) process writes arbitrary words into the segment; loads get O's capability or none | pass | fails |
| hashtable 8 20000 | 8 processes insert and delete in a chained hash table under a lock | pass | traps (null object) |
| unflagged-load, unflagged-store | a file compiled without `-fzmark-shared`, linked into the same program: its loads from O get no capability, its stores panic naming the flag, and flagged code keeps working on the same O | pass | n/a (new flag) |

The stock column uses the staging compiler without the patch and
`-Dzmark_shared(p)=((void)(p))`.

## PostgreSQL

PostgreSQL 18.6, built outside Nix with `filcc-staging` from this branch
(`patches/postgresql-filc-zmark-shared.patch`, against pristine 18.6) and
`CFLAGS="-O2 -g -Wno-int-conversion -fzmark-shared"`, run with
`huge_pages=off` and the default `io_method=worker`. All of PostgreSQL is
compiled with the flag, since most backend files touch the main segment.

The zmark-specific changes are small:

- `zmark_shared(ptr)` after the main segment's mmap in `CreateAnonymousSegment`
  (sysv_shmem.c).
- shm_mq keeps its sender and receiver as proc numbers, not `PGPROC *`
  (a DSM segment is a separate mapping, so a pointer from it into the main
  segment would be a cross-segment pointer).
- parallel.c passes the leader as `parallel_leader_proc_number` instead of
  `PGPROC *` in the parallel DSM, and the leader's SERIALIZABLEXACT as an
  offset from `ProcGlobal` instead of a pointer, for the same reason.
- AIO's issuer-private fields (`resowner`, `resowner_node`, `report_return`)
  move from the shared `PgAioHandle` to a backend-private array indexed by
  handle id. PostgreSQL 18 stores these process-local pointers in shared
  memory and only the issuing backend uses them. Under any addresses-only
  rule the owner would read them back with the segment's capability, and the
  store-side check refused them at the first `ResourceOwnerRememberAioHandle`.
- The iovecs of an IO on local (temporary-table) buffers move to
  backend-private memory. They point at private buffers, and only the issuing
  backend executes such an IO (`buffers_to_iovec` hit the store check).

The rest is ordinary single-process Fil-C porting, shared with the release
toolchain port in thread T-01a1ac20 (non-asm spinlocks and atomics, Datum as
`char *`, xlogprefetcher's `uintptr_t` private pointer, `sort_template.h`'s
byte swap), plus an 8-byte alignment of the expanded-object TOAST pointers in
`ExpandedObjectHeader`. Fil-C keeps a capability only on whole, aligned words,
so `DatumGetEOHP` lost the pointer.

Two staging toolchain gaps unrelated to zmark were worked around, not fixed:
glibc's `sync_file_range` reaches raw `syscall` inline asm (`initdb -N`,
`*_flush_after=0`), and nixpkgs' make defaults `SHELL` to a bare `sh`, which
pg_regress cannot exec (`SHELL=/bin/sh`).

Results with the main segment marked (staging toolchain from this branch):

| Run | Result |
| --- | --- |
| `initdb` | passes |
| `pgbench -i -s 10`, including parallel index builds | passes |
| `pgbench -c 8 -j 8 -T 60`, `io_method=worker` | 309207 transactions, 0 failed, 5154 tps, no Fil-C safety errors |
| `make -C src/test/isolation check` | 122 of 122 pass |
| With `-fzmark-shared` (after the opt-in): `pgbench -c 8 -j 8 -T 60` | 309462 transactions, 0 failed, 5158 tps, no Fil-C safety errors |
| With `-fzmark-shared`: isolation | 122 of 122 pass |
| Control: same build, `zmark_shared` call commented out | `initdb` passes (one process); the server's first pointer read across processes traps (`SetLatch` from `pgaio_worker_submit`: "cannot read pointer with null object") |

Each port change above was found by a trap during these runs. None of
them showed a soundness problem in the rule. Three came from the rule's
store side: the AIO resource-owner fields and the local-buffer iovecs
(typed stores of private pointers, refused by design), and the copy-in
check on heap tuples (stale capabilities on integer data). The copy-in check
has been removed (see F3). The typed-store check stays, and PostgreSQL passes
with it.

## Measurements

Ordinary code, Lua 5.4 built with the staging compiler with and without the
pass patch (same pass source as fork 49045c3fd094, same patched runtime),
user-mode instructions on nanofil's `bench/*.lua`:

| Workload | Without | With | Change |
| --- | --- | --- | --- |
| int.lua | 1.2384G | 1.2565G | +1.5% |
| tab.lua | 0.9987G | 1.0268G | +2.8% |
| str.lua | ~3.77G | ~3.85G | ~+2.3% (noisy) |
| `lua` text size | 1.866 MB | 2.096 MB | +12.3% |

Most of the text growth is the cold store-outline call: one call block per
inline pointer store site (1079 in Lua). The instruction growth is the
header load and flag test on pointer loads from objects without an aux.

Pointer ops, measured with `tests/zmark-shared/ptrcost.c` (a 4096-slot pointer
array; each op stores a pointer and loads one, or only loads), -O2, three runs:

| Object | store+load ns/op | load ns/op |
| --- | --- | --- |
| malloc, patched | 2.6 to 4.0 | 1.1 to 1.4 |
| malloc, unpatched | 2.6 to 3.0 | 1.1 to 1.2 |
| MAP_SHARED unmarked, patched | 2.4 to 4.4 | 1.2 to 1.4 |
| MAP_SHARED marked | 9.5 to 10.3 | 2.2 |

Unmarked objects are within run-to-run noise. In a marked object a load costs
about 1 ns more (the header load and select), and a store about 7 ns more,
almost all of it the outline call that performs the store-side diagnostic.

**Owner decision: the store side.** The Oracle confirmed that the store-side
check is not needed for soundness. Replacing the cold outline call with a
single branch (store the capability word only when the aux base is non-null)
would remove the 1079 call blocks from Lua and most of the 7 ns per shared
store. The cost is that storing a private or function pointer into O would
silently become an address-only store, as memcpy into O already does,
instead of panicking. PostgreSQL hit the typed-store panic twice, both in
AIO (resource-owner bookkeeping and local-buffer iovecs). Both were genuine
private pointers and needed a port change either way, since the owner could
not have used them after reading them back. The prototype keeps the panic.

### No zmark code without the flag

A slice of the staging world built from this branch without the flag
(`pkgsFilcStaging.{zlib,openssl,sqlite,curl,lua,bash,coreutils,python3,libxml2}`,
56 store paths and 1500 ELF files in their runtime closure, including glibc and
libc++) was scanned for both zmark markers (`.amp`-local script, not committed):

| Marker | World without the flag | postgres with `-fzmark-shared` |
| --- | --- | --- |
| references to `filc_object_ensure_aux_ptr_or_shared_outline` (store path) | 0 | 2 |
| shared-flag tests (`shr $54` of the header word, then `and $1`; load path) | 0 | 13323 |

The only other files that mention the symbol are libpizlo (which defines it)
and the compiler and JIT (which contain the pass). The compiler is not
deterministic from run to run, so a byte comparison with the pre-zmark pass was
not possible. The Oracle checked flag-off equivalence by reading the diff.

### nanofil

`scripts/nanofil-checks`: all 17 checks pass on this branch, before and after
the rebase onto origin/main (nanofil,
nanofil-bash, -bzip2, -coreutils, -dash, -hello, -jq, -lua, -lz4, -make,
-python, -python-regrtest-plain, -sed, -sqlite, -swipl, -xz, -zlib).

nanofil needs no change for programs that never call `zmark_shared`, since
the runtime is unchanged for unmarked objects. Code that nanofil compiles does
not know the shared flag, so on a marked object it fails safe rather than
following the rule. Its pointer loads find no aux and get no capability, and
its pointer stores reach `ensure_aux`, which panics on a marked object. To
support zmark_shared, nanofil's lowering would need the same three changes as
the pass: the flag test on null-aux loads, `ensure_aux_ptr_or_shared` on
stores, and the shared check before inline memmoves. Not done here.
