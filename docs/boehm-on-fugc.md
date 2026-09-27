# Boehm GC on FUGC

`pkgsFilc.boehmgc` is not the Boehm-Demers-Weiser collector. It is the
libgc API (headers, `libgc`, `libcord`, `libgccpp`, `libgctba`,
`bdw-gc.pc`) implemented on Fil-C's own garbage collector. The code is in
`ports/boehmgc/`, and `ports/overlay.nix` wires it in.

## Why not port Boehm itself

Boehm scans thread stacks, registers and data segments conservatively and
treats any word that looks like a heap address as a pointer. Under Fil-C:

- A pointer stored as an integer loses its capability, so a "pointer" that
  Boehm found by scanning cannot be dereferenced.
- The runtime does not let one thread read another thread's stack.
- Boehm would carve objects out of large mmap'd chunks, so they would get
  the whole chunk's bounds instead of their own. Fil-C's per-object bounds
  and use-after-free checks would be lost. A Boehm "collection" that
  misses a root would reuse live memory.

None of this is needed. Every Fil-C allocation is already collected by
FUGC, which is precise, concurrent and parallel, and `free` is optional. A
Boehm client only needs its API calls to do the right thing on FUGC. djb's
Filian does the same for simple clients
(`data/libgc/subst/gc.c`: `GC_malloc` is `malloc`). This implementation
covers the whole libgc 8.2 ABI, including finalization and weak
references, and it keeps upstream's headers, so clients compile unchanged.

## Mapping

| libgc                                   | FUGC implementation |
|-----------------------------------------|---------------------|
| `GC_malloc`, `_atomic`, `_ignore_off_page`, typed, gcj, kinds | `zgc_alloc` (zeroed, like libgc) |
| `GC_malloc_uncollectable`               | `zgc_alloc`, kept alive by a strong `zexact_ptrtable`. Membership is in a `zweak_map`, so `GC_realloc` keeps the kind |
| `GC_realloc`                            | `zgc_realloc` |
| `GC_free`                               | `zgc_free` (also drops the uncollectable hold and any finalizer). Later accesses trap |
| `GC_base`, `GC_size`                    | `zgetlower`, `zgetupper - zgetlower` |
| `GC_gcollect`                           | `zgc_request_and_wait`, then process the cycle (below) |
| finalizers (all `GC_register_finalizer*` variants) | see below |
| disappearing and long links             | see below |
| `GC_HIDE_POINTER` / `GC_REVEAL_POINTER` | a weak `zexact_ptrtable` (header patch below) |
| `GC_generic_malloc_many`, `GC_malloc_many` | a list of separate objects linked through their first word |
| roots, displacements, exclusions, incremental mode, heap expansion, mark bits, `GC_push_*` | accepted, no-ops |
| `GC_pthread_*`, `GC_dlopen`             | pass-through |
| `GC_register_my_thread` and other thread and stack calls | bookkeeping only. FUGC knows every thread. `GC_get_stack_base` returns `zstack_top()` |

### Finalizers

FUGC's finalizer queues (`zgc_finq`) apply to objects that were allocated
with `zgc_finq_alloc`. libgc lets you attach a finalizer to any existing
object. The bridge:

- Registering a finalizer on `obj` allocates a small sentinel with
  `zgc_finq_alloc`. The sentinel holds `obj` strongly, together with the
  function and its client data. It is stored in a global `zweak_map` under
  the key `obj`.
- The weak map is an ephemeron table: the sentinel is marked only if `obj`
  is live. The sentinel's own reference to `obj` does not keep `obj` alive.
- When `obj` dies, the sentinel is unreachable too. FUGC revives it, which
  also revives `obj`, and queues it. FUGC clears weak references (census)
  before it revives objects. So `zweak`s and links to `obj` are already
  cleared when the finalizer runs, like libgc's short links.
- The library drains the queue into a pending list. It then either runs
  the finalizers (`GC_finalize_on_demand == 0`) or calls
  `GC_finalizer_notifier`, and the client calls `GC_invoke_finalizers`.

Re-registering with `fn == 0` cancels the finalizer and reports the old one
through `ofn`/`ocd`. Registering again from inside a finalizer works, which
is the guardian pattern. `GC_finalize_all` runs every registered finalizer.
`GC_finalized_malloc` (gc_disclaim.h) is built on the same mechanism.

### Disappearing links

`GC_general_register_disappearing_link(link, obj)` records a `zweak` to the
link's containing object and a `zweak` to `obj`. The record goes in a hash
table keyed by the link's address. The library sweeps the table whenever it
sees that a GC cycle has completed. Dead targets get `*link = NULL`. Records
whose link object died are dropped. `GC_move_*` and `GC_unregister_*`
behave as in libgc.

### Hidden pointers

`~(GC_word)p` loses `p`'s capability. `include/gc.h` is patched
(`hide-pointer.patch`) so that under `__FILC__`, `GC_HIDE_POINTER(p)` is
`~zexact_ptrtable_encode(weak_table, p)` and `GC_REVEAL_POINTER(h)`
decodes it. The encoding is still the complemented address, so hidden
values look like libgc's. Revealing a live object's pointer gives back a
usable pointer. The table is weak, so hiding does not keep objects alive,
and the usual "hidden pointer plus disappearing link" weak-reference idiom
works.

FUGC clears weak references before it revives finalizable objects. libgc,
by contrast, keeps a hidden pointer to an unreachable object that has a
finalizer valid until the object is reclaimed. Two things bridge the
difference. When a revived object is queued, the library hides it again.
And if a reveal fails while finalizers exist, the library waits for the
running cycle to finish queueing, drains the queue, and retries.

### Disclaim procedures and mark bits

`GC_register_disclaim_proc` runs the procedure as a finalizer on objects
of that kind. If it returns nonzero, the object is kept and the procedure
is asked again the next time the object is unreachable. `GC_is_marked`
and `GC_set_mark_bit` only mean something inside a finalizer or disclaim
procedure. There, the object being finalized counts as marked if the
client called `GC_set_mark_bit` on it after the collection that found it
unreachable started, which is how libgc clients rescue such objects. Every
other object counts as marked.

### When cycle effects become visible

FUGC collects on its own threads. A client observes a finished cycle
(`GC_gc_no`, cleared links, queued finalizers, start/collection-event
callbacks) the next time it allocates or calls into the library. The check
is one `zgc_completed_cycle()` comparison.
`GC_call_with_alloc_lock` runs the check before it takes the lock. So code
that reveals links under the lock sees them cleared, as it would with libgc.
libgc also only acts during allocation, so the observable behaviour is
similar.

## Semantic gaps

- **Mark procedures and custom kinds are never called.** FUGC scans every
  object precisely, so all pointer-typed words are strong. Clients that use
  a mark procedure to make some fields weak get strong fields instead. Guile's
  weak tables and weak vectors are examples. The result is leaks, not
  crashes. Weak references that must work need a hidden pointer plus a
  disappearing link, or a port to `zweak`/`zweak_map`.
- **Atomic memory holds strong pointers.** `GC_malloc_atomic` does not
  hide the pointers stored in it. Code that relies on atomic memory being
  ignored by the collector keeps those objects alive.
- **Finalization is unordered.** Every registration behaves like
  `GC_register_finalizer_no_order`. When A points to B and both have
  finalizers, both run in the same batch, in unspecified order. libgc would
  run A first and B only on a later cycle. **Long links** are cleared at
  the same time as short links.
- **Pointers disguised by hand** (`~(uintptr_t)p`, tagged pointers, XOR
  lists) lose their capabilities. That is a Fil-C constraint, not a libgc
  one. Only the `GC_HIDE_POINTER` macros are bridged.
- **`GC_base` on non-heap memory** returns the enclosing object's base
  (a global or stack object) instead of NULL.
- **Statistics are approximate.** `GC_get_heap_size` is the resident set
  size sampled after each observed cycle. `GC_get_free_bytes` is 0.
  Allocation counters count only allocations made through this API.
- **`GC_disable` cannot stop FUGC.** It only maintains the counter that
  `GC_is_disabled` reports. `GC_enable_incremental`, time limits, stop
  functions and heap limits have no effect.
- **Toggle-refs** are held strongly forever. The toggle-ref callback is
  never called.
- `GC_enumerate_reachable_objects_inner`, back pointers and the leak
  detector do nothing.

## Validation

- `ports/boehmgc/fugc_test.c` runs in `checkPhase`. It covers allocation,
  finalizers (100/100 dead objects finalized), live and cancelled
  finalizers, resurrection and re-registration, disappearing links with
  hidden pointers (clear, move, unregister), uncollectable objects surviving
  when only a hidden pointer refers to them, finalize-on-demand with a
  notifier, `GC_finalized_malloc`, threads, kinds and typed allocation.
- Upstream's `cord/tests/cordtest.c` also runs in `checkPhase` against
  libcord built on this libgc.
- The exported symbols are a superset of upstream libgc 8.2.12's, except
  for the internal `GC_arrays` and `GC_push_other_roots` variables.
- Upstream's own tests, built by hand against this library: `realloc_test`,
  `huge_test` (absurd sizes go to the OOM function instead of a Fil-C
  panic), `middle`, `smash_test`, `threadkey_test`, `subthread_create` and
  `initsecondarythread` pass. `test.c` (gctest) fails: it checks
  collector internals such as exact sizes, displacement checks and
  finalization counts under libgc's ordering. `disclaim_test` fails
  because it depends on ordered finalization. `disclaim_weakmap_test` fails
  because it stores a pointer in a `GC_word` with flag bits, which Fil-C
  rejects.

## Consumers

Tested so far (nixos-26.05 campaign blockers):

- **w3m** builds. `w3m -dump` of a 3000-row table gives output identical
  to native w3m. It runs 8.3 s against native's 0.56 s, but linking it
  against a malloc-only libgc stub gives the same 8.2 s, so the time is
  Fil-C w3m itself, not this library.
- **a2ps** builds, and its test suite passes 23/23 (now enabled in
  `ports.nix`). It needed a fix unrelated to GC: gnulib's old `obstack.h`
  aligns pointers relative to `(char *) 0`, which drops their
  capabilities. The test scripts also needed their `/bin/rm` and shebangs
  patched.
- **guile_3_0** is marked broken. With the build fixes in `ports.nix`
  (drop an already-applied patch, `--disable-jit`, and expose only the
  programs of the native guile that compiles the Scheme modules, so that
  its native libraries stay off the Fil-C link path), libguile compiles
  and links against this libgc. But Guile stores SCM values in
  `scm_t_bits` (`uintptr_t`) cell words, so every heap reference loses its
  capability. The first symbol-table lookup during `scm_init_struct`
  traps. A Guile port would make `scm_t_bits` a pointer type (like the
  CPython and Perl ports) and move the VM stack out of mmap'd memory. Its
  weak tables use mark procedures, which would need `zweak_map`. That
  work, not libgc, is what the ~50 guile-* packages, guix, lilypond,
  mailutils, shepherd and mcron now wait on.
- **crystal, nim** were not attempted. Crystal needs LLVM and a Crystal
  bootstrap compiler. Nim's generated C and its own GC cast pointers to
  integers, and libgc is only an optional backend there.
