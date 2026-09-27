# Guile 3.0 on Fil-C

`pkgsFilc.guile_3_0` is GNU Guile 3.0.11 built with Fil-C, on the libgc
API that `pkgsFilc.boehmgc` implements on FUGC (`docs/boehm-on-fugc.md`).
The port is `ports/patch/guile-3.0.11.patch` (about 40 files in
`libguile/`), plus the build settings in `ports.nix`. The Scheme side is
unchanged: the build platform's Guile compiles the modules, and the `.go`
files are the same bytecode as native ones.

## What breaks, and why

Guile's `SCM` type is already a pointer
(`SCM_DEBUG_TYPING_STRICTNESS == 1`), and heap cells are read and written
as `SCM` (`SCM_GC_CELL_OBJECT`). Tagging is done by integer arithmetic on
`SCM_UNPACK`ed values. Under Fil-C that is fine: as
`docs/filc-findings.md` ("Pointer tagging works; integer-typed storage
loses capabilities") shows, what matters is the type of the *storage*,
not the tag bits. A pointer stored in a `scm_t_bits` (`uintptr_t`) word,
passed as a `scm_t_bits` argument or returned as one loses its
capability, and the next access traps. So the representation stays; what
the patch changes is every place that keeps a pointer in an integer
location. It finds them by running Guile and its test suite until nothing
traps, and by grepping for `scm_t_bits *`, `uintptr_t` returns and
`atomic_uintptr_t`.

| Where | Problem | Change |
|---|---|---|
| `struct.h` | `SCM_STRUCT_DATA_REF/SET` access slots through `scm_t_bits *` | Access the slot as `SCM`, converting with `SCM_UNPACK`/`SCM_PACK`. Flag updates become read-modify-write through the setter |
| `modules.h` | Module fields read with `SCM_STRUCT_DATA(m)[i]` | `SCM_STRUCT_SLOT_REF` |
| `struct.c`, `expand.[ch]`, `procs.c` | `scm_c_make_struct (…, scm_t_bits init, ...)` passes SCM values as integer varargs; `scm_c_make_structv` takes `scm_t_bits[]` | Both take `SCM` (`SCM init, ...` and `SCM init[]`). `scm_i_alloc_struct` takes the vtable as `SCM`. This is a source-incompatible API change, caught at compile time |
| `dynstack.c` | Dynstack entries are `scm_t_bits` words holding SCM values, C function and data pointers, jmp_buf pointers | Entry words are read and written through `SCM *` or `void **` (`WORD`, `PTR_WORD`); headers stay integers |
| `cache-internal.h`, `fluids.c`, `intrinsics.c` | The fluid cache stores keys and values as `scm_t_bits` | `SCM` fields |
| `options.h`, `options.c`, `print.c`, `private-options.h` | SCM-valued options (print highlight prefix, keyword style) in a `scm_t_bits` field | The field is a union with an `SCM scm_val` member used for SCM options |
| `atomics-internal.h` | `scm_atomic_*_scm`/`_pointer` go through `atomic_uintptr_t` | `__atomic_*` builtins on the pointer types |
| `ports.[ch]` | `scm_c_make_port (…, scm_t_bits stream)` usually gets a pointer as an integer argument | The exported functions are now `scm_i_c_make_port[_with_encoding]` taking `SCM stream`. `scm_c_make_port` and `scm_c_make_port_with_encoding` are macros with the old arguments that convert with `SCM_PACK ((scm_t_bits) (stream))` in the caller's expression, which keeps the capability even at `-O0` |
| `smob.[ch]` | `scm_i_new_smob`/`scm_i_new_double_smob` take data words as `scm_t_bits` | Take `SCM`. `SCM_NEWSMOB*` and `SCM_RETURN_NEWSMOB*` convert in the caller's expression and call them directly (mailutils builds its Guile module at `-O0`, where going through the inline `scm_new_smob` lost the pointer) |
| `inline.h` | `scm_cell`, `scm_words`, `scm_double_cell` and friends take words as `scm_t_bits` | Under `__FILC__`, `SCM_C_EXTERN_INLINE` adds `always_inline`, so the conversion is always visible (at `-O2`; see below) |
| `vm-engine.c` | u64/s64 stack slots can hold code or data pointers (`load-label`, `word-ref`, `pointer-ref`); they were stored as integers | `SP_REF_U64`/`SP_SET_U64` (and s64, and slot moves) store and load through the slot's `void *` member |
| `gsubr.c` | `primitive_call_ip` returned the call IP as `uintptr_t` | Returns a pointer |
| `foreign-object.c` | `scm_foreign_object_ref` returned `(void *)` of a `scm_t_bits` result | Loads the slot as a pointer after the checks. `scm_foreign_object_set_x` stores one |
| `vm.c` | After growing the VM stack, `fp` and `sp` were relocated by adding an offset, so they kept the *old* (unmapped) stack's capability | Recompute them from the new stack's top |
| `foreign.c`, `loader.c`, `vm.c` | `(T *) ROUND_UP ((uintptr_t) p, a)` in loops and across variables | Add the rounding difference to `p` |

### Addresses that Scheme holds as integers

Scheme code sometimes turns an address back into an object:
`(pointer->scm (make-pointer addr))` in `(system vm debug)` and the
disassembler (to read constants from loaded `.go` images),
`primitive-code-name` on a code address, and FFI code that keeps
`(pointer-address p)` and later calls `(make-pointer addr)`. An integer
has no capability, so `make-pointer` now derives one
(`scm_i_pointer_from_address` in `loader.c`):

- from the loaded ELF image that contains the address, if any;
- else from a strong `zexact_ptrtable` of addresses handed out by
  `pointer-address`. The object stays alive until it is freed, like C
  memory whose address a program keeps. This is needed for, for example,
  `test-foreign-object-scm`, which keeps a `malloc`ed address in an
  unboxed field and frees it in a finalizer;
- else from the weak table below, which `object-address` records into.

Otherwise the pointer has no capability and using it traps.
`primitive-code-name` rebases its address onto the subr code arena.

### Weak references

libgc keeps weak references in memory it does not trace. Guile's weak
sets (the symbol table, the port table), weak tables (object properties,
source properties, `make-weak-key-hash-table`, fluid value tables) and
weak vectors put keys in "pointerless" memory with disappearing links, or
use a typed allocation whose bitmap omits the weak fields. FUGC ignores
bitmaps and scans every pointer-typed word, so these would have been
strong, and since the fields were `scm_t_bits`, reading them trapped.

The port keeps the disappearing links and changes how weak slots hold
their referent (`bdw-gc.h`):

- `scm_i_weak_hide (x)` encodes a heap object into a weak
  `zexact_ptrtable` (`scm_i_weak_refs`) and returns the address with no
  capability, which is what gets stored. The collector does not see it.
- `scm_i_weak_reveal (x)` decodes such a value back into a pointer. If
  the object has died, the table gives an invalid pointer and the reveal
  returns 0, as if the link had already been cleared. Values that carry a
  capability (the strong half of a weak-key or weak-value table) are
  returned as they are.
- A weak set that reads a dead entry clears it and unregisters its link
  on the spot. The shim clears links only when it notices a finished
  cycle, and the slot could be reused by then.

Measured with 10,000 weak-key entries of which 100 stay reachable: 100
remain after `(gc)`, as with native Guile. Guardians and weak vectors
behave the same as native too.

### Continuations

`call/cc` in Guile copies the C stack between the continuation barrier
and the capture point, and reinstating a continuation copies it back and
`longjmp`s. Fil-C does not let a program read or rewrite its stack, and
`longjmp` only works while the `setjmp` frame is live. Under Fil-C a full
continuation captures only the VM state (the VM stack is ordinary
memory). Each `scm_call_n` records its `jmp_buf` in a list of active VM
entries, and invoking a continuation checks that the entry that captured
it is still active. Then it `longjmp`s to that entry directly. This
covers continuations captured and invoked in Scheme code, including
generators and re-entry, which is what the test suite exercises.
Invoking a continuation after the C frame that captured it has returned
(for example one captured inside `scm_c_eval_string` and called from C
later, as in `test-unwind`) raises "cannot reinstate a continuation whose
C stack has been unwound" instead of crashing. Delimited continuations
(prompts, `abort-to-prompt`, fibers-style suspension) never copied the C
stack and work unchanged.

### Smaller fixes

- `SCM_CHECK_STACK` and `scm_stack_size` used the address of a local as
  the C stack pointer. Fil-C allocates address-taken locals on the heap,
  so the depth was nonsense and Guile reported a stack overflow at
  startup. They use `zstack_pointer ()` (and thread bases are
  `zstack_top ()`, from `GC_get_stack_base`).
- `queue_after_gc_hook` pushes its async cell with CAS (see the
  `srfi-18` item under "Remaining gaps").
- Guile bugs that Fil-C caught: `scm_c_make_struct` read one vararg
  past the last one; `bitvector-copy` read one word past the source;
  `guardian_apply` was registered with one optional argument but declared
  with two; `do_spawn` returned -1 without setting `errno` from
  `posix_spawn`'s result, so `system*` of a missing program failed with
  ECHILD.

## Remaining gaps

- **The JIT is disabled** (`--disable-jit`): Lightning emits machine code.
- **Performance.** Without JIT on both sides, `(fib 30)` takes 0.65 s
  against 0.09 s natively, allocation-heavy code about 2.7x native, and
  startup 0.15 s against 0.02 s. Calls from C into Scheme are much
  slower (a `sort` with a Scheme comparator is 16x native) because every
  `scm_call_n` does a `setjmp`, which costs about 370 ns under Fil-C
  against 4 ns natively (a microbenchmark of `setjmp` alone).
- **Full continuations cannot re-enter C frames that have returned**
  (above).
- **SMOB mark functions are never called** (`test-smob-mark`). FUGC
  traces the SMOB's words itself, so SCM values stored in its cells stay
  alive. Values that a mark function would reach through C memory are
  kept alive as long as that memory holds real pointers.
- **C extensions must store pointers as pointers.** The same rule applies
  to libraries that call libguile: a pointer passed through a
  non-inline function parameter, struct field or array of type
  `scm_t_bits` loses its capability. The libguile macros
  (`SCM_SET_SMOB_DATA`, `SCM_SET_CELL_WORD`, `SCM_NEWSMOB`,
  `scm_c_make_port`) are safe at any optimization level when given the
  pointer itself. The inline functions that take `scm_t_bits` words
  (`scm_cell`, `scm_double_cell`, `scm_words`, `scm_new_smob`) are
  always inlined, which keeps pointers only when the extension is
  compiled with optimization. `scm_c_make_struct` and
  `scm_c_make_structv` now take `SCM`.
- **Raw memory introspection** does not work: `(system base types)` with
  the FFI memory backend (`types.test`) reads words at computed addresses
  and follows them as pointers, which Fil-C forbids by design. Arbitrary
  `make-pointer` of an address that was never handed out by
  `pointer-address`, `object-address` or a loaded image gives a pointer
  without a capability.
- **Out-of-memory is a Fil-C panic**, not a Guile exception
  (`test-out-of-memory`, `test-stack-overflow` under `ulimit -v`).
- **`srfi-18.test` hangs in about 3 of 16 runs** (native: 0 of 12).
  Evidence from a hung run, with `FILC_DUMP_STACKS_ON_SIGNAL=10` and
  `kill -USR1`: the main thread waits in `lock_mutex` → `block_self` →
  `pthread_cond_wait`, called from `scm_timed_lock_mutex` directly from
  the VM (a Scheme `lock-mutex`/`mutex-lock!`); the thread it waits for
  is in a condition-variable wait too; the finalizer thread is idle in
  `read`. One cause was found and fixed: libgc runs the GC start callback
  with the world stopped, but the shim runs it on whichever thread
  notices a finished cycle, while other threads keep running. Guile's
  `queue_after_gc_hook` pushed a shared async cell onto the thread's
  async list with plain stores, racing with `system-async-mark` from
  other threads (lost asyncs, a cell on two lists). It now claims the
  cell and pushes with CAS. That fixed a reduced reproducer
  (`make-thread` + `thread-terminate!` in a loop hung 1 run in 8 before,
  0 in 32 after), but not all `srfi-18.test` hangs. Condition waits in
  Guile also return early whenever an async is pending, and FUGC
  completes cycles far more often than libgc, so after-GC asyncs make
  such spurious wakeups much more frequent. Code that treats one wakeup
  as a signal (SRFI-18's `make-thread` handshake does) is exposed to that.
- `object-address` and `pointer-address` enter the object into a table,
  which costs a lock and some memory. `pointer-address` keeps the object
  alive until it is freed.
- A weak slot is revealed through an exact pointer table keyed by
  address. If an object dies and another object is allocated at the same
  address and entered into the table before the dead slot is read, the
  slot would resolve to the new object. Guile reads the entry's hash
  first and weak-set lookups re-check the key, which makes this
  unlikely to matter, but it is not impossible.

## Testing

The Scheme test suite (`test-suite/tests/*.test`, run file by file with
the uninstalled `libguile/guile` and the build platform's `.go` files,
the same bytecode) against native Guile 3.0.11 in the same harness:

| | Fil-C | native |
|---|---|---|
| PASS | 40,168 | 40,159 |
| FAIL | 91 | 12 |
| ERROR | 2 | 3 |

Of the extra failures, 80 are documentation checks ("documented?", `object-documentation`), an artefact of the
uninstalled harness: the build looks for `guile-procedures.txt` under
its configure prefix. With those removed, the lists of failing tests are
the same for both, except:

- `types.test` stops with a Fil-C trap (raw memory introspection,
  above), so its remaining tests do not run.
- `srfi-18.test` sometimes hangs (above).
- `ports.test`'s canonicalization test fails for both (FAIL here, ERROR
  natively).

`coverage.test`, `statprof.test`, `popen.test` and parts of
`posix.test` fail for both in this harness.

`test-suite/standalone` (C programs and scripts, run by hand): 38 pass,
including `test-ffi` (libffi calls and callbacks),
`test-foreign-object-c`/`-scm`, `test-asmobs`, `test-extensions`, the
pthread and `scm_with_guile` tests and `test-smob-mark-race`. One is
skipped (`test-command-line-encoding`, needs a locale). Five fail:
`test-smob-mark`, `test-unwind`, `test-out-of-memory` and
`test-stack-overflow` are the gaps above, and `test-guile-snarf` needs
`guile-snarf` on `PATH`.

The package's `installCheckPhase` runs a smoke test of the installed
interpreter (modules, `match`, `format`, bignums, GC, `call/cc`). Like
Nixpkgs, the build does not run `make check`.

To reproduce: `nix print-dev-env .#legacyPackages.x86_64-linux.pkgsFilc.guile_3_0`,
then `unpackPhase`, `patchPhase`, `configurePhase`, `make -C lib` and
`make -C libguile`, and run `libguile/guile` with `GUILE_LOAD_PATH` and
`GUILE_LOAD_COMPILED_PATH` pointing at a native Guile 3.0.11's
`share/guile/3.0` and `lib/guile/3.0/ccache`, and
`GUILE_AUTO_COMPILE=0`.

## Consumers

Built with `nix build .#legacyPackages.x86_64-linux.pkgsFilc.<name>`
against the Fil-C Guile:

- **guile-json** builds unchanged (its modules are compiled by the build
  platform's Guile). Its test suite, run by hand with the Fil-C `guile`:
  183 of 183 pass (builder 68, parser 76, record 39).
- **guile-lib** builds unchanged. Its unit tests with the Fil-C `guile`:
  16 of 17 files pass. `os.process.scm` fails the same way with native
  Guile (it runs `guile` from `PATH`).
- **guile-fibers** builds unchanged, including its `fibers-epoll` C
  extension.
- **gnu-shepherd** (1.0.9) builds with `ports.nix` adding a `guile` for
  configure. Configure checks that Fibers loads, and the build
  platform's Guile cannot load Fibers' Fil-C extension, so the Fil-C
  Guile itself compiles Shepherd's modules (it runs on the build
  machine). Shepherd works: started as a user daemon with two
  `make-forkexec-constructor` services, `herd status` lists them,
  `herd stop ticker` kills its process, and `herd stop root` shuts down
  cleanly.
- **mcron** (1.2.1) builds with the Fil-C `guile` as its build-time
  guile, and its test suite, which runs in the build with that guile,
  passes: 74 pass, 1 skipped.
- **mailutils** (3.21) builds with Guile support, and its whole test
  suite runs in the build and passes: 1,444 tests, 13 skipped. That
  includes the 46 tests of its Guile module (`libmu_scm`: mailboxes,
  messages, MIME), which load the Fil-C extension into the Fil-C
  `guile`. This needed (see `ports.nix`): the MySQL backend off
  (mariadb-connector-c does not link for Fil-C: its linker version
  script is rejected) and GSSAPI off, an unprefixed `pkg-config` so that
  `guile-config` reports the Fil-C Guile, the Fil-C `guile` on `PATH`
  for the tests, and fixes for four out-of-bounds reads that Fil-C
  stopped: `imap4d`'s LIST read `ref[-1]` for an empty reference (a
  real bug in the server), and three in test helpers (`cwdrepl.c`,
  `encode2047.c`, `tesh.c`). The Guile module is compiled at `-O0`,
  which is why `SCM_NEWSMOB` had to convert in the caller.

Not tried yet: guix, lilypond and the other guile-* libraries.
Most guile-* libraries are pure Scheme and should build like guile-json.
Libraries with C parts that keep pointers in `scm_t_bits` storage will
need the same kind of changes as libguile (see "Remaining gaps").
