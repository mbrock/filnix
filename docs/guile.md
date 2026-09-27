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
| `ports.[ch]` | `scm_c_make_port (…, scm_t_bits stream)` usually gets a pointer as an integer argument | The exported functions are now `scm_i_c_make_port[_with_encoding]` taking `SCM stream`. `scm_c_make_port` and `scm_c_make_port_with_encoding` are always-inline wrappers with the old signature, so a caller's `(scm_t_bits) ptr` is converted back in the caller, where Fil-C can still see the pointer |
| `smob.[ch]` | `scm_i_new_smob`/`scm_i_new_double_smob` take data words as `scm_t_bits` | Take `SCM`. The inline `scm_new_smob` converts |
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
  (`SCM_SET_SMOB_DATA`, `SCM_SET_CELL_WORD`, `scm_c_make_port`,
  `scm_new_smob`) are safe when the pointer is converted in the same
  function. `scm_c_make_struct` and `scm_c_make_structv` now take
  `SCM`.
- **Raw memory introspection** does not work: `(system base types)` with
  the FFI memory backend (`types.test`) reads words at computed addresses
  and follows them as pointers, which Fil-C forbids by design. Arbitrary
  `make-pointer` of an address that was never handed out by
  `pointer-address`, `object-address` or a loaded image gives a pointer
  without a capability.
- **Out-of-memory is a Fil-C panic**, not a Guile exception
  (`test-out-of-memory`, `test-stack-overflow` under `ulimit -v`).
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
| PASS | 40,164 | 40,216 |
| FAIL | 91 | 12 |
| ERROR | 6 | 3 |

Nearly all of the extra failures are artefacts of the uninstalled
harness, not of Fil-C: 80 are "documented?" checks, which fail because
the uninstalled build looks for `guile-procedures.txt` under its
configure prefix, and `posix.test`'s `system*` errors were the `errno`
bug above (fixed since). Real differences:

- `types.test` stops with a Fil-C trap (raw memory introspection, above).
- `coverage.test` and `statprof.test` fail the same way for both.

`test-suite/standalone`: 41 of 47 pass, including `test-ffi`
(libffi calls and callbacks), `test-foreign-object-c`/`-scm`, the
pthread and `scm_with_guile` tests and the SMOB race test. The rest are
the gaps above (`test-smob-mark`, `test-unwind`, `test-out-of-memory`,
`test-stack-overflow`), plus two that need `guile-snarf` and a locale.

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

See the end of this file (updated as consumers are tried).
