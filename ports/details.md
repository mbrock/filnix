# Fil-C Port Details

Detailed summaries and compatibility changes for all ported projects.

## Linux-PAM v1.6.1 and v1.7.1

Both versions apply Debian-specific patches that replace hardcoded system paths with build-time configuration macros and add Debian-specific PAM module features. No Fil-C-specific compatibility changes.

### Fil-C Compatibility Changes

None - these are Debian packaging patches, not Fil-C adaptations.

---

## Python 3.12.5

Extensive rework of Python's low-level memory and concurrency primitives to work with Fil-C's capability model. Changes touch GC, atomics, frame allocation, and code object handling.

### Fil-C Compatibility Changes

### GC Header Rewrite (pycore_gc.h, pycore_object.h)
**Problem:** GC used `uintptr_t` for linked list pointers with tag bits in low bits  
**Solution:** Switch to real pointers with capability-aware bit manipulation

```c
typedef struct PyGC_Head {
-    uintptr_t _gc_next;
-    uintptr_t _gc_prev;  // low 2 bits used for flags
+    PyGC_Head* _gc_next;
+    PyGC_Head* _gc_prev;
 } PyGC_Head;
```

**Helper function changes:**
- `_PyGCHead_PREV`: `_Py_CAST(uintptr_t, prev)` → `zandptr(prev, _PyGC_PREV_MASK)`
- `_PyGCHead_SET_PREV`: Direct cast → `zretagptr(prev, gc->_gc_prev, _PyGC_PREV_MASK)`
- `_PyGCHead_SET_FINALIZED`: OR operation → `zorptr(gc->_gc_prev, _PyGC_PREV_MASK_FINALIZED)`

**Impact:** GC traversal maintains capabilities throughout linked list walks

### Atomic Operations (pycore_atomic.h)
**Problem:** Python used `atomic_uintptr_t` for pointer atomics  
**Solution:** Use `void*_Atomic` directly

```c
 typedef struct _Py_atomic_address {
-    atomic_uintptr_t _value;
+    void*_Atomic _value;
 } _Py_atomic_address;
```

**Disabled intrinsics:**
- Added `#error` guards for `HAVE_BUILTIN_ATOMIC` and `__GNUC__` x86 paths
- Forces fallback to C11 atomics that work with capabilities

### Interpreter State (pycore_interp.h, pycore_runtime.h)
**Problem:** `_finalizing` stored as `uintptr_t`, treated as both integer and `PyThreadState*`  
**Solution:** Store actual pointer, cast thread_id separately

```c
-_Py_atomic_store_relaxed(&interp->_finalizing, (uintptr_t)tstate);
+_Py_atomic_store_relaxed(&interp->_finalizing, tstate);
```

### Frame Allocation Overhaul (pycore_frame.h, pycore_pystate.c)
**Original design:** Frames allocated from chunked stack  
**New design:** GC-allocated frames with linked list tracking

**PyThreadState changes:**
```c
-    _PyStackChunk *datastack_chunk;
-    PyObject **datastack_top;
-    PyObject **datastack_limit;
+    struct _PyInterpreterFrame *datastack_top_frame;
```

**_PyInterpreterFrame changes:**
```c
 typedef struct _PyInterpreterFrame {
     PyCodeObject *f_code;
+    struct _PyInterpreterFrame *_f_caller_frame;  // NEW: track caller
     struct _PyInterpreterFrame *previous;
```

**Allocation:**
```c
-_PyInterpreterFrame *new_frame = (_PyInterpreterFrame *)tstate->datastack_top;
-tstate->datastack_top += code->co_framesize;
+_PyInterpreterFrame *new_frame = (_PyInterpreterFrame *)zgc_alloc(size * sizeof(PyObject *));
+result->_f_caller_frame = tstate->datastack_top_frame;
+tstate->datastack_top_frame = result;
```

**Rationale:** Chunk-based allocation incompatible with capability provenance tracking

### Code Object Caching (pycore_code.h, Objects/codeobject.c)
**Problem:** Inline caches embed `PyObject*` in bytecode instruction stream  
**Solution:** Encode pointers through `_PyCode_PtrTable`

```c
+extern zptrtable* _PyCode_PtrTable;

 static inline void write_obj(uint16_t *p, PyObject *val) {
-    memcpy(p, &val, sizeof(val));
+    uintptr_t valint = zptrtable_encode(_PyCode_PtrTable, val);
+    memcpy(p, &valint, sizeof(valint));
 }
```

**Impact:** Bytecode cache invalidation/resurrection cycles preserve capabilities

### Generator Objects (cpython/genobject.h)
```c
-#define _PyGenObject_HEAD(prefix)  PyObject_HEAD
+#define _PyGenObject_HEAD(prefix)  PyObject_VAR_HEAD
```
**Rationale:** Generators need variable header for capability tracking

### Long Integer Pointer Conversion (Objects/longobject.c)
**Problem:** `PyLong_FromVoidPtr` / `PyLong_AsVoidPtr` cast pointers to integers  
**Solution:** Use `zexact_ptrtable` for bijective encoding

```c
+static zexact_ptrtable* ptrtable;
+
 PyObject *PyLong_FromVoidPtr(void *p) {
-    return PyLong_FromUnsignedLong((unsigned long)(uintptr_t)p);
+    return PyLong_FromUnsignedLong(zexact_ptrtable_encode(ptrtable, p));
 }
```

### Signal Handling (Modules/signalmodule.c)
```c
 Py_LOCAL_INLINE(PyObject *) get_handler(int i) {
-    return (PyObject *)_Py_atomic_load(&Handlers[i].func);
+    return _Py_atomic_load(&Handlers[i].func);
 }
```

### GC Implementation (Modules/gcmodule.c)
- `gc_list_move`, `gc_list_append`: Use real pointer operations
- `update_refs`: `gc->_gc_next = zandptr(gc->_gc_next, ~NEXT_MASK_UNREACHABLE)`
- `handle_weakrefs`: Direct pointer comparisons instead of uintptr_t casts

### Memory Allocator (Objects/obmalloc.c)
**Disabled debug wrapper:** Returns `malloc(nbytes)` directly instead of debug tracking  
**Rationale:** Debug allocator's metadata relies on pointer arithmetic that breaks capabilities

### List Sorting (Objects/listobject.c)
```c
// Fixed pointer arithmetic in binarysort
-            Py_ssize_t offset = lo.values - lo.keys;
-            p = start + offset;
+            p = lo.values + (start - lo.keys);
```

### Build System
- **Makefile.pre.in**: Remove `-` prefix from compileall commands (fail on error)
- **configure.ac**: Disable perf trampoline (Linux-specific assembler)

### SIMD Detection
**Modules/_blake2/**: Disable SSE/AVX when `__PIZLONATOR_WAS_HERE__`  
**Modules/_multiprocessing/**: Change `sem_t*` → `unsigned long` (opaque handle)

### Memory Debugging
- **pycore_pymem.h**: `_PyMem_IsPtrFreed` returns 0 under Fil-C
- **pycore_tracemalloc.h**: Disable `__attribute__((packed))` for Fil-C

### Type System
- **Include/object.h**: Added `ZASSERT` checks in `Py_SET_TYPE`
- **Include/longobject.h**: Added `_Py_PARSE_INTPTR`/`_Py_PARSE_UINTPTR` for Fil-C

### Platform Detection
- **Include/cpython/longintrepr.h**: FIXME comment about stashing capabilities
- **Include/internal/pycore_obmalloc.h**: Force disable radix tree under Fil-C

### macOS Compatibility  
- **Lib/urllib/request.py**: Disable `_scproxy` (can't call native Mac functions)

---

## XML-Parser v2.47

Minimal Perl XS fix to properly decode pointers stored as integers using Fil-C's pointer table mechanism.

### Fil-C Compatibility Changes

### Perl XS Typemap
- **File**: `Expat/typemap`
- **Input type**: `T_ENCOBJ`
- **Change**: Replaced direct cast `$var = ($type) tmp` with `$var = zptrtable_decode(Perl_xsub_ptrtable, tmp)`
- **Why**: Perl XS stores pointers as integers (IV = integer values) for passing across the Perl/C boundary. Under Fil-C, pointers cannot be reconstructed from integers via cast - must use explicit pointer table lookup.
- **Pattern**: Pointer table (`zptrtable`) for integer↔pointer conversion

---

## attr 2.5.2

Minimal patch changing symbol versioning directives for Fil-C linker compatibility.

### Fil-C Compatibility Changes

- **libattr/syscalls.c**: Changed `.symver` to `.filc_symver` in SYMVER macro definitions
  - Two occurrences: one in the clang-specific path with `__no_reorder__`, one in the fallback definition
  - Fil-C requires `.filc_symver` instead of standard `.symver` for symbol versioning

---

## bash 5.2.32

Single-line patch changing flexible array member type for memory safety compatibility.

### Fil-C Compatibility Changes

- **unwind_prot.c**: Changed `char desired_setting[1]` to `void *desired_setting[1]` in SAVED_VAR struct
  - Flexible array member must use pointer type for correct capability tracking
  - Ensures proper alignment and pointer table (`zptrtable`) compatibility

---

## binutils 2.43.1

Substantial changes converting integer-based pointer storage to void* throughout chew.c, plus splay tree changes, template instantiations, sbrk disabling, and linker flag adjustments.

### Fil-C Compatibility Changes

### Pointer Table Conversions
- **bfd/doc/chew.c**: Extensive intptr_t → void* conversions
  - Changed `pcu.l` from `intptr_t` to `void*` in union
  - Stack (`istack[]`, `isp`) converted from `intptr_t*` to `void**`
  - Internal mode tracking changed to `void**`
  - All integer/pointer conversions now use explicit casts
  - Pattern: values stored as pointers, cast to intptr_t only for printing/comparison

- **include/splay-tree.h**: Changed splay_tree_key/value from `uintptr_t` to `void*`
  - Fundamental type change for pointer-based data structures

### sbrk Disabling
- **libiberty/xmalloc.c**: Undefed HAVE_SBRK
  - sbrk incompatible with Fil-C's memory management

### Linker Adjustments
- **libctf/configure.ac**: Removed `-Wl,` prefix from `--version-script` flag
- **libsframe/Makefile.am**: Removed `-Wl,` prefix from `--version-script` flag
  - Fil-C linker expects flags directly without `-Wl,` wrapper

### Template Instantiations
- **gold/symtab.cc**: Added explicit template instantiations for `compute_final_value<32>` and `compute_final_value<64>`
  - Required for Fil-C's stricter template handling

---

## bison 3.8.2

Alignment macro rewritten to use Fil-C's zmkptr function for proper capability handling during pointer arithmetic.

### Fil-C Compatibility Changes

- **lib/obstack.h**: Rewrote `__BPTR_ALIGN` macro
  - Added includes: `<stdfil.h>` and `<inttypes.h>`
  - Original: `((B) + (((P) - (B) + (A)) & ~(A)))`
  - New: Uses GCC statement expression with temporary variable
  - Calls `zmkptr(__P, (uintptr_t)((B) + ((__P - (B) + (A)) & ~(A))))`
  - `zmkptr` preserves capabilities while creating aligned pointer from address
  - Pattern: compute address arithmetically, then construct pointer with proper bounds

---

## bzip3

Build configuration changes with no actual Fil-C compatibility modifications.

### Fil-C Compatibility Changes

None - no C/C++ code changes for memory safety.

---

## cairo 1.18.0

Systematic conversion of GLib once-initialization patterns from gsize to gpointer for proper type handling.

### Fil-C Compatibility Changes

### GObject Type Registration
- **util/cairo-gobject/cairo-gobject-enums.c**: Changed all enum type registration functions
  - Pattern repeated ~25 times across different enum types
  - Changed `static gsize type_ret = 0` to `static gpointer type_ret = 0`
  - Changed `g_once_init_enter(&type_ret)` to `g_once_init_enter_pointer(&type_ret)`
  - Changed `g_once_init_leave(&type_ret, type)` to `g_once_init_leave_pointer(&type_ret, type)`
  
- **util/cairo-gobject/cairo-gobject-structs.c**: Updated CAIRO_GOBJECT_DEFINE_TYPE_FULL macro
  - Same gsize → gpointer pattern
  - Same g_once_init_* function changes

### Rationale
- GLib's gsize-based once-init conflates pointer storage with size type
- Fil-C requires proper pointer types for capability tracking
- gpointer variants ensure type safety

---

## cmake 3.30.2

Simple library directory path change, not a Fil-C compatibility fix.

### Fil-C Compatibility Changes

None - this is a library installation path preference.

---

## dash 0.5.12

Single-line vfork→fork change for Fil-C compatibility, buried in massive autotools bloat.

### Fil-C Compatibility Changes

- **src/jobs.c**: Changed `vfork()` to `fork()`
  - vfork's shared address space semantics incompatible with Fil-C's capability tracking
  - Standard fork provides proper memory isolation

---

## dhcpcd 10.0.8

Comprehensive red-black tree implementation changes to preserve capabilities during pointer tagging operations.

### Fil-C Compatibility Changes

### Pointer Tagging in Red-Black Trees
- **compat/rbtree.h**: Complete rewrite of pointer tagging macros
  - Added `#include <stdfil.h>`
  - Changed `rb_info` from `uintptr_t` to `struct rb_node*`

### Fil-C Pointer Operations
Pattern: Replace bitwise operations on pointers with Fil-C intrinsics that preserve capabilities

- **zretagptr(ptr, new_val, mask)**: Create new pointer preserving tagged bits
  - `RB_SET_FATHER(rb, father)`: `zretagptr((father), (rb)->rb_info, ~RB_FLAG_MASK)`

- **zorptr(ptr, bits)**: OR operation preserving capabilities
  - `RB_MARK_RED(rb)`: `zorptr((rb)->rb_info, RB_FLAG_RED)`

- **zandptr(ptr, mask)**: AND operation preserving capabilities
  - `RB_MARK_BLACK(rb)`: `zandptr((rb)->rb_info, ~RB_FLAG_RED)`
  - `RB_ZERO_PROPERTIES(rb)`: `zandptr((rb)->rb_info, ~RB_FLAG_MASK)`

- **zxorptr(ptr, bits)**: XOR operation preserving capabilities
  - `RB_INVERT_COLOR(rb)`: `zxorptr((rb)->rb_info, RB_FLAG_RED)`
  - `RB_COPY_PROPERTIES`: Complex XOR with mask
  - `RB_SWAP_PROPERTIES`: XOR swap pattern

### Casts Added
- All macro uses that extract values now cast to `uintptr_t` for arithmetic
- `RB_FATHER`, `RB_POSITION`, `RB_RED_P`, `RB_BLACK_P` macros cast before bit testing
- Preserves pointer in storage, extracts integer only for bit checks

---

## diffutils 3.10

Warning suppression and stack overflow handling changes for Fil-C compatibility.

### Fil-C Compatibility Changes

### Diagnostic Pragmas
- **lib/regex.h**: `#pragma clang diagnostic ignored "-Wvla"`
- **lib/stdio.in.h**: `#pragma clang diagnostic ignored "-Winclude-next-absolute-path"`
- **lib/unistd.in.h**: `#pragma clang diagnostic ignored "-Winclude-next-absolute-path"`
- **lib/wctype.in.h**: `#pragma clang diagnostic ignored "-Winclude-next-absolute-path"`
- **src/diff.c**: `#pragma clang diagnostic ignored "-Wbool-operation"`

### Stack Overflow Handling
- **lib/sigsegv.c**: Disabled stack overflow recovery with `#if HAVE_STACK_OVERFLOW_RECOVERY && !defined(__FILC__)`
  - Fil-C's stack management incompatible with low-level stack manipulation

---

## e2fsprogs 1.47.1

Systematic removal of sbrk usage for memory tracking, replacing with NULL pointers.

### Fil-C Compatibility Changes

### sbrk Removal
sbrk(0) used to query current program break (heap end) for memory usage tracking. Fil-C doesn't support sbrk, so all calls replaced with NULL.

- **e2fsck/iscan.c**: 
  - `init_resource_track`: `track->brk_start = NULL` (was `sbrk(0)`)
  - `print_resource_track`: Two occurrences of `(char*)NULL` (was `(char*)sbrk(0)`)

- **e2fsck/scantest.c**:
  - `init_resource_track`: `track->brk_start = NULL` (was `sbrk(0)`)
  - `print_resource_track`: `(char*)NULL` (was `(char*)sbrk(0)`)

- **e2fsck/util.c**:
  - `init_resource_track`: `track->brk_start = NULL` (was `sbrk(0)`)
  - `print_resource_track`: Two occurrences of `(char*)NULL` (was `(char*)sbrk(0)`)

- **resize/resource_track.c**:
  - `init_resource_track`: `track->brk_start = NULL` (was `sbrk(0)`)
  - `print_resource_track`: `(char*)NULL` (was `(char*)sbrk(0)`)

### Impact
Memory usage tracking will report incorrect values (all calculations from NULL base), but code remains functional. This is acceptable since:
- Resource tracking is diagnostic/informational only
- Fil-C's GC makes sbrk-based tracking meaningless anyway

---

## elfutils 0.191

Warning suppression only - no actual Fil-C compatibility changes.

### Fil-C Compatibility Changes

None - only diagnostic pragma additions.

---

## Emacs 30.1

Substantial changes to integrate Emacs' Lisp allocator with Fil-C's garbage collector (FUGC). All custom memory pools replaced with direct zgc_alloc calls, and several subsystems disabled for safety.

### Fil-C Compatibility Changes

- **src/alloc.c**: Core allocator integration
  - All Lisp object allocators wrapped with `if ((true)) zgc_alloc(...)` bypass
  - Disabled custom memory managers: `make_interval()`, `allocate_string()`, `allocate_string_data()`, `make_float()`, `Fcons()`, `allocate_vectorlike()`, `make_lisp_symbol()`
  - Added `zerror()` guards to `lisp_malloc()` and `lisp_align_malloc()` to catch unexpected usage
  - Disabled memory reserve system (`refill_memory_reserve()`)
  - Disabled garbage collection entirely (`maybe_garbage_collect()`, `garbage_collect()`)
  
- **src/eval.c**: Added `#include <stdfil.h>`

- **src/lisp.h**: Symbol pointer handling for FUGC
  - Modified `XBARE_SYMBOL()` to handle both lispsym table and heap-allocated symbols
  - Updated `make_lisp_symbol_internal()` to use `TAG_PTR_INITIALLY` for heap symbols
  - Removed `__builtin_unwind_init()` from `flush_stack_call_func()` (incompatible with Fil-C)

- **src/sysdep.c**: Disabled SIGSEGV handler completely
  - `init_sigsegv()` now returns 0 without setting up signal handler
  - Removes stack overflow handling (conflicts with FUGC's memory model)

---

## Expat 2.7.1

No actual Fil-C compatibility changes - patch only adds a generated autotools configuration file.

### Fil-C Compatibility Changes

None - no C/C++ code modifications.

---

## Gettext 0.22.5

Minor pointer arithmetic fix and wholesale symbol renaming with "pizlonated_" prefix for libtextstyle library to avoid symbol conflicts.

### Fil-C Compatibility Changes

- **gettext-runtime/intl/localealias.c**: Pointer arithmetic fix
  - Changed `map[i].alias += new_pool - string_space` to `map[i].alias = new_pool + (map[i].alias - string_space)`
  - Same for `map[i].value`
  - Prevents undefined behavior from pointer difference used as integer offset

- **libtextstyle/lib/libtextstyle.sym.in**: Symbol versioning for Fil-C
  - All 130 exported symbols renamed with "pizlonated_" prefix
  - Example: `_libtextstyle_version` → `pizlonated__libtextstyle_version`
  - Prevents symbol conflicts in Fil-C's unified namespace

- **Test skips**:
  - `gettext-tools/tests/msgfmt-6`: Division by zero test (exit 77)
  - `gettext-tools/tests/msginit-4`: Unicode CLDR test (exit 77 with FIXME note)

---

## Git 2.46.0

Extensive changes to option parsing infrastructure to eliminate intptr_t casts, replacing them with direct void* pointers for Fil-C's strict pointer tracking.

### Fil-C Compatibility Changes

### Core infrastructure changes
- **parse-options.h**: Changed struct option field type
  - `intptr_t defval` → `void *defval`
  - Updated all OPT_* macros to use `(void *)(i)` casts instead of raw integer

- **parse-options.c**: Added explicit casts when reading defval
  - Changed `opt->defval` → `(intptr_t)opt->defval` in:
    - `OPTION_BIT`, `OPTION_NEGBIT`, `OPTION_BITOP`, `OPTION_SET_INT`
    - `OPTION_INTEGER`, `OPTION_MAGNITUDE` handlers

- **compat/bswap.h**: Disabled inline assembly for Fil-C
  - Added `&& !defined(__FILC__)` to GNUC bswap implementation guard

### Builtin command changes (40+ files modified)
All builtin commands updated to cast integer constants when passing to option structs:
- `(intptr_t)""` for default string values
- `(void *)CONST` for integer default values
- Examples across: `builtin/am.c`, `builtin/commit.c`, `builtin/merge.c`, `builtin/tag.c`, etc.

### Pattern applied consistently
- Before: `PARSE_OPT_OPTARG, NULL, (intptr_t)default_value`
- After: `PARSE_OPT_OPTARG, NULL, default_value` (for strings)
- After: `PARSE_OPT_OPTARG, NULL, (void *)VALUE` (for integers)

---

## GLib 2.80.4

Major type system change: GType converted from integer typedef to opaque pointer, requiring extensive uintptr_t casts throughout GObject system. Patch heavily bloated with CI configuration files.

### Fil-C Compatibility Changes

### Core type system (gobject/)
- **gobject/gtype.h**: Fundamental change
  - Changed `typedef gsize GType` (or gulong) to `typedef struct _GTypeOpaque *GType`
  - Makes GType an opaque pointer instead of integer
  - Required for Fil-C's pointer tracking
  - Updated macros: `G_TYPE_IS_FUNDAMENTAL()`, `G_TYPE_IS_DERIVED()` to cast to `(GType)`

- **gobject/gtype.c**: Extensive uintptr_t casts (50+ changes)
  - All type ID arithmetic now uses `(uintptr_t)` casts
  - Examples: `(uintptr_t) utype & ~(uintptr_t) TYPE_ID_MASK`
  - `lookup_type_node_I()`, type node allocation, fundamental type handling

- **gobject/gsignal.c**: Signal type handling (~30 changes)
  - All `G_SIGNAL_TYPE_STATIC_SCOPE` flag checks use uintptr_t
  - Pattern: `(uintptr_t) return_type & (uintptr_t) G_SIGNAL_TYPE_STATIC_SCOPE`
  - Applied to parameter types, return types, signal emission

- **gobject/gparamspecs.c**: Cast in GParamSpecGType initializer
  - `0xdeadbeef` → `(GType) 0xdeadbeef` for temporary value_type

### Test suite updates (gobject/tests/)
- Multiple test files updated to cast GType for comparisons:
  - `basics-gobject.c`, `dynamictype.c`, `param.c`, `reference.c`, `signals.c`, `type.c`
  - Pattern: `g_assert_cmpint((uintptr_t) type, ==, (uintptr_t) expected)`
  - `threadtests.c`: Changed `guintptr` to `gpointer` for consistency

- **gobject/tests/genmarshal.py**: Generated code now includes uintptr_t casts for static scope checks

---

## Grep 3.11

Minimal changes for Fil-C pointer provenance and signal handling compatibility.

### Fil-C Compatibility Changes

- **lib/obstack.h**: Pointer alignment with zmkptr
  - Replaced `__BPTR_ALIGN` macro with `zmkptr()` version
  - Before: `((B) + (((P) - (B) + (A)) & ~(A)))`
  - After: Uses `zmkptr(__P, (uintptr_t)((B) + ((__P - (B) + (A)) & ~(A))))`
  - Preserves pointer capability while computing aligned address
  - Added `#include <stdfil.h>` and `#include <inttypes.h>`

- **lib/sigsegv.c**: Disabled stack overflow recovery
  - Added `&& !defined(__FILC__)` to `HAVE_STACK_OVERFLOW_RECOVERY` check
  - Prevents SIGSEGV handler installation under Fil-C
  - Stack overflow handling conflicts with FUGC memory model

---

## ICU 76.1

Targeted changes for Fil-C pointer safety, compiler fencing, and build system adjustments to avoid assembly code generation.

### Fil-C Compatibility Changes

### Runtime code modifications
- **icu4c/source/common/putil.cpp**: Timezone handling
  - Added early return in `uprv_timezone()`: `if ((1)) return timezone;`
  - Bypasses complex timezone detection logic
  - Uses global `timezone` variable directly

- **icu4c/source/common/ucnv.cpp**: Pointer alignment with zmkptr
  - Changed: `stackBuffer = reinterpret_cast<void *>(aligned_p);`
  - To: `stackBuffer = zmkptr(stackBuffer, aligned_p);`
  - Preserves pointer provenance during alignment in safe clone operation

- **icu4c/source/common/unicode/char16ptr.h**: Aliasing barrier
  - Added `#ifdef __PIZLONATOR_WAS_HERE__` section
  - Defines `U_ALIASING_BARRIER(ptr)` as `zcompiler_fence()`
  - Replaces inline assembly with Fil-C fence primitive
  - Prevents compiler optimizations that violate memory model

### Build system changes
- **icu4c/source/configure.ac**: Disable assembly generation
  - Sets `GENCCODE_ASSEMBLY=` (empty)
  - Prevents assembly code generation during data compilation

- **icu4c/source/tools/toolutil/pkg_genc.h**: Force data-only mode
  - Added `#ifdef __PIZLONATOR_WAS_HERE__` → `#define U_DISABLE_OBJ_CODE`
  - Disables object code generation in packaging tool
  - Forces use of C data arrays instead of platform-specific binary formats

---

## JPEG 6b

Single alignment fix and removal of binary test files from repository.

### Fil-C Compatibility Changes

- **jmemmgr.c**: Alignment type change
  - Changed `#define ALIGN_TYPE  void*` to `#define ALIGN_TYPE  double`
  - Ensures memory blocks align to double (8-byte) boundaries instead of pointer size
  - More conservative alignment for Fil-C's memory model
  - Prevents potential alignment violations with stricter capability bounds

---

## KBD 2.6.4

Removes unnecessary (and dangerous) integer casts from ioctl pointer arguments. Most of patch is keymap data file corrections unrelated to Fil-C.

### Fil-C Compatibility Changes

### Source code changes (26 lines)
- **contrib/dropkeymaps.c**: Removed `(unsigned long)` casts
  - Changed `ioctl(fd, KDSKBENT, (unsigned long)&ke)` → `ioctl(fd, KDSKBENT, &ke)` (2 instances)

- **src/libkeymap/kernel.c**: Removed casts from ioctl calls
  - `KDGKBENT`: Removed `(unsigned long)` cast (1 instance)
  - `KDGKBSENT`: Removed `(unsigned long)` cast (1 instance)
  - `KDGKBDIACR(UC)`: Removed `(unsigned long)` cast (1 instance)

- **src/libkeymap/loadkeys.c**: Removed casts (6 instances)
  - `KDSKBENT`: 4 calls cleaned up
  - `KDSKBSENT`: 2 calls cleaned up
  - `KDSKBDIACRUC`, `KDSKBDIACR`: 2 calls cleaned up

- **src/libkeymap/summary.c**: Removed casts (5 instances)
  - All `ioctl()` calls with `KDSKBENT`, `KDGKBENT` cleaned up

**Why this matters**: Casting pointers to `unsigned long` then passing to variadic ioctl() breaks Fil-C's pointer capability tracking. The ioctl() syscall expects actual pointers, not integer representations.

### Keymap file changes (381 lines - NOT Fil-C related)
Multiple keymap data files modified:
- Changed `BackSpace` to `Delete` in various layouts
- Changed `Delete` to `Remove` in some keycodes
- Uncommented Hard Sign mappings in `ru1.map`
- These appear to be keymap correctness fixes, unrelated to Fil-C

Affected files:
- `i386/dvorak/dvorak-*.map` (2 files)
- `i386/fgGIod/tr_f-latin5.map`
- `i386/qwerty/lt*.map, no-latin1.map, ru*.map, se*.map, tr*.map, ua*.map` (15+ files)

---

## Keyutils 1.6.3

Complete syscall integration with Fil-C's syscall validation layer. All kernel key management syscalls replaced with Fil-C wrappers.

### Fil-C Compatibility Changes

### Syscall wrapper integration (keyutils.c)
- **add_key()**: Changed from `syscall(__NR_add_key, ...)` to `zsys_add_key(...)`
- **request_key()**: Changed to `zsys_request_key(...)`
- **keyctl()**: Major refactoring
  - Removed variadic argument handling (`va_list`, `va_arg`)
  - Changed to: `return *(long*)zcall(zsys_keyctl, zargs());`
  - Uses Fil-C's `zcall` mechanism for syscall validation

### Specialized keyctl operations
All keyctl DH/PKI operations now use dedicated Fil-C wrappers:
- **keyctl_dh_compute()**: → `zsys_keyctl_dh_compute()`
- **keyctl_dh_compute_kdf()**: → `zsys_keyctl_dh_compute_kdf()`
- **keyctl_pkey_query()**: → `zsys_keyctl_pkey_query()`
- **keyctl_pkey_encrypt()**: → `zsys_keyctl_pkey_encrypt()`
- **keyctl_pkey_decrypt()**: → `zsys_keyctl_pkey_decrypt()`
- **keyctl_pkey_sign()**: → `zsys_keyctl_pkey_sign()`
- **keyctl_pkey_verify()**: → `zsys_keyctl_pkey_verify()`

Added `#include <pizlonated_syscalls.h>` for wrapper declarations.

### Build system changes (Makefile)
- **Install target split**:
  - New `install-optfil` target: installs headers/libraries/binaries only
  - Original `install` target: depends on `install-optfil` + installs config files
  - Moved `keyutils.h` installation to `install-optfil` (from `install`)
  - Reason: Allows building without installing system configuration

### Code cleanup (keyctl_watch.c)
- Removed unused `after_eq()` inline function
  - Was defined but never called
  - Dead code removal

---

## Kerberos 5 1.21.3

Linker flag fix and memory fence integration for embedded libev event loop.

### Fil-C Compatibility Changes

### Build system fix (src/config/shlib.conf)
- **Version script linker flag**:
  - Changed: `-Wl,--version-script binutils.versions`
  - To: `--version-script=binutils.versions`
  - Removes `-Wl,` prefix (linker wrapper prefix)
  - Uses direct linker flag syntax

**Why**: Fil-C's linker integration expects direct linker flags, not gcc wrapper format.

### Event loop memory fences (src/util/verto/ev.c)
- **Added includes**:
  - `#include <stdfil.h>` (Fil-C primitives)
  
- **Memory fence definitions**:
  - `#define ECB_MEMORY_FENCE zfence()`
  - `#define ECB_MEMORY_FENCE_ACQUIRE zfence()`
  - `#define ECB_MEMORY_FENCE_RELEASE zfence()`
  
- **Purpose**: Replace libev's inline assembly memory barriers with Fil-C fence primitive
  - libev uses platform-specific atomic/fence operations
  - Fil-C doesn't support inline assembly
  - `zfence()` provides full memory barrier for all fence types

**Context**: This is part of the embedded libev event loop library in the Verto event abstraction layer used by Kerberos.

---

## LFS Bootscripts 20240825

System configuration changes for debugging and runtime directory setup - not Fil-C compatibility per se, but operational requirements.

### Fil-C Compatibility Changes

**Note**: These aren't technically Fil-C compatibility changes, but operational/debugging configuration for running Fil-C binaries in LFS environment.

### Runtime directory creation (lfs/init.d/mountvirtfs)
- **Added**: `mkdir -m 1777 /run/user || failed=1`
- Creates `/run/user` with sticky bit + full permissions (1777)
- Standard location for user-specific runtime files
- Required by many modern applications (systemd convention)

### Core dump configuration (lfs/lib/services/init-functions)
- **Added**: `ulimit -c unlimited`
- Enables unlimited core dump size
- Critical for debugging Fil-C programs
- Allows full memory dumps when programs crash

---

## libarchive 3.7.4

Minimal patch to support Fil-C's tagged pointer system in red-black tree implementation and pointer queue. Changes pointer-in-integer pattern to use tagged pointer operations and fixes type misuse in circular deque.

### Fil-C Compatibility Changes

**archive_rb.c/h (Red-Black Tree with Tagged Pointers)**:
- Changed `rb_info` from `uintptr_t` to `struct archive_rb_node *` in header
- Low 2 bits of `rb_info` used for flags (position, red/black color) while upper bits store parent pointer
- Added `<stdfil.h>` include
- Added `(uintptr_t)` casts when extracting integer value from pointer
- Replaced bitwise operations with tagged pointer operations:
  - `RB_SET_FATHER`: Uses `zretagptr(father, rb_info, ~RB_FLAG_MASK)` to preserve low bits while replacing pointer
  - `RB_MARK_RED`: Uses `zorptr(rb_info, RB_FLAG_RED)` to set red flag
  - `RB_MARK_BLACK`: Uses `zandptr(rb_info, ~RB_FLAG_RED)` to clear red flag
  - `RB_INVERT_COLOR`: Uses `zxorptr(rb_info, RB_FLAG_RED)` to toggle color
  - `RB_SET_POSITION`, `RB_ZERO_PROPERTIES`, `RB_COPY_PROPERTIES`, `RB_SWAP_PROPERTIES`: Similar tagged pointer operations

**archive_read_support_format_rar5.c (Pointer Queue)**:
- Changed `struct cdeque::arr` from `size_t*` to `void**`
- Removed cast `(size_t)` when storing pointer: `d->arr[d->end_pos] = item` instead of `d->arr[d->end_pos] = (size_t)item`
- Fixes anti-pattern of storing pointers as integers

---

## libdrm 2.4.122

DRM library passes pointers to kernel via ioctl in uint64_t fields. Patch adds pointer table to encode pointers for kernel and decode on return. Most conversions are one-way since kernel doesn't return pointers.

### Fil-C Compatibility Changes

**xf86drmMode.c (Pointer Table for Kernel Ioctls)**:
- Added `<stdfil.h>` include
- Created static `zexact_ptrtable* ptrtable` with constructor to initialize: `zexact_ptrtable_new()`
- Redefined macros:
  - `U642VOID(x)`: `zexact_ptrtable_decode(ptrtable, (unsigned long)(x))`
  - `VOID2U64(x)`: `zexact_ptrtable_encode(ptrtable, (x))`
  - Added `VOID2U64_ONEWAY(x)`: `(uint64_t)(unsigned long)(x)` - for pointers sent to kernel but never decoded
- Comment notes: "DRM ioctls are a safety escape hatch, since we're passing a buffer to the kernel that has pointers in it"
- Changed most `VOID2U64` calls to `VOID2U64_ONEWAY` since kernel doesn't return these pointers:
  - `drmModeDirtyFB`: clips_ptr
  - `drmModeSetCrtc`: set_connectors_ptr
  - `_drmModeGetConnector`: modes_ptr (stack_mode address)
  - `drmModeCrtcGetGamma/SetGamma`: red/green/blue pointers
  - `drmModeAtomicCommit`: objs_ptr, count_props_ptr, props_ptr, prop_values_ptr
  - `drmModeListLessees/drmModeGetLease`: lessees_ptr/objects_ptr
- Only `atomic.user_data` uses bidirectional `VOID2U64` (line 107)

---

## libedit 20240808-3.1

Trivial one-line patch to skip ISO 10646 compatibility check on Linux. Not Fil-C specific, just a Linux portability fix.

### Fil-C Compatibility Changes

**src/chartype.h**:
- Added `!defined(__linux__)` to existing platform check for `__STDC_ISO_10646__`
- Existing check already excludes macOS, OpenBSD, FreeBSD, DragonFly
- Comment explains: "first 127 code points are ASCII compatible, so ensure wchar_t indeed does ISO 10646"
- Not actually Fil-C-specific - just standard Linux portability

---

## libevdev 1.11.0

Replaces GCC section attributes for test discovery with constructor functions and linked list. Changes symbol versioning linker flag to Fil-C format.

### Fil-C Compatibility Changes

**meson.build (Symbol Versioning)**:
- Changed `-Wl,--version-script` to `--version-script` (Fil-C linker doesn't use `-Wl,` prefix)

**test/test-common.h & test/test-main.c (Test Registration)**:
- Removed `__start_test_section`/`__stop_test_section` linker symbols
- Added `const struct libevdev_test *first_test` global
- Added `next_test` pointer to `struct libevdev_test` for linked list
- Changed `_TEST_SUITE` macro:
  - Removed `__attribute__((section ("test_section")))`
  - Added constructor function `register_##name()` that:
    - Allocates test struct with `malloc()`
    - Populates name, setup function, privileges flag
    - Prepends to `first_test` linked list
- Changed test iteration from section iteration to linked list traversal:
  - `for (t = &__start_test_section; t < &__stop_test_section; t++)` 
  - → `for (t = first_test; t; t = t->next_test)`
- Added `#include <stdlib.h>` for malloc

---

## libevent 2.1.12

Mostly test adjustments: disables flaky tests and fixes function pointer cast. Minimal Fil-C compatibility work.

### Fil-C Compatibility Changes

**test/regress_http.c (Disabled Tests)**:
- Added `HTTPS_SKIP` macro: `TT_ISOLATED|TT_OFF_BY_DEFAULT`
- Changed to `HTTPS_SKIP` for:
  - `https_incomplete`
  - `https_incomplete_timeout`
  - `https_chunk_out`
- These tests likely have timing/behavior differences under Fil-C

**test/regress_ssl.c (Disabled Tests)**:
- Added `TT_OFF_BY_DEFAULT` flag to:
  - `bufferevent_socketpair_dirty_shutdown`
  - `bufferevent_renegotiate_socketpair_dirty_shutdown`
  - `bufferevent_socketpair_startopen_dirty_shutdown`
- Dirty shutdown tests probably interact badly with Fil-C's safety checks

**test/regress_main.c (Function Pointer Cast)**:
- Changed `data->legacy_test_fn()` to cast through intermediate variable:
  ```c
  void (*fn)(void* arg) = (void (*)(void*))data->legacy_test_fn;
  fn(NULL);
  ```
- Fil-C requires explicit function pointer type matching

---

## libffi 3.4.6

Substantial Fil-C port implementing FFI with zclosure system, custom calling convention, and stack-based marshaling. Replaces assembly trampolines with Fil-C closures. Includes test files and documentation.

### Fil-C Compatibility Changes

**Makefile.am & configure.host (Build Configuration)**:
- Changed `-Wl,--version-script` to `--version-script`
- Hardcoded `SOURCES=ffi64.c` in configure.host (forces x86_64 backend)

**src/closures.c (Closure Implementation)**:
- Wrapped entire original implementation in `#ifndef __FILC__`
- Fil-C implementation:
  - `ffi_closure_alloc`: Uses `zclosure_new(ffi_closure_callback, NULL)` instead of mmap
  - `ffi_closure_free`: No-op (GC handles cleanup)
  - `ffi_tramp_is_present`: Returns 0
- No executable memory needed - closures use Fil-C's native closure system

**src/x86/ffi64.c (x86-64 Backend)**:
- Added `FFI_FILC` ABI enum value (aliased to `FFI_UNIX64` for compatibility)
- Added `is_filc` static bool flag
- Stack-based calling in `ffi_call_int`:
  - Allocates stack with `alloca(cif->bytes)`
  - Marshals arguments sequentially with alignment
  - Calls via `zcall(fn, stack)` instead of `ffi_call_unix64` assembly
  - Return value copied from `zcall` result
- Modified `ffi_prep_cif_machdep`:
  - Forces all arguments to stack (bypasses register classification)
  - `if (is_filc || examine_argument(...))` - always takes stack path
- Closure callback `ffi_closure_callback` (Fil-C only):
  - Gets closure data: `zcallee_closure_data()`
  - Gets arguments: `zargs()`
  - Unmarshals from stack to avalue array
  - Calls user function
  - Returns via `zreturn(rvalue)`

**src/x86/ffitarget.h (ABI Definition)**:
- Conditional ABI enum for `__FILC__`:
  ```c
  #if defined(__FILC__)
    FFI_FILC,
    FFI_UNIX64 = FFI_FILC,
    FFI_DEFAULT_ABI = FFI_FILC
  ```
- Disabled `FFI_GO_CLOSURES` for Fil-C

**src/x86/ffi64.c (Prep CIF)**:
- Disabled EFI64/GNUW64 ABI support under Fil-C
- Only allows `FFI_FILC` ABI

---

## libinput 1.29.1

Similar to libevdev: replaces linker sections with constructor-based registration for test devices and collections. Symbol versioning flag change.

### Fil-C Compatibility Changes

**meson.build (Symbol Versioning)**:
- Changed `-Wl,--version-script` to `--version-script`

**test/litest.h & test/litest-main.c (Test Device Registration)**:
- Removed `__start_test_device_section`/`__stop_test_device_section` symbols
- Added `struct test_device *first_test_device` global
- Added `next_test_device` pointer to `struct test_device`
- Changed `TEST_DEVICE` macro:
  - Removed `__attribute__((section ("test_device_section")))`
  - Added constructor `register_##which()`:
    - `malloc(sizeof(struct test_device))`
    - Prepends to `first_test_device` linked list
- Changed `TEST_COLLECTION` macro similarly:
  - Removed `__attribute__((section ("test_collection_section")))`
  - Added constructor with malloc and linked list prepend
- Updated iteration loops:
  - `for (t = &__start_test_device_section; t < &__stop_test_device_section; t++)`
  - → `for (t = first_test_device; t; t = t->next_test_device)`
  - Same for test collections
- Added `#include <stdlib.h>` for malloc

---

## libpng 1.6.43

This patch adds APNG (Animated PNG) support. **NOT Fil-C specific** - it's a feature addition, not a compatibility fix. Unclear why it's in the Fil-C patches.

### Fil-C Compatibility Changes

**None** - this patch has no Fil-C-specific changes.

---

## libuev 2.4.1

No actual Fil-C compatibility changes. After filtering autotools artifacts, the remaining patch contains Debian packaging, documentation, and an autogen script.

### Fil-C Compatibility Changes

None.

---

## libuv v1.48.0

Moderate Fil-C port: disables io_uring, adds signal safety, uses pointer tables for signal handlers, fixes string length calculation, and disables problematic tests.

### Fil-C Compatibility Changes

**src/unix/linux.c (Disable io_uring)**:
- Added `#elif defined(__FILC__)` returning 0 in `uv__use_io_uring()`
- Comment: "The io_uring API is not yet supported by Fil-C, and may never be."
- Fallback to traditional epoll/poll

**src/unix/process.c (Signal Safety)**:
- Added `#include <stdfil.h>`
- Signal setup loop skips unsafe signals:
  ```c
  if (n == SIGKILL || n == SIGSTOP || zis_unsafe_signal_for_handlers(n))
    continue;
  ```
- Fil-C runtime function checks signal compatibility

**src/unix/signal.c (Signal Handler Pointer Table)**:
- Added `#include <stdfil.h>`
- Created `zexact_ptrtable* handle_table` with constructor: `zexact_ptrtable_new_weak()`
- Signal handler encodes pointer:
  ```c
  msg.handle = (void*)zexact_ptrtable_encode(handle_table, handle);
  ```
- Event loop decodes pointer:
  ```c
  handle = zexact_ptrtable_decode(handle_table, (uintptr_t)msg->handle);
  ```
- Necessary because signal handlers can't safely pass pointers through non-async-signal-safe mechanisms

**src/unix/proctitle.c (Process Title Length)**:
- Added `#include <stdfil.h>`
- Changed capacity calculation:
  ```c
  // Old: pt.cap = argv[i - 1] + size - argv[0];
  // New: pt.cap = zlength(pt.str);
  ```
- Uses Fil-C's `zlength()` instead of pointer arithmetic on argv array

**test/test-process-priority.c (Disabled Test)**:
- Commented out PID 0/getpid equivalence check with FIXME:
  ```c
  // FIXME: On Fil-C, this fails, most likely due to the main thread hack we do.
  //ASSERT_OK(uv_os_getpriority(uv_os_getpid(), &r));
  //ASSERT_EQ(priority, r);
  ```

**test/test-thread-priority.c (Disabled Test)**:
- Commented out nice value test on Linux:
  ```c
  // FIXME: Why isn't the Fil-C runtime getting this right?
  ```

**test/test-thread.c (Stack Size Check)**:
- Added `&& !defined(__FILC__)` to Linux/glibc stack size check
- Fil-C thread stacks may not match glibc behavior

**test/test-timer.c (Disabled Test)**:
- Commented out entire `timer_run_once` test body
- Comment: "This has a flaky failure where the second uv_run call returns 1 in Fil-C."

---

## libxcrypt 4.4.36

Minimal patch: disables SIMD and uses Fil-C symbol versioning directive.

### Fil-C Compatibility Changes

**lib/alg-yescrypt-opt.c (Disable SIMD)**:
- Added `#undef __SSE2__` and `#undef __SSE__` after includes
- Prevents SSE optimizations in yescrypt/scrypt/gost_yescrypt implementations
- Fil-C likely doesn't support SIMD intrinsics or they cause issues

**lib/crypt-port.h (Symbol Versioning)**:
- Changed `.symver` to `.filc_symver` in inline assembly:
  ```c
  // Old: __asm__ (".symver " #intname "," extstr "@" #version)
  // New: __asm__ (".filc_symver " #intname "," extstr "@" #version)
  ```
- Applies to both `_symver_ref` (compatibility symbols) and `symver_set` macros
- Fil-C linker uses different symbol versioning directive

---

## libxkbcommon xkbcommon-1.11.0

Trivial patch changing symbol versioning linker flag format across all libraries.

### Fil-C Compatibility Changes

**meson.build (Symbol Versioning Everywhere)**:
- Changed linker probe test:
  - Old: `-Wl,--version-script=@meson_test_map@`
  - New: `--version-script=@meson_test_map@`
  - Updated variable name: `have_version_script`
- Changed link args for three libraries:
  - **libxkbcommon**: `--version-script=@xkbcommon_map@`
  - **libxkbcommon-x11**: `--version-script=...xkbcommon-x11.map`
  - **libxkbregistry**: `--version-script=...xkbregistry.map`
- Fil-C linker accepts `--version-script` directly without `-Wl,` wrapper

---

## libxml2 v2.14.4

Minimal patch adding atomic qualifier to one catalog entry field for Fil-C thread safety.

### Fil-C Compatibility Changes

- **catalog.c**: Changed `struct _xmlCatalogEntry *children` to `struct _xmlCatalogEntry *_Atomic children` (line 10) to ensure atomic access to the children field in catalog entry structures

---

## Linux Kernel v6.10.5

Large refactoring of VMware graphics drivers and kernel utility code with Fil-C compatibility changes to pointer arithmetic and red-black tree implementation.

### Fil-C Compatibility Changes

### VMware Graphics Driver (vmwgfx)
- Major simplification: removed dumb buffer surface tracking, detached resource management
- Removed XArray-based resource tracking
- Simplified buffer release paths

### Kernel Utilities (tools/)
- **tools/include/linux/compiler.h**: Replaced type-punning `__may_alias__` casts with `zmemmove()` for safe memory copying
- **tools/include/linux/rbtree.h**: Changed `__rb_parent_color` from `unsigned long` to `struct rb_node *` pointer
- **tools/include/linux/rbtree_augmented.h**: Added casts to `unsigned long` when extracting color bits from pointer
- **tools/lib/rbtree.c**: Updated pointer arithmetic to use pointer types directly

---

## Lua v5.4.7

Simple build configuration changes to remove readline dependency and add debug symbols.

### Fil-C Compatibility Changes

None - these are build configuration changes, not code adaptations.

---

## m4 v1.4.19

Comprehensive Fil-C compatibility changes across library code plus test suite adjustments.

### Fil-C Compatibility Changes

### Core Library Modifications
- **lib/fpucw.h**: Add Fil-C FPU control word functions
  - `#ifdef __FILC__` block includes `pizlonated_math.h`
  - Replace inline asm `GET_FPUCW()`/`SET_FPUCW()` with `zmath_getcw()`/`zmath_setcw()`

- **lib/obstack.h**: Fix pointer alignment macro
  - Include `<inttypes.h>` and `<stdfil.h>`
  - Change `__BPTR_ALIGN` to use `zmkptr()` for safe pointer arithmetic

- **lib/sigsegv.in.h**: Disable stack overflow recovery under Fil-C
  - Add `&& !defined __FILC__` to `HAVE_STACK_OVERFLOW_RECOVERY` check

### Macro Processing
- **src/macro.c**: Use `zmkptr()` for argv pointer calculation

### Test Suite Adjustments
- **checks/006.command_li**: Deleted (tests closed stdout, problematic for Fil-C)
- **checks/198.sysval**: Deleted (tests signal handling with kill -9)
- **tests/test-calloc-gnu.c**: Skip allocation size checks under `__FILC__`
- **tests/test-explicit_bzero.c**: Skip freed memory checks under `__FILC__`
- **tests/test-free.c**: Skip max_map_count test under `__FILC__`
- **tests/test-malloc-gnu.c**: Skip PTRDIFF_MAX allocation test under `__FILC__`
- **tests/test-posix_spawn-script.c**: Mark test as flaky and skip
- **tests/test-realloc-gnu.c**: Skip PTRDIFF_MAX reallocation test under `__FILC__`
- **tests/test-reallocarray.c**: Skip size limit tests under `__FILC__`
- **tests/test-sigsegv-catch-segv1.c**: Disable under `__FILC__`
- **tests/test-sigsegv-catch-segv2.c**: Disable under `__FILC__`
- **tests/test-spawn-pipe.sh**: Reduce test iterations from 0-7 to exclude 3 and 7

---

## GNU Make v4.4.1

Single targeted bounds check added to prevent out-of-bounds access when parsing environment variables.

### Fil-C Compatibility Changes

- **src/expand.c**: 
  - Include `<stdfil.h>` header
  - Add `zinbounds(&(*ep)[nl])` check before accessing `(*ep)[nl]` when iterating environment variables
  - Prevents potential out-of-bounds access when checking for `=` separator in environment strings

---

## man-db v2.12.1

Removes unsafe integer-to-pointer cast in filesystem I/O control call.

### Fil-C Compatibility Changes

- **lib/orderfiles.c**: Changed `ioctl(fd, FS_IOC_FIEMAP, (unsigned long) &fm)` to `ioctl(fd, FS_IOC_FIEMAP, &fm)`
  - Removes unnecessary and unsafe cast from pointer to `unsigned long` and back
  - FIEMAP ioctl expects a pointer to struct, no cast needed

---

## OpenSSH v9.8p1

Minimal seccomp filter adjustment to allow scheduler yield syscall needed by Fil-C runtime.

### Fil-C Compatibility Changes

- **sandbox-seccomp-filter.c**: Add `SC_ALLOW(__NR_sched_yield)` to pre-authentication syscall allow-list
  - Fil-C's garbage collector or runtime likely requires `sched_yield()` for cooperative scheduling
  - Added conditionally with `#ifdef __NR_sched_yield` guard

---

## OpenSSL v3.3.1

Comprehensive Fil-C adaptation: linker flag fixes and extensive C wrappers for assembly AES functions with bounds checking via Fil-C safety primitives.

### Fil-C Compatibility Changes

### Build System
- **Configurations/shared-info.pl**: Remove `-Wl,` prefix from `--version-script=` linker flags (lines 9, 18)
  - Fil-C linker expects bare `--version-script=` format

### Assembly Function Wrappers (New Files)
Created extensive C wrapper layers for assembly-optimized AES functions:

- **crypto/aes/aes_asm_forward.c**: Wrappers for generic AES assembly
  - `AES_set_encrypt_key()`, `AES_set_decrypt_key()`, `AES_encrypt()`, `AES_decrypt()`, `AES_cbc_encrypt()`
  - Use `zcheck_readonly()`, `zcheck()`, `zunsafe_buf_call()`, `zunsafe_fast_call()`

- **crypto/aes/aesni_asm_forward.c**: Wrappers for AES-NI assembly (181 lines)
  - `aesni_*` functions: set_encrypt_key, encrypt, ecb_encrypt, cbc_encrypt, ocb_encrypt/decrypt, ctr32_encrypt_blocks, xts_encrypt/decrypt, ccm64_*
  - Includes `l_size()` helper for OCB buffer size calculation

- **crypto/aes/aesni_mb_asm_forward.c**: Multi-block AES wrapper
  - `aesni_multi_cbc_encrypt()` with descriptor array validation

- **crypto/aes/aesni_sha1_asm_forward.c**: AES+SHA1 stitched implementation
  - `aesni_cbc_sha1_enc()`

- **crypto/aes/aesni_sha256_asm_forward.c**: AES+SHA256 stitched
  - `aesni_cbc_sha256_enc()`

- **crypto/aes/bsaes_asm_forward.c**: Bit-sliced AES wrappers
  - `ossl_bsaes_*` functions: cbc_encrypt, ctr32_encrypt_blocks, xts_encrypt/decrypt

- **crypto/aes/vpaes_asm_forward.c**: Vector-permute AES wrappers
  - `vpaes_set_encrypt_key()`, `vpaes_set_decrypt_key()`, `vpaes_encrypt()`, `vpaes_decrypt()`, `vpaes_cbc_encrypt()`

### Build Integration
- **crypto/aes/build.info**: Updated to compile new wrapper files alongside assembly
  - Changed from bare assembly references to pairs like `aes_asm_forward.c aes-x86_64.s`

### Provider Code Updates
- **cipher_aes_gcm_hw_aesni.inc**: Add `#include <stdfil.h>`
- **cipher_aes_gcm_hw_vaes_avx512.inc**: Convert function declarations to static inline wrappers with bounds checking
  - `ossl_vaes_vpclmulqdq_capable()`, `ossl_aes_gcm_*_avx512()`, `ossl_gcm_gmult_avx512()`
  - All use `zcheck()`, `zcheck_readonly()`, `zunsafe_*_call()` patterns

### Random Seeding
- **rand_cpu_x86.c**: Add `#include <stdfil.h>` for RDRAND/RDSEED support

### Disabled Tests
Deleted test files that are incompatible with Fil-C:
- **test/recipes/01-test_symbol_presence.t**: Symbol checking via nm (242 lines)
- **test/recipes/04-test_param_build.t**: Parameter building tests
- **test/recipes/30-test_afalg.t**: AF_ALG engine tests
- **test/recipes/90-test_secmem.t**: Secure memory tests
- **test/recipes/90-test_shlibload.t**: Shared library loading tests (75 lines)

---

## p11-kit v0.25.5

Simple linker flag adjustment for Fil-C compatibility in Meson build files.

### Fil-C Compatibility Changes

- **p11-kit/meson.build**: 
  - Line 9: Change `'-Wl,--version-script,' + libp11_kit_symbol_map` to `'--version-script=' + libp11_kit_symbol_map`
  - Line 19: Change `'-Wl,--version-script,' + p11_module_symbol_map` to `'--version-script=' + p11_module_symbol_map`
  - Fil-C linker expects version script flags without `-Wl,` wrapper

---

## PCRE2 10.44

Minimal actual changes: one test disabled. The patch is 99% build artifact bloat from autotools-generated files.

### Fil-C Compatibility Changes

**RunGrepTest** - Test 150 disabled (locale test)
- Skips `which locale` test that checks LC_CTYPE=badlocale behavior
- Change appears defensive, not required by Fil-C semantics

---

## Perl 5.40.0

Comprehensive Fil-C integration across Perl's XS (eXtension System) interface. Replaces all pointer-to-integer conversions with zptrtable encoding to maintain capability tracking.

### Fil-C Compatibility Changes

### Core Infrastructure
**perl.c** / **perl.h**
- Global `Perl_xsub_ptrtable` declared and initialized
- Constructor creates pointer table for all XS modules to share
- Includes `<stdfil.h>` at top level

### XS Module Modifications
Each XS module creates its own pointer table and converts PTR2IV ↔ INT2PTR:

**builtin.c**
- `builtin_ptrtable` for encoding `BuiltinFuncDescriptor*`
- Used in `ck_builtin_const`, `ck_builtin_func1`, `ck_builtin_funcN`

**Encode.xs** (`cpan/Encode/`)
- `encode_ptrtable` for `encode_t*` encoding
- Affects encode/decode operations across character sets

**Compress-Raw-Zlib/typemap**
- Converts typemap `INT2PTR` → `zptrtable_decode(Perl_xsub_ptrtable, ...)`

**Storable.xs** (`dist/Storable/`)
- `perinterp_ptrtable` for per-interpreter context encoding
- Complex macro rewrites for `dSTCXT_PTR`, `INIT_STCXT`, `SET_STCXT`

**threads-shared/shared.xs**
- `sharedsv_ptrtable` for shared SV encoding
- `SHAREDSV_FROM_OBJ` macro rewritten

**threads.xs** (`dist/threads/`)
- `threads_ptrtable` for thread management
- Affects `ithread_mg_get`, `S_ithread_to_SV`, `S_SV_to_ithread`, etc.

### Directory Handle Management
**doio.c**
- `dir_ptrtable` for `DIR*` encoding in ARGV processing
- `S_argvout_free`, `Perl_nextargv`, `S_argvout_final` updated

### Introspection (B::)
**ext/B/B.xs** + **typemap**
- All OP/SV/MAGIC pointer operations use `Perl_xsub_ptrtable`
- Affects `make_op_object`, `make_sv_object`, `make_mg_object`, etc.
- All `T_OP_OBJ`, `T_SV_OBJ`, `T_MG_OBJ` conversions rewritten

### DynaLoader
**ext/DynaLoader/dl_dlopen.xs**
- `dl_load_file`, `dl_find_symbol` encode dlopen handles

### Regex Engine
**ext/re/re.xs**
- Encodes `my_reg_engine` pointer

### GV/Stash Cache
**gv.c**
- `gvstash_ptrtable` for stash cache (`PL_stashcache`)
- `Perl_gv_stashsvpvn_cached` encodes HV* pointers

### Regex Context Saving
**pp_ctl.c**
- `rxres_save`/`rxres_restore`/`rxres_free` rewritten
- Uses `*(void**)` casts instead of `PTR2UV`/`INT2PTR` for match buffers

### Regex Engine Dispatch
**regcomp.c**
- `Perl_current_re_engine` decodes from `cop_hints_fetch_pvs`

### Public API
**sv.c**
- `Perl_sv_setref_pv` uses `zptrtable_encode` for blessed references

### Performance Optimization
**util.c**
- `Perl_repeatcpy` loop replaced with `memcpy` (unrelated optimization)

### Typemap Defaults
**lib/ExtUtils/typemap**
- Default `T_PTR`, `T_PTRREF`, `T_PTROBJ` conversions use `Perl_xsub_ptrtable`
- Affects all XS modules using standard typemaps

---

## procps-ng 4.0.4

Single defensive fix for variadic argument handling that could cause undefined behavior.

### Fil-C Compatibility Changes

### library/pids.c - `pids_oldproc_open`
```c
-    int *ids;
+    int *ids = NULL;
     int num = 0;
 
     if (*this == NULL) {
         va_start(vl, flags);
-        ids = va_arg(vl, int*);
+        if (flags & (PROC_PID | PROC_UID)) ids = va_arg(vl, int*);
         if (flags & PROC_UID) num = va_arg(vl, int);
```

**Why this matters:**
- Original code unconditionally read `int*` from varargs
- If `flags` doesn't indicate PID or UID filtering, the `ids` argument may not exist
- Reading non-existent variadic argument is undefined behavior
- Fil-C runtime may trap on invalid va_arg access

**Impact:**
- Defensive programming - prevents reading past end of va_list
- Also initializes `ids = NULL` to avoid uninitialized variable

---

## QuickJS (no version in patch)

Minimal changes to make QuickJS work with Fil-C: disable threaded dispatch, fix pointer tagging, add qsort_r compatibility.

### Fil-C Compatibility Changes

### Makefile
```make
+CONFIG_CLANG=y
-  HOST_CC=clang
-  CC=$(CROSS_PREFIX)clang
+  HOST_CC=$(PWD)/../../../build/bin/clang
+  CC=$(CROSS_PREFIX)$(PWD)/../../../build/bin/clang
```
**Hardcodes Fil-C compiler path** - should use environment variable instead

### Interpreter Dispatch (quickjs.c)
```c
-#if defined(EMSCRIPTEN)
+#if defined(EMSCRIPTEN) || defined(__PIZLONATOR_WAS_HERE__)
 #define DIRECT_DISPATCH  0
```
**Disables computed goto dispatch** - Fil-C doesn't support `&&label` address-of-label extension

### Property Autoinit (quickjs.c)
**Problem:** `realm_and_id` stored `JSContext*` with 2-bit ID tag in low bits

```c
 typedef struct JSProperty {
     union {
         struct {
-            uintptr_t realm_and_id;
+            void* realm_and_id;
             void *opaque;
         } init;
     } u;
 } JSProperty;
```

**Helper functions:**
```c
 static JSContext *js_autoinit_get_realm(JSProperty *pr) {
-    return (JSContext *)(pr->u.init.realm_and_id & ~3);
+    return (JSContext *)((uintptr_t)pr->u.init.realm_and_id & ~3);
 }
 
 static JSAutoInitIDEnum js_autoinit_get_id(JSProperty *pr) {
-    return pr->u.init.realm_and_id & 3;
+    return (uintptr_t)pr->u.init.realm_and_id & 3;
 }
```

**Setting:**
```c
-    pr->u.init.realm_and_id = (uintptr_t)JS_DupContext(ctx);
-    pr->u.init.realm_and_id |= id;
+    pr->u.init.realm_and_id = JS_DupContext(ctx);
+    pr->u.init.realm_and_id = (void*)((uintptr_t)pr->u.init.realm_and_id | id);
```

**Pattern:** Store as `void*`, cast to `uintptr_t` for bit manipulation, cast back

### qsort_r Compatibility (cutils.c)
```c
+#ifdef __PIZLONATOR_WAS_HERE__
+void rqsort(void *base, size_t nmemb, size_t size,
+            int (*cmp)(const void *, const void *, void *),
+            void *arg)
+{
+    qsort_r(base, nmemb, size, cmp, arg);
+}
```
**Wrapper for BSD-style qsort_r** (used elsewhere in QuickJS)

### Headers
```c
+#include <stdfil.h>
```

---

## seatd 0.9.1

Trivial change to pass version script directly to linker instead of through `-Wl,`.

### Fil-C Compatibility Changes

### meson.build
```diff
-symbols_flag = '-Wl,--version-script,@0@/@1@'.format(meson.current_source_dir(), symbols_file)
+symbols_flag = '--version-script=@0@/@1@'.format(meson.current_source_dir(), symbols_file)
```

**Explanation:**
- `-Wl,` is GCC/Clang syntax for passing flags to linker
- Fil-C compiler may invoke linker directly, requiring bare flag
- Also changed `,` separator to `=` (more portable)

**Impact:** Build system compatibility, not a code change

---

## sed 4.9

Disabled gnulib test assumptions about memory behavior and fixed pointer arithmetic in obstack allocator.

### Fil-C Compatibility Changes

### Gnulib Tests - Disabled Under Fil-C

**gnulib-tests/test-explicit_bzero.c**
```c
+#ifndef __FILC__
   if (is_range_mapped (addr, addr + SECRET_SIZE))
+#endif
```
**Issue:** Test checks if freed memory is still mapped - Fil-C may not unmap freed regions

**gnulib-tests/test-free.c**
```c
-  #if defined __linux__ && !(__GLIBC__ == 2 && __GLIBC_MINOR__ < 15)
+  #if defined __linux__ && !(__GLIBC__ == 2 && __GLIBC_MINOR__ < 15) && !defined __FILC__
```
**Issue:** Test tries to exhaust virtual memory - undefined under GC

**gnulib-tests/test-malloc-gnu.c**
```c
+#ifndef __FILC__
   if (PTRDIFF_MAX < SIZE_MAX) {
     size_t one = 1;
     p = malloc (PTRDIFF_MAX + one);
+#endif
```
**Issue:** Tests that malloc fails for huge allocations - Fil-C may have different limits

**gnulib-tests/test-realloc-gnu.c** - Same pattern

**gnulib-tests/test-reallocarray.c**
```c
+#ifndef __FILC__
   for (size_t n = 2; n != 0; n <<= 1) {
     if (SIZE_MAX / n + 1 <= PTRDIFF_MAX) {
       p = reallocarray (NULL, PTRDIFF_MAX / n + 1, n);
+#endif
```
**Issue:** Tests allocation overflow detection

### Obstack Pointer Alignment (lib/obstack.h)
**Original (broken for capabilities):**
```c
#define __BPTR_ALIGN(B, P, A) ((B) + (((P) - (B) + (A)) & ~(A)))
```

**Fixed:**
```c
+#include <stdfil.h>
+#include <inttypes.h>

 #define __BPTR_ALIGN(B, P, A)                                            \
   __extension__                                                          \
     ({ char *__P = (char *) (P);                                         \
        zmkptr(__P, (uintptr_t)((B) + ((__P - (B) + (A)) & ~(A)))); })
```

**Why this matters:**
- Original macro does `(B) + offset` where both B and offset are expressions
- If B is a pointer, offset calculation loses capability
- `zmkptr(__P, offset)` creates new pointer from base `__P` with computed offset
- Preserves provenance through alignment operation

---

## simdutf 5.5.0

Minimal changes to enable CPU feature detection under Fil-C runtime.

### Fil-C Compatibility Changes

### include/simdutf/internal/isadetection.h

**CPUID detection:**
```c
-#elif defined(HAVE_GCC_GET_CPUID) && defined(USE_GCC_GET_CPUID)
+#elif (defined(HAVE_GCC_GET_CPUID) && defined(USE_GCC_GET_CPUID)) || defined(__PIZLONATOR_WAS_HERE__)
 #include <cpuid.h>
 #endif
+#ifdef __PIZLONATOR_WAS_HERE__
+#include <stdfil.h>
+#endif
```
**Forces GCC `__get_cpuid` path** instead of inline assembly

**cpuid() wrapper:**
```c
-#elif defined(HAVE_GCC_GET_CPUID) && defined(USE_GCC_GET_CPUID)
+#elif (defined(HAVE_GCC_GET_CPUID) && defined(USE_GCC_GET_CPUID)) || defined(__PIZLONATOR_WAS_HERE__)
   uint32_t level = *eax;
   __get_cpuid(level, eax, ebx, ecx, edx);
```

**xgetbv (AVX detection):**
```c
 static inline uint64_t xgetbv() {
  #if defined(_MSC_VER)
    return _xgetbv(0);
+ #elif defined(__PIZLONATOR_WAS_HERE__)
+   return zxgetbv();
  #else
    uint32_t xcr0_lo, xcr0_hi;
    asm volatile("xgetbv\n\t" : "=a" (xcr0_lo), "=d" (xcr0_hi) : "c" (0));
```

**Why needed:**
- Inline assembly (`asm volatile("cpuid")`) not supported in Fil-C
- `xgetbv` instruction reads XCR0 register (AVX enable bit)
- Fil-C provides `zxgetbv()` runtime helper for safe access

---

## SQLite (version not in patch, likely 3.x)

Substantial test harness modifications to encode pointers when passing to/from TCL, plus core changes to disable atomics and add custom build system.

### Fil-C Compatibility Changes

### Core Changes

**src/sqliteInt.h**
```c
-#if GCC_VERSION>=4007000 || __has_extension(c_atomic)
+#if (GCC_VERSION>=4007000 || __has_extension(c_atomic)) && !defined(__PIZLONATOR_WAS_HERE__)
 # define SQLITE_ATOMIC_INTRINSICS 1
```
**Disables GCC atomic builtins** - forces fallback implementation

### Test Infrastructure Pointer Encoding

**src/test1.c**
```c
+#ifdef __PIZLONATOR_WAS_HERE__
+static zptrtable* externalPtrTable;
+void* sqlite3EncodeExternalTestPtr(void *p) {
+  ensureExternalPtrTable();
+  return (void*)zptrtable_encode(externalPtrTable, p);
+}
+void* sqlite3DecodeExternalTestPtr(void *p) {
+  ensureExternalPtrTable();
+  return zptrtable_decode(externalPtrTable, (size_t)p);
+}
```

**Pattern used throughout test suite:**
```c
-  sqlite3_snprintf(sizeof(zBuf), zBuf, "%p", p->db);
+  sqlite3_snprintf(sizeof(zBuf), zBuf, "%p", sqlite3EncodeExternalTestPtr(p->db));
```

**Files affected:**
- **src/test1.c**: Main test harness, array addresses, text-to-pointer conversion
- **src/test2.c**: Pager test objects
- **src/test3.c**: B-tree test objects
- **src/test_blob.c**: Blob handles
- **src/test_malloc.c**: Memory test pointers (bidirectional encoding)
- **src/test_mutex.c**: Mutex handles
- **src/test_quota.c**: File handle pointers
- **src/test_syscall.c**: `va_arg` safety (`zcan_va_arg` for mremap)
- **ext/misc/carray.c**: C array test pointers

**Rationale:**  
TCL stores pointers as integers. When passing C pointers to TCL (for later retrieval), must encode to preserve capability. Decoding required when TCL returns pointer to C.

### TCL Test Detection

**src/test1.c**
```c
+#ifdef __PIZLONATOR_WAS_HERE__
+  res = 1;  /* Treat Fil-C like sanitizers for test purposes */
+#endif
```
**Makes tests behave as if running under ASan/MSan** (some checks disabled)

### Build System

**Makefile.filc** (115 lines)
- Custom non-autoconf Makefile
- Hardcodes Fil-C compiler path (bad practice)
- Enables SQLite features: `SQLITE_DEBUG`, `SQLITE_ENABLE_MATH_FUNCTIONS`, etc.
- Disables lookaside allocator: `SQLITE_OMIT_LOOKASIDE=1`

**main.mk**
```diff
-	mv sqlite3 /usr/bin
+	mv sqlite3 $(PREFIX)/bin
```
**Fixes install paths** to respect PREFIX

### Lemon Parser Generator

**tool/lemon.c**
```c
-  static int nolinenosflag = 0;
+  static int nolinenosflag = 1;
```
**Disables #line directives** (cleaner debugging under Fil-C?)

### Symbol Versioning

**src/sqliteInt.h**
```c
+  void *sqlite3EncodeExternalTestPtr(void*);
+  void *sqlite3DecodeExternalTestPtr(void*);
```
**Declares encoding functions for use across test modules**

---

## systemd 256.4

Major rework of sd-bus error map infrastructure to avoid ELF section magic, plus signal handling safety and build system fixes.

### Fil-C Compatibility Changes

### Build System (meson.build)
```diff
-                     '-Wl,--version-script=' + libsystemd_sym_path],
+                     '--version-script=' + libsystemd_sym_path],
```
**Repeated 3 times** for libsystemd, libudev, and NSS modules  
**Same as seatd** - removes `-Wl,` prefix

### Signal Handling Safety (src/basic/signal-util.c)
```c
+#include <stdfil.h>

 int reset_all_signal_handlers(void) {
     for (int sig = 1; sig < _NSIG; sig++) {
         if (IN_SET(sig, SIGKILL, SIGSTOP))
             continue;
 
+        if (zis_unsafe_signal_for_handlers(sig))
+            continue;
+
         r = RET_NERRNO(sigaction(sig, &sa, NULL));
```

**Why needed:**
- Some signals may be reserved by Fil-C runtime
- `zis_unsafe_signal_for_handlers` prevents systemd from clobbering them
- Avoids runtime conflicts

### ELF Section Magic Removal

**Original design:**
```c
#define BUS_ERROR_MAP_ELF_REGISTER                                      \
        _section_("SYSTEMD_BUS_ERROR_MAP")                              \
        _used_                                                          \
        _retain_
```
- Error maps placed in special ELF section
- Linker provides `__start_SYSTEMD_BUS_ERROR_MAP` / `__stop_SYSTEMD_BUS_ERROR_MAP`
- Iteration over section at runtime to find all error maps

**Problem with Fil-C:**
- ELF section iteration doesn't preserve pointer capabilities
- Section boundaries are raw addresses, not capability-bearing pointers

**Solution:** Inline all error maps

**src/libsystemd/sd-bus/bus-error.c**
```c
-BUS_ERROR_MAP_ELF_REGISTER const sd_bus_error_map bus_standard_errors[] = {
+const sd_bus_error_map bus_standard_errors[] = {
     SD_BUS_ERROR_MAP(SD_BUS_ERROR_FAILED, EACCES),
     // ... standard errors ...
+
+    // INLINED: All of bus_common_errors
+    SD_BUS_ERROR_MAP(BUS_ERROR_NO_SUCH_UNIT, ENOENT),
+    SD_BUS_ERROR_MAP(BUS_ERROR_NO_UNIT_FOR_PID, ESRCH),
+    // ... 140+ additional error mappings ...
+
     SD_BUS_ERROR_MAP_END
 };
```

**src/libsystemd/sd-bus/bus-common-errors.c**
```c
-BUS_ERROR_MAP_ELF_REGISTER const sd_bus_error_map bus_common_errors[] = {
-    SD_BUS_ERROR_MAP(BUS_ERROR_NO_SUCH_UNIT, ENOENT),
-    // ... deleted ...
-};
+// File is now empty (except includes)
```

**src/libsystemd/sd-bus/bus-common-errors.h**
```c
-BUS_ERROR_MAP_ELF_USE(bus_common_errors);
+//BUS_ERROR_MAP_ELF_USE(bus_common_errors);
```

**Lookup code changes:**
```c
-        m = ALIGN_PTR(__start_SYSTEMD_BUS_ERROR_MAP);
-        while (m < __stop_SYSTEMD_BUS_ERROR_MAP) {
-            if (m->code == BUS_ERROR_MAP_END_MARKER) {
-                m = ALIGN_PTR(m + 1);
-                continue;
-            }
+        m = bus_standard_errors;
+        while (m->code != BUS_ERROR_MAP_END_MARKER) {
             if (streq(m->name, name)) {
                 return m->code;
             }
```

**Impact:**
- Single consolidated error map instead of distributed maps
- Simpler, faster lookup (no section iteration)
- Loses modularity - can't add new error maps via separate compilation units
- Acceptable for systemd's use case (all errors are in libsystemd)

### Macro Definitions (src/libsystemd/sd-bus/bus-error.h)
```c
-#define BUS_ERROR_MAP_ELF_REGISTER ...
-#define BUS_ERROR_MAP_ELF_USE(errors) ...
+//#define BUS_ERROR_MAP_ELF_REGISTER ...
+//#define BUS_ERROR_MAP_ELF_USE(errors) ...
```
**Commented out** - no longer used

---

## tar 1.35

Identical obstack fix as sed - makes pointer alignment capability-aware.

### Fil-C Compatibility Changes

### gnu/obstack.h
```c
+#include <inttypes.h>
+#include <stdfil.h>

-#define __BPTR_ALIGN(B, P, A) ((B) + (((P) - (B) + (A)) & ~(A)))
+#define __BPTR_ALIGN(B, P, A)                                            \
+  __extension__                                                          \
+    ({ char *__P = (char *) (P);                                         \
+       zmkptr(__P, (uintptr_t)((B) + ((__P - (B) + (A)) & ~(A)))); })
```

**Same fix as sed** - see [sed details](../sed/details.md) for explanation.

**Why obstack needs this:**
- Obstack is a stack-like allocator
- Allocates memory in chunks, returns aligned pointers within chunks
- Original macro computes alignment offset, adds to base
- Without `zmkptr`, loses capability provenance
- With `zmkptr`, preserves capability from base pointer `__P`

---

## TCL 8.6.15

No actual Fil-C compatibility changes. After filtering prebuilt binaries and common build artifacts, the remaining patch contains library files, Windows resources, and build helpers that are part of the git history.

### Fil-C Compatibility Changes

None.

---

## texinfo v7.1

Texinfo required two types of Fil-C compatibility changes: a pointer alignment macro fix using `zmkptr` in gnulib's obstack implementation, and systematic replacement of `intptr_t` with `void*` for proper capability tracking in the parser's extra info system.

### Fil-C Compatibility Changes

### Pointer Alignment Fix
- **File**: `tp/Texinfo/XS/gnulib/lib/obstack.h`
- **Pattern**: Pointer arithmetic with alignment
- **Change**: Replaced pointer arithmetic `((B) + (((P) - (B) + (A)) & ~(A)))` with `zmkptr(__P, (uintptr_t)((B) + ((__P - (B) + (A)) & ~(A))))` in `__BPTR_ALIGN` macro
- **Why**: Ensures aligned pointer retains original capability bounds
- **Added headers**: `<stdfil.h>` and `<inttypes.h>`

### Type System Changes
- **Files**: `tp/Texinfo/XS/parsetexi/extra.c`, `tp/Texinfo/XS/parsetexi/tree_types.h`
- **Pattern**: Pointer-as-integer storage
- **Changes**:
  - Changed `KEY_PAIR.value` from `intptr_t` to `void*`
  - Updated `add_associated_info_key()` to accept `void*` instead of `intptr_t`
  - Removed 15+ casts from `(intptr_t)` to direct `void*` passing
  - Integer values now cast to `void*` instead of `intptr_t`
- **Why**: Fil-C capabilities cannot be truncated to integers; must be tracked as pointers

---

## tmux v3.5a

The tmux patch contains only autotools infrastructure files with no actual Fil-C compatibility changes to C source code.

### Fil-C Compatibility Changes

None - no C/C++ source code modifications.

---

## Toybox 8.12

Toybox is an all-in-one Linux command-line tool suite (like busybox). The Fil-C port disables vfork, adds signal safety checks, and fixes pointer/integer type conversions.

### Fil-C Compatibility Changes

### vfork Replacement

**lib/lib.h:**
```c
 #define XVFORK() xvforkwrap(vfork())
+#define XVFORK() xvforkwrap(({ errno = ENOSYS; -1; }))
```

vfork not available in Fil-C's safe glibc, so XVFORK macro now returns error instead.

**toys/other/oneit.c:**
```c
-  if (!vfork()) reboot(action);
+  if (!fork()) reboot(action);
 
-    pid = XVFORK();
+    pid = fork();
```

Direct vfork calls replaced with fork.

### Signal Handler Safety

**lib/portability.c:**
```c
+#include <stdfil.h>
+
-    if (signames[i].num != SIGKILL) xsignal(signames[i].num, handler);
+    if (signames[i].num != SIGKILL && !zis_unsafe_signal_for_handlers(signames[i].num))
+      xsignal(signames[i].num, handler);
```

Fil-C runtime reserves certain signals. `zis_unsafe_signal_for_handlers()` checks if a signal number is safe to install handlers for.

### Type Conversion in ls.c

**toys/posix/ls.c:**
```c
-static void zprint(int zap, char *pat, int len, unsigned long arg)
+static void zprint(int zap, char *pat, int len, void *arg)
```

Converted format helper from taking `unsigned long` to `void*`. All call sites updated to cast appropriately:

```c
-    if (FLAG(i)) zprint(zap, "lu ", totals[1], st->st_ino);
+    if (FLAG(i)) zprint(zap, "lu ", totals[1], (void*)st->st_ino);

-      zprint(zap, "s ", totals[6], (unsigned long)tmp);
+      zprint(zap, "s ", totals[6], tmp);

-      zprint(zap, "ld", totals[2]+1, st->st_nlink);
+      zprint(zap, "ld", totals[2]+1, (void*)st->st_nlink);
```

---

## vim v9.1.0660

Minimal one-line fix to prevent passing invalid signal handler pointer to sigaction on Unix systems.

### Fil-C Compatibility Changes

### Signal Handler Safety
- **File**: `src/os_unix.c`
- **Function**: `mch_signal()`
- **Change**: Modified sigaction call from:
  ```c
  if (sigaction(sig, &sa, &old) == -1)
  ```
  to:
  ```c
  if (sigaction(sig, func == SIG_ERR ? NULL : &sa, &old) == -1)
  ```
- **Why**: When `func` parameter is `SIG_ERR` (error sentinel), the code was previously setting up a `sigaction` struct with an invalid handler and passing it to `sigaction()`. Under Fil-C's strict pointer checking, this could trap. The fix passes NULL instead when error is indicated.
- **Pattern**: Defensive null pointer handling for special sentinel values

---

## wayland v1.24.0

Wayland required two changes: fixing pointer bit-masking for capability safety and replacing GCC section-based test registration with runtime constructors compatible with Fil-C.

### Fil-C Compatibility Changes

### Pointer Bit-Masking Fix
- **File**: `src/wayland-util.c`
- **Function**: `map_entry_get_data()`
- **Change**: Replaced `(void *)(entry.next & ~(uintptr_t)0x3)` with `(void *)((uintptr_t)entry.data & ~(uintptr_t)0x3)`
- **Why**: Cannot mask bits directly from pointer in Fil-C; must convert to integer, mask, then reconstruct pointer capability
- **Pattern**: Pointer metadata extraction via bit manipulation

### Test Registration System
- **Files**: `tests/test-runner.h`, `tests/test-runner.c`
- **Pattern**: ELF section → constructor-based registration
- **Changes**:
  - Removed `__start_test_section`/`__stop_test_section` external symbols
  - Added `struct test *first_test` global linked list
  - Rewrote `TEST()` and `FAIL_TEST()` macros to:
    - Define `register_test_##name()` constructor function
    - Dynamically `malloc()` test struct at initialization
    - Link into `first_test` list
  - Updated all test iteration loops from pointer arithmetic to list traversal
  - Changed test counting from section subtraction to manual iteration
- **Why**: Fil-C doesn't support accessing ELF section symbols as pointer ranges

---

## weston v12.0.5

Weston's test infrastructure used ELF linker sections for test discovery in three separate frameworks. All were converted to Fil-C-compatible constructor-based registration.

### Fil-C Compatibility Changes

### IVI Layout Test Plugin
- **File**: `tests/ivi-layout-test-plugin.c`
- **Pattern**: Section `plugin_test_section` → linked list
- **Changes**:
  - Removed `__start_plugin_test_section`/`__stop_plugin_test_section`
  - Added `struct runner_test *first_test` and `next` field
  - Rewrote `RUNNER_TEST()` macro with `register_test_##name()` constructor
  - Updated `find_runner_test()` to traverse list instead of array

### Main Test Runner
- **File**: `tests/weston-test-runner.{h,c}`
- **Pattern**: Section `test_section` → linked list + array conversion
- **Changes**:
  - Removed `__start_test_section`/`__stop_test_section`
  - Added `struct weston_test_entry *first_test` and `size_t num_tests`
  - Rewrote `TEST_COMMON()` macro with constructor that increments `num_tests`
  - Updated `find_test()` and `list_tests()` for list traversal
  - **Special**: `weston_test_harness_create()` converts linked list to array for backward compatibility with test harness API

### Zunitc Framework
- **Files**: `tools/zunitc/inc/zunitc/zunitc.h`, `tools/zunitc/inc/zunitc/zunitc_impl.h`, `tools/zunitc/src/zunitc_impl.c`
- **Pattern**: Section `zuc_tsect` → indexed linked list
- **Changes**:
  - Removed `__start_zuc_tsect`/`__stop_zuc_tsect`
  - Added `struct zuc_registration *first_zuc_reg` and `size_t zuc_reg_count`
  - Added `next_reg` and `index` fields to `struct zuc_registration`
  - Rewrote `ZUC_TEST()` macro to populate these fields
  - Updated `register_tests()` to build array from linked list for sorting

---

## xz v5.6.2

The xz package required symbol versioning support for Fil-C, pointer alignment fixes for SIMD code, buffer alignment, disabling of problematic optimizations, and build system adjustments.

### Fil-C Compatibility Changes

### Symbol Versioning
- **File**: `src/liblzma/common/common.h`
- **Change**: Added Fil-C-specific branch to `LZMA_SYMVER_API` macro:
  ```c
  #elif __PIZLONATOR_WAS_HERE__
  #  define LZMA_SYMVER_API(extnamever, type, intname) \
      __asm__(".filc_symver " #intname "," extnamever); \
      extern LZMA_API(type) intname
  ```
- **Pattern**: `.filc_symver` directive for Fil-C's symbol versioning
- **Why**: Fil-C uses custom assembly directive instead of `.symver`

### Pointer Alignment (SIMD)
- **File**: `src/liblzma/check/crc_x86_clmul.h`
- **Function**: `crc_simd_body()`
- **Change**: Replaced pointer arithmetic alignment:
  ```c
  const __m128i *aligned_buf = (const __m128i *)zmkptr(
      buf, (uintptr_t)buf & ~(uintptr_t)15);
  ```
- **Added header**: `<stdfil.h>`
- **Why**: Aligning pointer via masking loses capability bounds; `zmkptr` preserves them

### Buffer Alignment
- **File**: `src/xz/file_io.h`
- **Change**: Added explicit alignment to union:
  ```c
  typedef union __attribute__((aligned(16))) {
  ```
- **Why**: I/O buffer union used for aliasing between u8/u32/u64 arrays needs guaranteed alignment for SIMD access

### Optimization Disable
- **File**: `src/liblzma/rangecoder/range_decoder.h`
- **Change**: Disabled x86_64 optimized decoder config when `__PIZLONATOR_WAS_HERE__` is defined
- **Why**: The optimized decoder likely uses pointer/integer tricks incompatible with Fil-C capabilities

### Build System
- **File**: `src/liblzma/Makefile.am`
- **Change**: Replaced `-Wl,--version-script=` with `-XCClinker --version-script=`
- **Why**: Fil-C compiler wrapper uses different flag syntax for linker arguments

---

## zlib v1.3

Zlib patch disables ARM-specific optimizations, hardcodes some configure results, and removes build artifacts. No fundamental Fil-C compatibility work beyond platform restriction.

### Fil-C Compatibility Changes

### ARM CRC32 Disabled
- **File**: `crc32.c`
- **Change**: Commented out ARM CRC32 detection:
  ```c
  //#if defined(__aarch64__) && defined(__ARM_FEATURE_CRC32) && W == 8
  //#  define ARMCRC32
  //#endif
  ```
- **Why**: ARM intrinsics likely incompatible with Fil-C (Linux/x86_64 only platform)

### Configure Hardcoding
- **File**: `zconf.h`
- **Change**: Replaced configure-time conditionals with hardcoded `#if 1`:
  ```c
  #if 1    /* was set to #if 1 by ./configure */
  #  define Z_HAVE_UNISTD_H
  #endif
  
  #if 1    /* was set to #if 1 by ./configure */
  #  define Z_HAVE_STDARG_H
  #endif
  ```
- **Why**: Assumes POSIX environment (unistd.h, stdarg.h always available)

---

## zsh v5.8.0.1-dev

Zsh required disabling its custom arena allocator in favor of standard malloc/free, plus a struct layout fix for HashNode compatibility.

### Fil-C Compatibility Changes

### Custom Allocator Bypass
- **File**: `Src/mem.c`
- **Functions**: `zhalloc()`, `hrealloc()`
- **Changes**:
  - Added `if ((1)) return malloc(size);` at start of `zhalloc()`
  - Added `if ((1)) { char* result = malloc(new); memcpy(result, p, old < new ? old : new); return result; }` in `hrealloc()`
- **Why**: Zsh uses custom heap allocator with arena-style memory management. This likely confuses Fil-C's garbage collector or uses pointer tricks incompatible with capabilities. Forcing standard malloc/free ensures proper tracking.
- **Pattern**: Allocator compatibility bypass

### Struct Layout Fix
- **File**: `Src/Zle/zle_keymap.c`
- **Struct**: `struct key`
- **Change**: Added `int flags;` field after `char *nam;`
- **Why**: `struct key` is used as a `HashNode` (includes `flags` field), but was missing this member. Fil-C's stricter type checking likely caught this layout mismatch.
- **Pattern**: Struct alignment/layout correction

---

## zstd v1.5.6

Zstd required replacing inline CPUID assembly with standard library calls and disabling assembly-level loop alignment optimizations.

### Fil-C Compatibility Changes

### CPUID Detection
- **File**: `lib/common/cpu.h`
- **Function**: `ZSTD_cpuid()`
- **Changes**:
  - Added `#include <cpuid.h>` when `__FILC__` defined
  - Added Fil-C branch using `__get_cpuid()` from cpuid.h:
    ```c
    #ifdef __FILC__
        unsigned eax, ebx, ecx, edx, n;
        __get_cpuid(0, &eax, &ebx, &ecx, &edx);
        n = eax;
        if (n >= 1) {
            __get_cpuid(1, &eax, &ebx, &ecx, &edx);
            f1c = ecx; f1d = edx;
        }
        if (n >= 7) {
            __get_cpuid(7, &eax, &ebx, &ecx, &edx);
            f7b = ebx; f7c = ecx;
        }
    ```
- **Why**: Original code uses inline assembly or compiler intrinsics for CPUID. Fil-C doesn't support inline assembly, so standard `cpuid.h` provides safe access.
- **Pattern**: Platform intrinsics → standard library

### Loop Alignment Disabled
- **Files**: `lib/compress/zstd_lazy.c`, `lib/decompress/zstd_decompress_block.c`
- **Changes**: Added `&& !defined(__FILC__)` to four instances of:
  ```c
  #if defined(__GNUC__) && defined(__x86_64__) && !defined(__FILC__)
      __asm__(".p2align 6");  // or similar alignment directives
  ```
- **Why**: Inline assembly directives for loop alignment not supported by Fil-C compiler
- **Pattern**: Inline assembly removal

---

