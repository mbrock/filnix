# Python 3.12.5

## Summary
Extensive rework of Python's low-level memory and concurrency primitives to work with Fil-C's capability model. Changes touch GC, atomics, frame allocation, and code object handling.

## Fil-C Compatibility Changes

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

## Build Artifact Bloat
None - code-only patch.

## Assessment
- **Patch quality**: Clean, well-structured
- **Actual changes**: Very substantial - touches 30+ files
- **Complexity**: High - requires deep understanding of CPython internals
- **Correctness**: Appears sound - systematic approach to capability preservation
- **Performance impact**: Frame allocation change may be costly (GC pressure)
