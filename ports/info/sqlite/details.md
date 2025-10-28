# SQLite (version not in patch, likely 3.x)

## Summary
Substantial test harness modifications to encode pointers when passing to/from TCL, plus core changes to disable atomics and add custom build system.

## Fil-C Compatibility Changes

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

## Build Artifact Bloat
None (Makefile.filc is intentional custom build system).

## Assessment
- **Patch quality**: Clean, systematic
- **Actual changes**: Substantial (affects 10+ test files)
- **Pattern consistency**: Good - centralized encode/decode functions
- **Build system**: Custom Makefile is fragile (hardcoded paths)
- **Test philosophy**: Pragmatic - makes tests pass without compromising safety
