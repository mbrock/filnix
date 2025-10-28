# sed 4.9

## Summary
Disabled gnulib test assumptions about memory behavior and fixed pointer arithmetic in obstack allocator.

## Fil-C Compatibility Changes

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

## Build Artifact Bloat
None.

## Assessment
- **Patch quality**: Clean
- **Actual changes**: Minor (test guards + obstack fix)
- **Correctness**: Obstack fix is critical for capability semantics
- **Test philosophy**: Disabling tests that assume specific allocator behavior is pragmatic
