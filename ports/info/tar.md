# tar 1.35

## Summary
Identical obstack fix as sed - makes pointer alignment capability-aware.

## Fil-C Compatibility Changes

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

## Build Artifact Bloat
None.

## Assessment
- **Patch quality**: Minimal, correct
- **Actual changes**: Trivial (1 macro fix)
- **Pattern**: Identical to sed, likely from same gnulib source
- **Correctness**: Critical for capability safety in obstack operations
