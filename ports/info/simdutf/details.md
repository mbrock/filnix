# simdutf 5.5.0

## Summary
Minimal changes to enable CPU feature detection under Fil-C runtime.

## Fil-C Compatibility Changes

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

## Build Artifact Bloat
None.

## Assessment
- **Patch quality**: Minimal, clean
- **Actual changes**: Trivial (feature detection compatibility)
- **Correctness**: Appropriate - delegates to runtime helpers
- **Impact**: Low - only affects CPU feature detection at startup
