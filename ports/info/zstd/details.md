# zstd v1.5.6

## Summary
Zstd required replacing inline CPUID assembly with standard library calls and disabling assembly-level loop alignment optimizations.

## Fil-C Compatibility Changes

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

## Build Artifact Bloat
None - only source code changes.

## Assessment
- **Patch quality**: Clean, minimal changes
- **Actual changes**: Minor - replaces non-portable features with portable equivalents
- **Complexity**: Trivial - standard library substitution plus optimization disabling
