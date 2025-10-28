# Grep 3.11

## Summary
Minimal changes for Fil-C pointer provenance and signal handling compatibility.

## Fil-C Compatibility Changes
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

## Build Artifact Bloat
None - patch contains only actual code changes.

## Assessment
- **Patch quality**: Minimal - exactly what's needed
- **Actual changes**: Minor but critical
  - zmkptr usage prevents pointer provenance violations in alignment calculations
  - Signal handler disabling necessary for FUGC compatibility
- **Pattern**: Similar to other projects (emacs, krb5) in disabling signal handlers
