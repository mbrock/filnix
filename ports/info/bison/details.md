# bison 3.8.2

## Summary
Alignment macro rewritten to use Fil-C's zmkptr function for proper capability handling during pointer arithmetic.

## Fil-C Compatibility Changes
- **lib/obstack.h**: Rewrote `__BPTR_ALIGN` macro
  - Added includes: `<stdfil.h>` and `<inttypes.h>`
  - Original: `((B) + (((P) - (B) + (A)) & ~(A)))`
  - New: Uses GCC statement expression with temporary variable
  - Calls `zmkptr(__P, (uintptr_t)((B) + ((__P - (B) + (A)) & ~(A))))`
  - `zmkptr` preserves capabilities while creating aligned pointer from address
  - Pattern: compute address arithmetically, then construct pointer with proper bounds

## Build Artifact Bloat
None - clean patch with only source code changes.

## Assessment
- **Patch quality**: Minimal, no bloat
- **Actual changes**: Minor (single macro rewrite for alignment)
