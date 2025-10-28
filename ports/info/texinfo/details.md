# texinfo v7.1

## Summary
Texinfo required two types of Fil-C compatibility changes: a pointer alignment macro fix using `zmkptr` in gnulib's obstack implementation, and systematic replacement of `intptr_t` with `void*` for proper capability tracking in the parser's extra info system.

## Fil-C Compatibility Changes

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

## Build Artifact Bloat
None - this is a clean patch with only source code changes.

## Assessment
- **Patch quality**: Minimal, clean implementation
- **Actual changes**: Minor but essential - fixes fundamental pointer handling for Fil-C safety
- **Complexity**: Two distinct patterns - alignment (obstack) and type safety (parser)
