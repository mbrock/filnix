# diffutils 3.10

## Summary
Warning suppression and stack overflow handling changes for Fil-C compatibility.

## Fil-C Compatibility Changes

### Diagnostic Pragmas
- **lib/regex.h**: `#pragma clang diagnostic ignored "-Wvla"`
- **lib/stdio.in.h**: `#pragma clang diagnostic ignored "-Winclude-next-absolute-path"`
- **lib/unistd.in.h**: `#pragma clang diagnostic ignored "-Winclude-next-absolute-path"`
- **lib/wctype.in.h**: `#pragma clang diagnostic ignored "-Winclude-next-absolute-path"`
- **src/diff.c**: `#pragma clang diagnostic ignored "-Wbool-operation"`

### Stack Overflow Handling
- **lib/sigsegv.c**: Disabled stack overflow recovery with `#if HAVE_STACK_OVERFLOW_RECOVERY && !defined(__FILC__)`
  - Fil-C's stack management incompatible with low-level stack manipulation

## Build Artifact Bloat
None - clean patch with only source code changes.

## Assessment
- **Patch quality**: Minimal, no bloat
- **Actual changes**: Minor (mostly warning suppression, one feature disable)
