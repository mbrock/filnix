# m4 v1.4.19

## Summary
Comprehensive Fil-C compatibility changes across library code plus test suite adjustments.

## Fil-C Compatibility Changes

### Core Library Modifications
- **lib/fpucw.h**: Add Fil-C FPU control word functions
  - `#ifdef __FILC__` block includes `pizlonated_math.h`
  - Replace inline asm `GET_FPUCW()`/`SET_FPUCW()` with `zmath_getcw()`/`zmath_setcw()`

- **lib/obstack.h**: Fix pointer alignment macro
  - Include `<inttypes.h>` and `<stdfil.h>`
  - Change `__BPTR_ALIGN` to use `zmkptr()` for safe pointer arithmetic

- **lib/sigsegv.in.h**: Disable stack overflow recovery under Fil-C
  - Add `&& !defined __FILC__` to `HAVE_STACK_OVERFLOW_RECOVERY` check

### Macro Processing
- **src/macro.c**: Use `zmkptr()` for argv pointer calculation

### Test Suite Adjustments
- **checks/006.command_li**: Deleted (tests closed stdout, problematic for Fil-C)
- **checks/198.sysval**: Deleted (tests signal handling with kill -9)
- **tests/test-calloc-gnu.c**: Skip allocation size checks under `__FILC__`
- **tests/test-explicit_bzero.c**: Skip freed memory checks under `__FILC__`
- **tests/test-free.c**: Skip max_map_count test under `__FILC__`
- **tests/test-malloc-gnu.c**: Skip PTRDIFF_MAX allocation test under `__FILC__`
- **tests/test-posix_spawn-script.c**: Mark test as flaky and skip
- **tests/test-realloc-gnu.c**: Skip PTRDIFF_MAX reallocation test under `__FILC__`
- **tests/test-reallocarray.c**: Skip size limit tests under `__FILC__`
- **tests/test-sigsegv-catch-segv1.c**: Disable under `__FILC__`
- **tests/test-sigsegv-catch-segv2.c**: Disable under `__FILC__`
- **tests/test-spawn-pipe.sh**: Reduce test iterations from 0-7 to exclude 3 and 7

## Build Artifact Bloat
None - deleted test files were test cases, not build artifacts.

## Assessment
- Patch quality: Clean, well-targeted changes
- Actual changes: Substantial (multiple library compatibility fixes + extensive test adjustments)
