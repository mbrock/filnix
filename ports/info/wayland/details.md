# wayland v1.24.0

## Summary
Wayland required two changes: fixing pointer bit-masking for capability safety and replacing GCC section-based test registration with runtime constructors compatible with Fil-C.

## Fil-C Compatibility Changes

### Pointer Bit-Masking Fix
- **File**: `src/wayland-util.c`
- **Function**: `map_entry_get_data()`
- **Change**: Replaced `(void *)(entry.next & ~(uintptr_t)0x3)` with `(void *)((uintptr_t)entry.data & ~(uintptr_t)0x3)`
- **Why**: Cannot mask bits directly from pointer in Fil-C; must convert to integer, mask, then reconstruct pointer capability
- **Pattern**: Pointer metadata extraction via bit manipulation

### Test Registration System
- **Files**: `tests/test-runner.h`, `tests/test-runner.c`
- **Pattern**: ELF section → constructor-based registration
- **Changes**:
  - Removed `__start_test_section`/`__stop_test_section` external symbols
  - Added `struct test *first_test` global linked list
  - Rewrote `TEST()` and `FAIL_TEST()` macros to:
    - Define `register_test_##name()` constructor function
    - Dynamically `malloc()` test struct at initialization
    - Link into `first_test` list
  - Updated all test iteration loops from pointer arithmetic to list traversal
  - Changed test counting from section subtraction to manual iteration
- **Why**: Fil-C doesn't support accessing ELF section symbols as pointer ranges

## Build Artifact Bloat
None - only source code changes.

## Assessment
- **Patch quality**: Clean and minimal
- **Actual changes**: Moderate - one trivial fix plus systematic test infrastructure rewrite
- **Complexity**: Test registration change is standard Fil-C pattern (seen in other projects)
