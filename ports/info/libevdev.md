# libevdev 1.11.0

## Summary
Replaces GCC section attributes for test discovery with constructor functions and linked list. Changes symbol versioning linker flag to Fil-C format.

## Fil-C Compatibility Changes

**meson.build (Symbol Versioning)**:
- Changed `-Wl,--version-script` to `--version-script` (Fil-C linker doesn't use `-Wl,` prefix)

**test/test-common.h & test/test-main.c (Test Registration)**:
- Removed `__start_test_section`/`__stop_test_section` linker symbols
- Added `const struct libevdev_test *first_test` global
- Added `next_test` pointer to `struct libevdev_test` for linked list
- Changed `_TEST_SUITE` macro:
  - Removed `__attribute__((section ("test_section")))`
  - Added constructor function `register_##name()` that:
    - Allocates test struct with `malloc()`
    - Populates name, setup function, privileges flag
    - Prepends to `first_test` linked list
- Changed test iteration from section iteration to linked list traversal:
  - `for (t = &__start_test_section; t < &__stop_test_section; t++)` 
  - → `for (t = first_test; t; t = t->next_test)`
- Added `#include <stdlib.h>` for malloc

## Build Artifact Bloat
None - this is a clean patch with only source code changes.

## Assessment
- **Patch quality**: Minimal - only necessary changes
- **Actual changes**: Moderate - complete rewrite of test discovery from sections to constructors
- **Pattern**: Constructor-based initialization instead of linker sections (Fil-C doesn't support custom sections)
