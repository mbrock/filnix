# libinput 1.29.1

## Summary
Similar to libevdev: replaces linker sections with constructor-based registration for test devices and collections. Symbol versioning flag change.

## Fil-C Compatibility Changes

**meson.build (Symbol Versioning)**:
- Changed `-Wl,--version-script` to `--version-script`

**test/litest.h & test/litest-main.c (Test Device Registration)**:
- Removed `__start_test_device_section`/`__stop_test_device_section` symbols
- Added `struct test_device *first_test_device` global
- Added `next_test_device` pointer to `struct test_device`
- Changed `TEST_DEVICE` macro:
  - Removed `__attribute__((section ("test_device_section")))`
  - Added constructor `register_##which()`:
    - `malloc(sizeof(struct test_device))`
    - Prepends to `first_test_device` linked list
- Changed `TEST_COLLECTION` macro similarly:
  - Removed `__attribute__((section ("test_collection_section")))`
  - Added constructor with malloc and linked list prepend
- Updated iteration loops:
  - `for (t = &__start_test_device_section; t < &__stop_test_device_section; t++)`
  - → `for (t = first_test_device; t; t = t->next_test_device)`
  - Same for test collections
- Added `#include <stdlib.h>` for malloc

## Build Artifact Bloat
None - this is a clean patch with only source code changes.

## Assessment
- **Patch quality**: Minimal - only necessary changes
- **Actual changes**: Moderate - dual registration system (devices + collections) converted from sections to constructors
- **Pattern**: Identical to libevdev - constructor-based initialization instead of linker sections
