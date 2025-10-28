# weston v12.0.5

## Summary
Weston's test infrastructure used ELF linker sections for test discovery in three separate frameworks. All were converted to Fil-C-compatible constructor-based registration.

## Fil-C Compatibility Changes

### IVI Layout Test Plugin
- **File**: `tests/ivi-layout-test-plugin.c`
- **Pattern**: Section `plugin_test_section` → linked list
- **Changes**:
  - Removed `__start_plugin_test_section`/`__stop_plugin_test_section`
  - Added `struct runner_test *first_test` and `next` field
  - Rewrote `RUNNER_TEST()` macro with `register_test_##name()` constructor
  - Updated `find_runner_test()` to traverse list instead of array

### Main Test Runner
- **File**: `tests/weston-test-runner.{h,c}`
- **Pattern**: Section `test_section` → linked list + array conversion
- **Changes**:
  - Removed `__start_test_section`/`__stop_test_section`
  - Added `struct weston_test_entry *first_test` and `size_t num_tests`
  - Rewrote `TEST_COMMON()` macro with constructor that increments `num_tests`
  - Updated `find_test()` and `list_tests()` for list traversal
  - **Special**: `weston_test_harness_create()` converts linked list to array for backward compatibility with test harness API

### Zunitc Framework
- **Files**: `tools/zunitc/inc/zunitc/zunitc.h`, `tools/zunitc/inc/zunitc/zunitc_impl.h`, `tools/zunitc/src/zunitc_impl.c`
- **Pattern**: Section `zuc_tsect` → indexed linked list
- **Changes**:
  - Removed `__start_zuc_tsect`/`__stop_zuc_tsect`
  - Added `struct zuc_registration *first_zuc_reg` and `size_t zuc_reg_count`
  - Added `next_reg` and `index` fields to `struct zuc_registration`
  - Rewrote `ZUC_TEST()` macro to populate these fields
  - Updated `register_tests()` to build array from linked list for sorting

## Build Artifact Bloat
None - only test framework source changes.

## Assessment
- **Patch quality**: Clean, systematic refactoring
- **Actual changes**: Moderate - three independent test frameworks converted
- **Complexity**: Standard Fil-C pattern, but applied to three different systems. The weston-test-runner and zunitc conversions preserve original ordering/sorting behavior.
