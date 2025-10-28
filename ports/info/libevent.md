# libevent 2.1.12

## Summary
Mostly test adjustments: disables flaky tests and fixes function pointer cast. Minimal Fil-C compatibility work.

## Fil-C Compatibility Changes

**test/regress_http.c (Disabled Tests)**:
- Added `HTTPS_SKIP` macro: `TT_ISOLATED|TT_OFF_BY_DEFAULT`
- Changed to `HTTPS_SKIP` for:
  - `https_incomplete`
  - `https_incomplete_timeout`
  - `https_chunk_out`
- These tests likely have timing/behavior differences under Fil-C

**test/regress_ssl.c (Disabled Tests)**:
- Added `TT_OFF_BY_DEFAULT` flag to:
  - `bufferevent_socketpair_dirty_shutdown`
  - `bufferevent_renegotiate_socketpair_dirty_shutdown`
  - `bufferevent_socketpair_startopen_dirty_shutdown`
- Dirty shutdown tests probably interact badly with Fil-C's safety checks

**test/regress_main.c (Function Pointer Cast)**:
- Changed `data->legacy_test_fn()` to cast through intermediate variable:
  ```c
  void (*fn)(void* arg) = (void (*)(void*))data->legacy_test_fn;
  fn(NULL);
  ```
- Fil-C requires explicit function pointer type matching

## Build Artifact Bloat
None - this is a clean patch with only source code changes.

## Assessment
- **Patch quality**: Minimal - targeted test disables and one cast fix
- **Actual changes**: Minor - mostly test configuration, one function pointer fix
- **Pattern**: Test stability adjustments for Fil-C runtime behavior
