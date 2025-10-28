# libuv v1.48.0

## Summary
Moderate Fil-C port: disables io_uring, adds signal safety, uses pointer tables for signal handlers, fixes string length calculation, and disables problematic tests.

## Fil-C Compatibility Changes

**src/unix/linux.c (Disable io_uring)**:
- Added `#elif defined(__FILC__)` returning 0 in `uv__use_io_uring()`
- Comment: "The io_uring API is not yet supported by Fil-C, and may never be."
- Fallback to traditional epoll/poll

**src/unix/process.c (Signal Safety)**:
- Added `#include <stdfil.h>`
- Signal setup loop skips unsafe signals:
  ```c
  if (n == SIGKILL || n == SIGSTOP || zis_unsafe_signal_for_handlers(n))
    continue;
  ```
- Fil-C runtime function checks signal compatibility

**src/unix/signal.c (Signal Handler Pointer Table)**:
- Added `#include <stdfil.h>`
- Created `zexact_ptrtable* handle_table` with constructor: `zexact_ptrtable_new_weak()`
- Signal handler encodes pointer:
  ```c
  msg.handle = (void*)zexact_ptrtable_encode(handle_table, handle);
  ```
- Event loop decodes pointer:
  ```c
  handle = zexact_ptrtable_decode(handle_table, (uintptr_t)msg->handle);
  ```
- Necessary because signal handlers can't safely pass pointers through non-async-signal-safe mechanisms

**src/unix/proctitle.c (Process Title Length)**:
- Added `#include <stdfil.h>`
- Changed capacity calculation:
  ```c
  // Old: pt.cap = argv[i - 1] + size - argv[0];
  // New: pt.cap = zlength(pt.str);
  ```
- Uses Fil-C's `zlength()` instead of pointer arithmetic on argv array

**test/test-process-priority.c (Disabled Test)**:
- Commented out PID 0/getpid equivalence check with FIXME:
  ```c
  // FIXME: On Fil-C, this fails, most likely due to the main thread hack we do.
  //ASSERT_OK(uv_os_getpriority(uv_os_getpid(), &r));
  //ASSERT_EQ(priority, r);
  ```

**test/test-thread-priority.c (Disabled Test)**:
- Commented out nice value test on Linux:
  ```c
  // FIXME: Why isn't the Fil-C runtime getting this right?
  ```

**test/test-thread.c (Stack Size Check)**:
- Added `&& !defined(__FILC__)` to Linux/glibc stack size check
- Fil-C thread stacks may not match glibc behavior

**test/test-timer.c (Disabled Test)**:
- Commented out entire `timer_run_once` test body
- Comment: "This has a flaky failure where the second uv_run call returns 1 in Fil-C."

## Build Artifact Bloat
None - this is a clean patch with only source code changes.

## Assessment
- **Patch quality**: Minimal - targeted fixes and test disables with FIXME comments
- **Actual changes**: Moderate - several runtime compatibility adjustments
- **Pattern**: 
  - Platform capability disabling (io_uring)
  - Signal safety infrastructure (pointer table, safety checks)
  - String/array handling (zlength vs pointer arithmetic)
  - Test stability fixes (disabled flaky tests)
