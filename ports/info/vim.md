# vim v9.1.0660

## Summary
Minimal one-line fix to prevent passing invalid signal handler pointer to sigaction on Unix systems.

## Fil-C Compatibility Changes

### Signal Handler Safety
- **File**: `src/os_unix.c`
- **Function**: `mch_signal()`
- **Change**: Modified sigaction call from:
  ```c
  if (sigaction(sig, &sa, &old) == -1)
  ```
  to:
  ```c
  if (sigaction(sig, func == SIG_ERR ? NULL : &sa, &old) == -1)
  ```
- **Why**: When `func` parameter is `SIG_ERR` (error sentinel), the code was previously setting up a `sigaction` struct with an invalid handler and passing it to `sigaction()`. Under Fil-C's strict pointer checking, this could trap. The fix passes NULL instead when error is indicated.
- **Pattern**: Defensive null pointer handling for special sentinel values

## Build Artifact Bloat
None - single source file change only.

## Assessment
- **Patch quality**: Minimal and precise
- **Actual changes**: Minor but important - prevents undefined behavior with invalid signal handlers
- **Complexity**: Trivial one-line conditional fix
