# OpenSSH v9.8p1

## Summary
Minimal seccomp filter adjustment to allow scheduler yield syscall needed by Fil-C runtime.

## Fil-C Compatibility Changes
- **sandbox-seccomp-filter.c**: Add `SC_ALLOW(__NR_sched_yield)` to pre-authentication syscall allow-list
  - Fil-C's garbage collector or runtime likely requires `sched_yield()` for cooperative scheduling
  - Added conditionally with `#ifdef __NR_sched_yield` guard

## Build Artifact Bloat
None - single source file change.

## Assessment
- Patch quality: Minimal, targeted fix
- Actual changes: Minor (single syscall allowlist addition for Fil-C runtime)
