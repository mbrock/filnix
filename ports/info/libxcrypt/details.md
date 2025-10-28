# libxcrypt 4.4.36

## Summary
Minimal patch: disables SIMD and uses Fil-C symbol versioning directive.

## Fil-C Compatibility Changes

**lib/alg-yescrypt-opt.c (Disable SIMD)**:
- Added `#undef __SSE2__` and `#undef __SSE__` after includes
- Prevents SSE optimizations in yescrypt/scrypt/gost_yescrypt implementations
- Fil-C likely doesn't support SIMD intrinsics or they cause issues

**lib/crypt-port.h (Symbol Versioning)**:
- Changed `.symver` to `.filc_symver` in inline assembly:
  ```c
  // Old: __asm__ (".symver " #intname "," extstr "@" #version)
  // New: __asm__ (".filc_symver " #intname "," extstr "@" #version)
  ```
- Applies to both `_symver_ref` (compatibility symbols) and `symver_set` macros
- Fil-C linker uses different symbol versioning directive

## Build Artifact Bloat
None - this is a clean patch with only source code changes.

## Assessment
- **Patch quality**: Minimal - two targeted changes
- **Actual changes**: Minor - SIMD disable + assembler directive change
- **Pattern**:
  - SIMD incompatibility (common in Fil-C)
  - Symbol versioning syntax (`.filc_symver` vs `.symver`)
