# zlib v1.3

## Summary
Zlib patch disables ARM-specific optimizations, hardcodes some configure results, and removes build artifacts. No fundamental Fil-C compatibility work beyond platform restriction.

## Fil-C Compatibility Changes

### ARM CRC32 Disabled
- **File**: `crc32.c`
- **Change**: Commented out ARM CRC32 detection:
  ```c
  //#if defined(__aarch64__) && defined(__ARM_FEATURE_CRC32) && W == 8
  //#  define ARMCRC32
  //#endif
  ```
- **Why**: ARM intrinsics likely incompatible with Fil-C (Linux/x86_64 only platform)

### Configure Hardcoding
- **File**: `zconf.h`
- **Change**: Replaced configure-time conditionals with hardcoded `#if 1`:
  ```c
  #if 1    /* was set to #if 1 by ./configure */
  #  define Z_HAVE_UNISTD_H
  #endif
  
  #if 1    /* was set to #if 1 by ./configure */
  #  define Z_HAVE_STDARG_H
  #endif
  ```
- **Why**: Assumes POSIX environment (unistd.h, stdarg.h always available)

## Build Artifact Bloat
Significant cleanup - removing generated files:
- `Makefile` (5 lines) - Generated, should not be in source
- `zconf.h.cmakein` (553 lines) - CMake template, build artifact

This is actually beneficial bloat reduction.

## Assessment
- **Patch quality**: Mixed - good artifact cleanup, but minimal Fil-C work
- **Actual changes**: Minor - platform restriction only, no real capability/pointer fixes
- **Complexity**: Trivial - mostly just disabling features
