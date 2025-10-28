# libffi 3.4.6

## Summary
Substantial Fil-C port implementing FFI with zclosure system, custom calling convention, and stack-based marshaling. Replaces assembly trampolines with Fil-C closures. Includes test files and documentation.

## Fil-C Compatibility Changes

**Makefile.am & configure.host (Build Configuration)**:
- Changed `-Wl,--version-script` to `--version-script`
- Hardcoded `SOURCES=ffi64.c` in configure.host (forces x86_64 backend)

**src/closures.c (Closure Implementation)**:
- Wrapped entire original implementation in `#ifndef __FILC__`
- Fil-C implementation:
  - `ffi_closure_alloc`: Uses `zclosure_new(ffi_closure_callback, NULL)` instead of mmap
  - `ffi_closure_free`: No-op (GC handles cleanup)
  - `ffi_tramp_is_present`: Returns 0
- No executable memory needed - closures use Fil-C's native closure system

**src/x86/ffi64.c (x86-64 Backend)**:
- Added `FFI_FILC` ABI enum value (aliased to `FFI_UNIX64` for compatibility)
- Added `is_filc` static bool flag
- Stack-based calling in `ffi_call_int`:
  - Allocates stack with `alloca(cif->bytes)`
  - Marshals arguments sequentially with alignment
  - Calls via `zcall(fn, stack)` instead of `ffi_call_unix64` assembly
  - Return value copied from `zcall` result
- Modified `ffi_prep_cif_machdep`:
  - Forces all arguments to stack (bypasses register classification)
  - `if (is_filc || examine_argument(...))` - always takes stack path
- Closure callback `ffi_closure_callback` (Fil-C only):
  - Gets closure data: `zcallee_closure_data()`
  - Gets arguments: `zargs()`
  - Unmarshals from stack to avalue array
  - Calls user function
  - Returns via `zreturn(rvalue)`

**src/x86/ffitarget.h (ABI Definition)**:
- Conditional ABI enum for `__FILC__`:
  ```c
  #if defined(__FILC__)
    FFI_FILC,
    FFI_UNIX64 = FFI_FILC,
    FFI_DEFAULT_ABI = FFI_FILC
  ```
- Disabled `FFI_GO_CLOSURES` for Fil-C

**src/x86/ffi64.c (Prep CIF)**:
- Disabled EFI64/GNUW64 ABI support under Fil-C
- Only allows `FFI_FILC` ABI

## Build Artifact Bloat

**Generated/Test Files (Should Exclude)**:
- `doc/libffi.info` (362 lines): Generated documentation from makeinfo 6.8
- `fficonfig.h.in`: Autoconf template
- `ffitest.c`, `ffitest.expected`: Test files

## Assessment
- **Patch quality**: Moderate bloat - includes test files and generated docs, but core changes are clean
- **Actual changes**: Substantial - complete reimplementation of FFI mechanism using Fil-C primitives
- **Pattern**: 
  - Closure system replacement (zclosure instead of trampolines)
  - Stack-based calling convention (zcall)
  - Simplified argument marshaling (no register classification)
  - Symbol versioning flag changes
