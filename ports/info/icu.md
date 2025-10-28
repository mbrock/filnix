# ICU 76.1

## Summary
Targeted changes for Fil-C pointer safety, compiler fencing, and build system adjustments to avoid assembly code generation.

## Fil-C Compatibility Changes

### Runtime code modifications
- **icu4c/source/common/putil.cpp**: Timezone handling
  - Added early return in `uprv_timezone()`: `if ((1)) return timezone;`
  - Bypasses complex timezone detection logic
  - Uses global `timezone` variable directly

- **icu4c/source/common/ucnv.cpp**: Pointer alignment with zmkptr
  - Changed: `stackBuffer = reinterpret_cast<void *>(aligned_p);`
  - To: `stackBuffer = zmkptr(stackBuffer, aligned_p);`
  - Preserves pointer provenance during alignment in safe clone operation

- **icu4c/source/common/unicode/char16ptr.h**: Aliasing barrier
  - Added `#ifdef __PIZLONATOR_WAS_HERE__` section
  - Defines `U_ALIASING_BARRIER(ptr)` as `zcompiler_fence()`
  - Replaces inline assembly with Fil-C fence primitive
  - Prevents compiler optimizations that violate memory model

### Build system changes
- **icu4c/source/configure.ac**: Disable assembly generation
  - Sets `GENCCODE_ASSEMBLY=` (empty)
  - Prevents assembly code generation during data compilation

- **icu4c/source/tools/toolutil/pkg_genc.h**: Force data-only mode
  - Added `#ifdef __PIZLONATOR_WAS_HERE__` → `#define U_DISABLE_OBJ_CODE`
  - Disables object code generation in packaging tool
  - Forces use of C data arrays instead of platform-specific binary formats

## Build Artifact Bloat
None - all changes are code or build configuration modifications.

## Assessment
- **Patch quality**: Minimal - targeted changes only
- **Actual changes**: Minor but essential
  - zmkptr prevents provenance violations during pointer arithmetic
  - Compiler fence replaces inline assembly (Fil-C doesn't support asm)
  - Object code disabling avoids assembly generation entirely
- **Interesting pattern**: Uses `__PIZLONATOR_WAS_HERE__` macro to conditionalize Fil-C changes
