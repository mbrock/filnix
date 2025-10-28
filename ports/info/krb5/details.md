# Kerberos 5 1.21.3

## Summary
Linker flag fix and memory fence integration for embedded libev event loop.

## Fil-C Compatibility Changes

### Build system fix (src/config/shlib.conf)
- **Version script linker flag**:
  - Changed: `-Wl,--version-script binutils.versions`
  - To: `--version-script=binutils.versions`
  - Removes `-Wl,` prefix (linker wrapper prefix)
  - Uses direct linker flag syntax

**Why**: Fil-C's linker integration expects direct linker flags, not gcc wrapper format.

### Event loop memory fences (src/util/verto/ev.c)
- **Added includes**:
  - `#include <stdfil.h>` (Fil-C primitives)
  
- **Memory fence definitions**:
  - `#define ECB_MEMORY_FENCE zfence()`
  - `#define ECB_MEMORY_FENCE_ACQUIRE zfence()`
  - `#define ECB_MEMORY_FENCE_RELEASE zfence()`
  
- **Purpose**: Replace libev's inline assembly memory barriers with Fil-C fence primitive
  - libev uses platform-specific atomic/fence operations
  - Fil-C doesn't support inline assembly
  - `zfence()` provides full memory barrier for all fence types

**Context**: This is part of the embedded libev event loop library in the Verto event abstraction layer used by Kerberos.

## Build Artifact Bloat
None - all changes are code modifications.

## Assessment
- **Patch quality**: Minimal - exactly what's needed
- **Actual changes**: Minor but necessary
  - Linker flag fix is build system integration
  - Memory fences essential for event loop correctness
  - Conservative approach: using full fence for all barrier types
- **Pattern**: Similar to ICU's aliasing barrier replacement - both replace low-level primitives with Fil-C equivalents
