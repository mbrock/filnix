# libdrm 2.4.122

## Summary
DRM library passes pointers to kernel via ioctl in uint64_t fields. Patch adds pointer table to encode pointers for kernel and decode on return. Most conversions are one-way since kernel doesn't return pointers.

## Fil-C Compatibility Changes

**xf86drmMode.c (Pointer Table for Kernel Ioctls)**:
- Added `<stdfil.h>` include
- Created static `zexact_ptrtable* ptrtable` with constructor to initialize: `zexact_ptrtable_new()`
- Redefined macros:
  - `U642VOID(x)`: `zexact_ptrtable_decode(ptrtable, (unsigned long)(x))`
  - `VOID2U64(x)`: `zexact_ptrtable_encode(ptrtable, (x))`
  - Added `VOID2U64_ONEWAY(x)`: `(uint64_t)(unsigned long)(x)` - for pointers sent to kernel but never decoded
- Comment notes: "DRM ioctls are a safety escape hatch, since we're passing a buffer to the kernel that has pointers in it"
- Changed most `VOID2U64` calls to `VOID2U64_ONEWAY` since kernel doesn't return these pointers:
  - `drmModeDirtyFB`: clips_ptr
  - `drmModeSetCrtc`: set_connectors_ptr
  - `_drmModeGetConnector`: modes_ptr (stack_mode address)
  - `drmModeCrtcGetGamma/SetGamma`: red/green/blue pointers
  - `drmModeAtomicCommit`: objs_ptr, count_props_ptr, props_ptr, prop_values_ptr
  - `drmModeListLessees/drmModeGetLease`: lessees_ptr/objects_ptr
- Only `atomic.user_data` uses bidirectional `VOID2U64` (line 107)

## Build Artifact Bloat
None - this is a clean patch with only source code changes.

## Assessment
- **Patch quality**: Minimal - only necessary changes with helpful comment
- **Actual changes**: Moderate - requires pointer table infrastructure and careful analysis of which pointers are one-way vs bidirectional
- **Pattern**: Syscall pointer marshaling - common pattern when passing pointers through integer fields to kernel
