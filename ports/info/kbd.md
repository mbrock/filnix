# KBD 2.6.4

## Summary
Removes unnecessary (and dangerous) integer casts from ioctl pointer arguments. Most of patch is keymap data file corrections unrelated to Fil-C.

## Fil-C Compatibility Changes

### Source code changes (26 lines)
- **contrib/dropkeymaps.c**: Removed `(unsigned long)` casts
  - Changed `ioctl(fd, KDSKBENT, (unsigned long)&ke)` → `ioctl(fd, KDSKBENT, &ke)` (2 instances)

- **src/libkeymap/kernel.c**: Removed casts from ioctl calls
  - `KDGKBENT`: Removed `(unsigned long)` cast (1 instance)
  - `KDGKBSENT`: Removed `(unsigned long)` cast (1 instance)
  - `KDGKBDIACR(UC)`: Removed `(unsigned long)` cast (1 instance)

- **src/libkeymap/loadkeys.c**: Removed casts (6 instances)
  - `KDSKBENT`: 4 calls cleaned up
  - `KDSKBSENT`: 2 calls cleaned up
  - `KDSKBDIACRUC`, `KDSKBDIACR`: 2 calls cleaned up

- **src/libkeymap/summary.c**: Removed casts (5 instances)
  - All `ioctl()` calls with `KDSKBENT`, `KDGKBENT` cleaned up

**Why this matters**: Casting pointers to `unsigned long` then passing to variadic ioctl() breaks Fil-C's pointer capability tracking. The ioctl() syscall expects actual pointers, not integer representations.

### Keymap file changes (381 lines - NOT Fil-C related)
Multiple keymap data files modified:
- Changed `BackSpace` to `Delete` in various layouts
- Changed `Delete` to `Remove` in some keycodes
- Uncommented Hard Sign mappings in `ru1.map`
- These appear to be keymap correctness fixes, unrelated to Fil-C

Affected files:
- `i386/dvorak/dvorak-*.map` (2 files)
- `i386/fgGIod/tr_f-latin5.map`
- `i386/qwerty/lt*.map, no-latin1.map, ru*.map, se*.map, tr*.map, ua*.map` (15+ files)

## Build Artifact Bloat
None - changes are data files and source code.

## Assessment
- **Patch quality**: Moderate - mixes Fil-C fixes with keymap corrections
- **Actual changes**: 
  - Minor but critical (26 lines): Pointer cast removal essential for Fil-C
  - Unrelated (381 lines): Keymap data fixes should be separate patch
- **Recommendation**: Split into two patches:
  1. Fil-C compatibility: ioctl cast removal (~26 lines)
  2. Keymap corrections: data file fixes (~381 lines)
