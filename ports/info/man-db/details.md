# man-db v2.12.1

## Summary
Removes unsafe integer-to-pointer cast in filesystem I/O control call.

## Fil-C Compatibility Changes
- **lib/orderfiles.c**: Changed `ioctl(fd, FS_IOC_FIEMAP, (unsigned long) &fm)` to `ioctl(fd, FS_IOC_FIEMAP, &fm)`
  - Removes unnecessary and unsafe cast from pointer to `unsigned long` and back
  - FIEMAP ioctl expects a pointer to struct, no cast needed

## Build Artifact Bloat
None - single line change.

## Assessment
- Patch quality: Minimal, correct fix
- Actual changes: Minor (removes one unsafe cast)
