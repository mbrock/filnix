# e2fsprogs 1.47.1

## Summary
Systematic removal of sbrk usage for memory tracking, replacing with NULL pointers.

## Fil-C Compatibility Changes

### sbrk Removal
sbrk(0) used to query current program break (heap end) for memory usage tracking. Fil-C doesn't support sbrk, so all calls replaced with NULL.

- **e2fsck/iscan.c**: 
  - `init_resource_track`: `track->brk_start = NULL` (was `sbrk(0)`)
  - `print_resource_track`: Two occurrences of `(char*)NULL` (was `(char*)sbrk(0)`)

- **e2fsck/scantest.c**:
  - `init_resource_track`: `track->brk_start = NULL` (was `sbrk(0)`)
  - `print_resource_track`: `(char*)NULL` (was `(char*)sbrk(0)`)

- **e2fsck/util.c**:
  - `init_resource_track`: `track->brk_start = NULL` (was `sbrk(0)`)
  - `print_resource_track`: Two occurrences of `(char*)NULL` (was `(char*)sbrk(0)`)

- **resize/resource_track.c**:
  - `init_resource_track`: `track->brk_start = NULL` (was `sbrk(0)`)
  - `print_resource_track`: `(char*)NULL` (was `(char*)sbrk(0)`)

### Impact
Memory usage tracking will report incorrect values (all calculations from NULL base), but code remains functional. This is acceptable since:
- Resource tracking is diagnostic/informational only
- Fil-C's GC makes sbrk-based tracking meaningless anyway

## Build Artifact Bloat
None - clean patch with only source code changes.

## Assessment
- **Patch quality**: Minimal, no bloat
- **Actual changes**: Minor (systematic sbrk removal, functionality degradation acceptable)
