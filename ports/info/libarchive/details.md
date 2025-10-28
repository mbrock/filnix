# libarchive 3.7.4

## Summary
Minimal patch to support Fil-C's tagged pointer system in red-black tree implementation and pointer queue. Changes pointer-in-integer pattern to use tagged pointer operations and fixes type misuse in circular deque.

## Fil-C Compatibility Changes

**archive_rb.c/h (Red-Black Tree with Tagged Pointers)**:
- Changed `rb_info` from `uintptr_t` to `struct archive_rb_node *` in header
- Low 2 bits of `rb_info` used for flags (position, red/black color) while upper bits store parent pointer
- Added `<stdfil.h>` include
- Added `(uintptr_t)` casts when extracting integer value from pointer
- Replaced bitwise operations with tagged pointer operations:
  - `RB_SET_FATHER`: Uses `zretagptr(father, rb_info, ~RB_FLAG_MASK)` to preserve low bits while replacing pointer
  - `RB_MARK_RED`: Uses `zorptr(rb_info, RB_FLAG_RED)` to set red flag
  - `RB_MARK_BLACK`: Uses `zandptr(rb_info, ~RB_FLAG_RED)` to clear red flag
  - `RB_INVERT_COLOR`: Uses `zxorptr(rb_info, RB_FLAG_RED)` to toggle color
  - `RB_SET_POSITION`, `RB_ZERO_PROPERTIES`, `RB_COPY_PROPERTIES`, `RB_SWAP_PROPERTIES`: Similar tagged pointer operations

**archive_read_support_format_rar5.c (Pointer Queue)**:
- Changed `struct cdeque::arr` from `size_t*` to `void**`
- Removed cast `(size_t)` when storing pointer: `d->arr[d->end_pos] = item` instead of `d->arr[d->end_pos] = (size_t)item`
- Fixes anti-pattern of storing pointers as integers

## Build Artifact Bloat
None - this is a clean patch with only source code changes.

## Assessment
- **Patch quality**: Minimal - only necessary changes
- **Actual changes**: Moderate - red-black tree needs extensive tagged pointer operations, deque fix is trivial
- **Pattern**: Classic tagged pointer refactoring for data structure that packs flags into pointer low bits
