# dhcpcd 10.0.8

## Summary
Comprehensive red-black tree implementation changes to preserve capabilities during pointer tagging operations.

## Fil-C Compatibility Changes

### Pointer Tagging in Red-Black Trees
- **compat/rbtree.h**: Complete rewrite of pointer tagging macros
  - Added `#include <stdfil.h>`
  - Changed `rb_info` from `uintptr_t` to `struct rb_node*`

### Fil-C Pointer Operations
Pattern: Replace bitwise operations on pointers with Fil-C intrinsics that preserve capabilities

- **zretagptr(ptr, new_val, mask)**: Create new pointer preserving tagged bits
  - `RB_SET_FATHER(rb, father)`: `zretagptr((father), (rb)->rb_info, ~RB_FLAG_MASK)`

- **zorptr(ptr, bits)**: OR operation preserving capabilities
  - `RB_MARK_RED(rb)`: `zorptr((rb)->rb_info, RB_FLAG_RED)`

- **zandptr(ptr, mask)**: AND operation preserving capabilities
  - `RB_MARK_BLACK(rb)`: `zandptr((rb)->rb_info, ~RB_FLAG_RED)`
  - `RB_ZERO_PROPERTIES(rb)`: `zandptr((rb)->rb_info, ~RB_FLAG_MASK)`

- **zxorptr(ptr, bits)**: XOR operation preserving capabilities
  - `RB_INVERT_COLOR(rb)`: `zxorptr((rb)->rb_info, RB_FLAG_RED)`
  - `RB_COPY_PROPERTIES`: Complex XOR with mask
  - `RB_SWAP_PROPERTIES`: XOR swap pattern

### Casts Added
- All macro uses that extract values now cast to `uintptr_t` for arithmetic
- `RB_FATHER`, `RB_POSITION`, `RB_RED_P`, `RB_BLACK_P` macros cast before bit testing
- Preserves pointer in storage, extracts integer only for bit checks

## Build Artifact Bloat
None - clean patch with only source code changes.

## Assessment
- **Patch quality**: Minimal, no bloat
- **Actual changes**: Substantial (complete pointer tagging rewrite using Fil-C intrinsics)
