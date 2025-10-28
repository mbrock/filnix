# binutils 2.43.1

## Summary
Substantial changes converting integer-based pointer storage to void* throughout chew.c, plus splay tree changes, template instantiations, sbrk disabling, and linker flag adjustments.

## Fil-C Compatibility Changes

### Pointer Table Conversions
- **bfd/doc/chew.c**: Extensive intptr_t → void* conversions
  - Changed `pcu.l` from `intptr_t` to `void*` in union
  - Stack (`istack[]`, `isp`) converted from `intptr_t*` to `void**`
  - Internal mode tracking changed to `void**`
  - All integer/pointer conversions now use explicit casts
  - Pattern: values stored as pointers, cast to intptr_t only for printing/comparison

- **include/splay-tree.h**: Changed splay_tree_key/value from `uintptr_t` to `void*`
  - Fundamental type change for pointer-based data structures

### sbrk Disabling
- **libiberty/xmalloc.c**: Undefed HAVE_SBRK
  - sbrk incompatible with Fil-C's memory management

### Linker Adjustments
- **libctf/configure.ac**: Removed `-Wl,` prefix from `--version-script` flag
- **libsframe/Makefile.am**: Removed `-Wl,` prefix from `--version-script` flag
  - Fil-C linker expects flags directly without `-Wl,` wrapper

### Template Instantiations
- **gold/symtab.cc**: Added explicit template instantiations for `compute_final_value<32>` and `compute_final_value<64>`
  - Required for Fil-C's stricter template handling

## Build Artifact Bloat
None - clean patch with only source code and build configuration changes.

## Assessment
- **Patch quality**: Minimal, no bloat
- **Actual changes**: Substantial (pointer table conversions throughout chew.c, multiple subsystem changes)
