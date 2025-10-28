# Emacs 30.1

## Summary
Substantial changes to integrate Emacs' Lisp allocator with Fil-C's garbage collector (FUGC). All custom memory pools replaced with direct zgc_alloc calls, and several subsystems disabled for safety.

## Fil-C Compatibility Changes
- **src/alloc.c**: Core allocator integration
  - All Lisp object allocators wrapped with `if ((true)) zgc_alloc(...)` bypass
  - Disabled custom memory managers: `make_interval()`, `allocate_string()`, `allocate_string_data()`, `make_float()`, `Fcons()`, `allocate_vectorlike()`, `make_lisp_symbol()`
  - Added `zerror()` guards to `lisp_malloc()` and `lisp_align_malloc()` to catch unexpected usage
  - Disabled memory reserve system (`refill_memory_reserve()`)
  - Disabled garbage collection entirely (`maybe_garbage_collect()`, `garbage_collect()`)
  
- **src/eval.c**: Added `#include <stdfil.h>`

- **src/lisp.h**: Symbol pointer handling for FUGC
  - Modified `XBARE_SYMBOL()` to handle both lispsym table and heap-allocated symbols
  - Updated `make_lisp_symbol_internal()` to use `TAG_PTR_INITIALLY` for heap symbols
  - Removed `__builtin_unwind_init()` from `flush_stack_call_func()` (incompatible with Fil-C)

- **src/sysdep.c**: Disabled SIGSEGV handler completely
  - `init_sigsegv()` now returns 0 without setting up signal handler
  - Removes stack overflow handling (conflicts with FUGC's memory model)

## Build Artifact Bloat
None - patch contains only actual code changes.

## Assessment
- **Patch quality**: Minimal - clean code-only changes
- **Actual changes**: Substantial - fundamentally alters Emacs' memory management to use FUGC
- **Integration approach**: Complete replacement of custom allocators rather than gradual migration
