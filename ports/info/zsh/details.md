# zsh v5.8.0.1-dev

## Summary
Zsh required disabling its custom arena allocator in favor of standard malloc/free, plus a struct layout fix for HashNode compatibility.

## Fil-C Compatibility Changes

### Custom Allocator Bypass
- **File**: `Src/mem.c`
- **Functions**: `zhalloc()`, `hrealloc()`
- **Changes**:
  - Added `if ((1)) return malloc(size);` at start of `zhalloc()`
  - Added `if ((1)) { char* result = malloc(new); memcpy(result, p, old < new ? old : new); return result; }` in `hrealloc()`
- **Why**: Zsh uses custom heap allocator with arena-style memory management. This likely confuses Fil-C's garbage collector or uses pointer tricks incompatible with capabilities. Forcing standard malloc/free ensures proper tracking.
- **Pattern**: Allocator compatibility bypass

### Struct Layout Fix
- **File**: `Src/Zle/zle_keymap.c`
- **Struct**: `struct key`
- **Change**: Added `int flags;` field after `char *nam;`
- **Why**: `struct key` is used as a `HashNode` (includes `flags` field), but was missing this member. Fil-C's stricter type checking likely caught this layout mismatch.
- **Pattern**: Struct alignment/layout correction

## Build Artifact Bloat
Minor additions (not bloat, but generated files):
- `Doc/help/.cvsignore` (1 line) - CVS ignore file
- `Doc/help/.distfiles` (3 lines) - Distribution file list  
- `stamp-h.in` (1 line) - Autotools timestamp file

These are trivial build system files, not significant bloat.

## Assessment
- **Patch quality**: Minimal, targeted fixes
- **Actual changes**: Moderate - allocator bypass is significant behavioral change
- **Complexity**: The allocator bypass is a workaround rather than a proper fix, but acceptable for Fil-C porting. The struct fix is trivial.
