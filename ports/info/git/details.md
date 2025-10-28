# Git 2.46.0

## Summary
Extensive changes to option parsing infrastructure to eliminate intptr_t casts, replacing them with direct void* pointers for Fil-C's strict pointer tracking.

## Fil-C Compatibility Changes

### Core infrastructure changes
- **parse-options.h**: Changed struct option field type
  - `intptr_t defval` → `void *defval`
  - Updated all OPT_* macros to use `(void *)(i)` casts instead of raw integer

- **parse-options.c**: Added explicit casts when reading defval
  - Changed `opt->defval` → `(intptr_t)opt->defval` in:
    - `OPTION_BIT`, `OPTION_NEGBIT`, `OPTION_BITOP`, `OPTION_SET_INT`
    - `OPTION_INTEGER`, `OPTION_MAGNITUDE` handlers

- **compat/bswap.h**: Disabled inline assembly for Fil-C
  - Added `&& !defined(__FILC__)` to GNUC bswap implementation guard

### Builtin command changes (40+ files modified)
All builtin commands updated to cast integer constants when passing to option structs:
- `(intptr_t)""` for default string values
- `(void *)CONST` for integer default values
- Examples across: `builtin/am.c`, `builtin/commit.c`, `builtin/merge.c`, `builtin/tag.c`, etc.

### Pattern applied consistently
- Before: `PARSE_OPT_OPTARG, NULL, (intptr_t)default_value`
- After: `PARSE_OPT_OPTARG, NULL, default_value` (for strings)
- After: `PARSE_OPT_OPTARG, NULL, (void *)VALUE` (for integers)

## Build Artifact Bloat
None - all changes are code modifications.

## Assessment
- **Patch quality**: Minimal - systematic refactoring across codebase
- **Actual changes**: Substantial scope but mechanical
  - Changes required because Fil-C tracks pointer provenance strictly
  - Can't cast integers to pointers without explicit void* cast
  - Pattern applied consistently across ~40 files
- **Type safety improvement**: Actually improves clarity by making pointer/integer distinction explicit
