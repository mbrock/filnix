# Gettext 0.22.5

## Summary
Minor pointer arithmetic fix and wholesale symbol renaming with "pizlonated_" prefix for libtextstyle library to avoid symbol conflicts.

## Fil-C Compatibility Changes
- **gettext-runtime/intl/localealias.c**: Pointer arithmetic fix
  - Changed `map[i].alias += new_pool - string_space` to `map[i].alias = new_pool + (map[i].alias - string_space)`
  - Same for `map[i].value`
  - Prevents undefined behavior from pointer difference used as integer offset

- **libtextstyle/lib/libtextstyle.sym.in**: Symbol versioning for Fil-C
  - All 130 exported symbols renamed with "pizlonated_" prefix
  - Example: `_libtextstyle_version` → `pizlonated__libtextstyle_version`
  - Prevents symbol conflicts in Fil-C's unified namespace

- **Test skips**:
  - `gettext-tools/tests/msgfmt-6`: Division by zero test (exit 77)
  - `gettext-tools/tests/msginit-4`: Unicode CLDR test (exit 77 with FIXME note)

## Build Artifact Bloat
None - all changes are actual code modifications.

## Assessment
- **Patch quality**: Minimal - focused changes only
- **Actual changes**: Minor but necessary
  - Pointer arithmetic fix is essential for memory safety
  - Symbol renaming prevents linker conflicts in Fil-C environment
  - Test skips indicate compatibility issues to investigate
