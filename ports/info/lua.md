# Lua v5.4.7

## Summary
Simple build configuration changes to remove readline dependency and add debug symbols.

## Fil-C Compatibility Changes
None - these are build configuration changes, not code adaptations.

## Build Configuration Changes
- **makefile**: 
  - Remove `-DLUA_USE_READLINE` from `MYCFLAGS`
  - Remove `-lreadline` from `MYLIBS`
  - Add `-g` debug flag to `CFLAGS`

## Build Artifact Bloat
None - only makefile changes.

## Assessment
- Patch quality: Minimal, no bloat
- Actual changes: None (build-only changes, likely to simplify Fil-C compilation)
