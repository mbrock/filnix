# cmake 3.30.2

## Summary
Simple library directory path change, not a Fil-C compatibility fix.

## Fil-C Compatibility Changes
None - this is a library installation path preference.

## Build Artifact Bloat
None - clean patch with only configuration changes.

## Other Changes
- **Modules/GNUInstallDirs.cmake**: Changed lib64 → lib for CMAKE_SIZEOF_VOID_P == 8
  - Forces libraries to install in `lib/` instead of `lib64/` on 64-bit systems
  - Likely for Nix consistency, not Fil-C memory safety

## Assessment
- **Patch quality**: Minimal, no bloat
- **Actual changes**: None (installation preference, not code changes)
