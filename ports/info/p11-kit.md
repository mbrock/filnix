# p11-kit v0.25.5

## Summary
Simple linker flag adjustment for Fil-C compatibility in Meson build files.

## Fil-C Compatibility Changes
- **p11-kit/meson.build**: 
  - Line 9: Change `'-Wl,--version-script,' + libp11_kit_symbol_map` to `'--version-script=' + libp11_kit_symbol_map`
  - Line 19: Change `'-Wl,--version-script,' + p11_module_symbol_map` to `'--version-script=' + p11_module_symbol_map`
  - Fil-C linker expects version script flags without `-Wl,` wrapper

## Build Artifact Bloat
None - only build system changes.

## Assessment
- Patch quality: Minimal, correct fix
- Actual changes: Minor (symbol versioning flag format for Fil-C linker)
