# libxkbcommon xkbcommon-1.11.0

## Summary
Trivial patch changing symbol versioning linker flag format across all libraries.

## Fil-C Compatibility Changes

**meson.build (Symbol Versioning Everywhere)**:
- Changed linker probe test:
  - Old: `-Wl,--version-script=@meson_test_map@`
  - New: `--version-script=@meson_test_map@`
  - Updated variable name: `have_version_script`
- Changed link args for three libraries:
  - **libxkbcommon**: `--version-script=@xkbcommon_map@`
  - **libxkbcommon-x11**: `--version-script=...xkbcommon-x11.map`
  - **libxkbregistry**: `--version-script=...xkbregistry.map`
- Fil-C linker accepts `--version-script` directly without `-Wl,` wrapper

## Build Artifact Bloat
None - this is a clean patch with only build configuration changes.

## Assessment
- **Patch quality**: Minimal - mechanical flag replacement
- **Actual changes**: Trivial - linker flag syntax only
- **Pattern**: Consistent with other ports (libevdev, libinput, libffi, etc)
- Symbol versioning is standard practice, just different syntax for Fil-C linker
