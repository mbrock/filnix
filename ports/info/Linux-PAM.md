# Linux-PAM v1.6.1 and v1.7.1

## Summary
Both versions apply Debian-specific patches that replace hardcoded system paths with build-time configuration macros and add Debian-specific PAM module features. No Fil-C-specific compatibility changes.

## Fil-C Compatibility Changes
None - these are Debian packaging patches, not Fil-C adaptations.

## Common Changes (Both Versions)
- **libpam/pam_private.h**: Replace `/etc/pam.conf`, `/etc/pam.d/*`, `/usr/lib/pam.d/*` with `SYSCONFDIR` and `LIBDIR` macros
- **Makefile.am/meson.build**: Add `-DLIBDIR` to build flags

## Additional Changes in v1.7.1
- **Symbol versioning**: Remove `-Wl,` prefix from `--version-script=` linker flags (for Fil-C linker compatibility)
- **pam_dispatch.c**: Remove cached chain jump logic
- **pam_handlers.c**: Add `@include` directive handling
- **pam_unix**: Add `obscure` password checking feature (new obscure.c file with 199 lines)
- **pam_limits**: Add `chroot` limit type, relaxed error handling
- **pam_motd**: Add dynamic MOTD script execution (`/etc/update-motd.d`)
- **pam_wheel**: Remove `use_uid` option (always use real UID)

## Build Artifact Bloat
None - all changes are source code.

## Assessment
- Patch quality: Clean Debian patches, no bloat
- Actual changes: Moderate (v1.6.1 minimal, v1.7.1 adds Debian features + symbol versioning fix)
