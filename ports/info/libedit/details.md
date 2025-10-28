# libedit 20240808-3.1

## Summary
Trivial one-line patch to skip ISO 10646 compatibility check on Linux. Not Fil-C specific, just a Linux portability fix.

## Fil-C Compatibility Changes

**src/chartype.h**:
- Added `!defined(__linux__)` to existing platform check for `__STDC_ISO_10646__`
- Existing check already excludes macOS, OpenBSD, FreeBSD, DragonFly
- Comment explains: "first 127 code points are ASCII compatible, so ensure wchar_t indeed does ISO 10646"
- Not actually Fil-C-specific - just standard Linux portability

## Build Artifact Bloat
None - this is a clean patch with only source code changes.

## Assessment
- **Patch quality**: Minimal - one line change
- **Actual changes**: None (Fil-C-specific) - this is standard Linux portability
- **Pattern**: Platform detection adjustment, not memory safety related
