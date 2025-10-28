# dash 0.5.12

## Summary
Single-line vfork→fork change for Fil-C compatibility, buried in massive autotools bloat.

## Fil-C Compatibility Changes
- **src/jobs.c**: Changed `vfork()` to `fork()`
  - vfork's shared address space semantics incompatible with Fil-C's capability tracking
  - Standard fork provides proper memory isolation

## Build Artifact Bloat
Extensive autotools files that should be excluded:

### Generated Files (368+ lines each)
- **INSTALL**: Generic autotools installation instructions (368 lines)
- **compile**: Automake compiler wrapper script (348 lines)
- **install-sh**: Automake install script (over 500 lines)
- **missing**: Automake missing program wrapper (215 lines)

### Recommendations
These are standard autotools artifacts that should be:
- Generated during build, not committed to patches
- Excluded with patterns: `INSTALL`, `compile`, `install-sh`, `missing`

## Assessment
- **Patch quality**: Excessive bloat (autotools scripts dwarf actual code change)
- **Actual changes**: Minor (single vfork→fork replacement)
