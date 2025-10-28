# Fil-C Patch Analysis

This directory contains analysis of all Fil-C patches for ported software.

Each subdirectory corresponds to a patched project and contains:
- `oneliner.txt` - One-sentence summary of the patch
- `details.md` - Detailed analysis of changes

## Analysis Guidelines for Subagents

When analyzing a patch, focus on:

1. **Actual Fil-C compatibility changes** - Ignore build artifacts
2. **Common patterns**: pointer tables, alignment, symbol versioning, vfork→fork
3. **Build artifact bloat**: autotools files, CI configs, binaries
4. **Patch quality**: Are changes minimal? Is there bloat to exclude?

### Build Artifacts to Ignore

These appear in patches but should be excluded:
- Autotools: `configure`, `*.m4`, `config.{guess,sub}`, `install-sh`, `missing`, `depcomp`, `compile`, `test-driver`, `ltmain.sh`, `ar-lib`
- CI: `.github/*`, `.gitlab-ci/*`
- Generated: `INSTALL`, `Makefile.in`, `aclocal.m4`
- Binaries: `*.dll`, `*.exe`, `*.lib`, `*.wad`

### Output Format

**oneliner.txt:**
```
One sentence describing the main Fil-C compatibility changes
```

**details.md:**
```markdown
# Project Name vX.Y.Z

## Summary
Brief overview of what changes were needed for Fil-C.

## Fil-C Compatibility Changes
- Specific code modifications (with file references)
- Patterns used (pointer tables, alignment fixes, etc.)

## Build Artifact Bloat
- List of unnecessary files in patch
- Recommendations for exclusion patterns

## Assessment
- Patch quality: minimal/moderate/excessive bloat
- Actual changes: substantial/minor/none
```
