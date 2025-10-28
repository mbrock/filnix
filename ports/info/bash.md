# bash 5.2.32

## Summary
Single-line patch changing flexible array member type for memory safety compatibility.

## Fil-C Compatibility Changes
- **unwind_prot.c**: Changed `char desired_setting[1]` to `void *desired_setting[1]` in SAVED_VAR struct
  - Flexible array member must use pointer type for correct capability tracking
  - Ensures proper alignment and pointer table (`zptrtable`) compatibility

## Build Artifact Bloat
None - clean patch with only source code changes.

## Assessment
- **Patch quality**: Minimal, no bloat
- **Actual changes**: Minor (single type change)
