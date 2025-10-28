# libxml2 v2.14.4

## Summary
Minimal patch adding atomic qualifier to one catalog entry field for Fil-C thread safety.

## Fil-C Compatibility Changes
- **catalog.c**: Changed `struct _xmlCatalogEntry *children` to `struct _xmlCatalogEntry *_Atomic children` (line 10) to ensure atomic access to the children field in catalog entry structures

## Build Artifact Bloat
None - this is a minimal patch with actual code changes only.

## Assessment
- Patch quality: Minimal, no bloat
- Actual changes: Minor (single field qualifier change for atomicity)
