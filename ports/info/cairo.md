# cairo 1.18.0

## Summary
Systematic conversion of GLib once-initialization patterns from gsize to gpointer for proper type handling.

## Fil-C Compatibility Changes

### GObject Type Registration
- **util/cairo-gobject/cairo-gobject-enums.c**: Changed all enum type registration functions
  - Pattern repeated ~25 times across different enum types
  - Changed `static gsize type_ret = 0` to `static gpointer type_ret = 0`
  - Changed `g_once_init_enter(&type_ret)` to `g_once_init_enter_pointer(&type_ret)`
  - Changed `g_once_init_leave(&type_ret, type)` to `g_once_init_leave_pointer(&type_ret, type)`
  
- **util/cairo-gobject/cairo-gobject-structs.c**: Updated CAIRO_GOBJECT_DEFINE_TYPE_FULL macro
  - Same gsize → gpointer pattern
  - Same g_once_init_* function changes

### Rationale
- GLib's gsize-based once-init conflates pointer storage with size type
- Fil-C requires proper pointer types for capability tracking
- gpointer variants ensure type safety

## Build Artifact Bloat
None - clean patch with only source code changes.

## Assessment
- **Patch quality**: Minimal, no bloat
- **Actual changes**: Minor (systematic type changes, no algorithm changes)
