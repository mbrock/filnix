# seatd 0.9.1

## Summary
Trivial change to pass version script directly to linker instead of through `-Wl,`.

## Fil-C Compatibility Changes

### meson.build
```diff
-symbols_flag = '-Wl,--version-script,@0@/@1@'.format(meson.current_source_dir(), symbols_file)
+symbols_flag = '--version-script=@0@/@1@'.format(meson.current_source_dir(), symbols_file)
```

**Explanation:**
- `-Wl,` is GCC/Clang syntax for passing flags to linker
- Fil-C compiler may invoke linker directly, requiring bare flag
- Also changed `,` separator to `=` (more portable)

**Impact:** Build system compatibility, not a code change

## Build Artifact Bloat
None.

## Assessment
- **Patch quality**: Minimal
- **Actual changes**: Trivial build fix
- **Fil-C relevance**: Low - linker invocation detail
