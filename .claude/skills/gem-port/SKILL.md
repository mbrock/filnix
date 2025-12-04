---
name: gem-port
description: Port Ruby gems with native C extensions to Fil-C. Use when fixing gem compilation errors, VALUE/int type mismatches, rb_attr/rb_protect issues, or using ast-grep for Ruby C extensions.
---

# Fil-C Ruby Gem Porting

## Context

Fil-C is a memory-safe C compiler. Ruby's VALUE type becomes a pointer (`struct rb_value_unit_struct *`) instead of an integer. This breaks code that:
- Passes int literals where VALUE expected (Qfalse, Qtrue, ERROR_TOKEN)
- Stores VALUE in int variables
- Does bitwise ops on VALUE
- Mixes VALUE and ID types

## Workflow

Each command runs independently (no persistent shell). Use `ruby_3_3` not `ruby`.

### 1. Unpack gem
```bash
rm -rf /tmp/gem-port && mkdir -p /tmp/gem-port
nix develop .#pkgsFilc.ruby_3_3.gems.<name> --command bash -c 'gem unpack $src'
```

### 2. Find ext structure
```bash
ls /tmp/gem-port/*/ext/
```
Note: Some gems have `ext/<name>/`, others have files directly in `ext/`.

### 3. Run extconf.rb
```bash
nix develop .#pkgsFilc.ruby_3_3.gems.<name> --command bash -c \
  'cd /tmp/gem-port/*/ext && ruby extconf.rb'
# Or if nested: cd /tmp/gem-port/*/ext/<name>
```

### 4. Build and capture errors
```bash
nix develop .#pkgsFilc.ruby_3_3.gems.<name> --command bash -c \
  'cd /tmp/gem-port/*/ext && make 2>&1' > /tmp/build.log
cat /tmp/build.log | head -100
```

### 5. Fix and iterate
Edit files in `/tmp/gem-port/*/ext/` directly, then re-run step 4. No need to re-unpack or re-run extconf.

### 6. Add to rubyports.nix and verify
```bash
nix build .#pkgsFilc.ruby_3_3.gems.<name> -L
```

## ast-grep for C Function Calls

**Critical**: Use `--selector call_expression` for C function calls, otherwise patterns parse as macros.

```bash
ast-grep run -p 'rb_attr($A, $B, $C, $D, Qfalse)' \
             -r 'rb_attr($A, $B, $C, $D, 0)' \
             -l c --selector call_expression -U .
```

## Adding Fixes to rubyports.nix

Use the helpers in rubyports.nix:

```nix
(for "gemname" [
  native
  (astGrep "pattern($A)" "replacement($A)")
  (replace "path/to/file.c" "old string" "new string")
])
```

See REFERENCE.md for common patterns and FIXES.md for per-gem solutions.
