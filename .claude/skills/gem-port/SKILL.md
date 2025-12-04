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
- Uses `switch` on VALUE (case labels must be integer constants)

## Workflow

Each command runs independently (no persistent shell). Use `ruby_3_3` not `ruby`.

### 1. Unpack gem
```bash
rm -rf /tmp/gem-port && mkdir -p /tmp/gem-port
nix develop .#pkgsFilc.ruby_3_3.gems.<name> --command bash -c 'gem unpack $src'
# Move to /tmp if unpacked in current dir
mv *<name>* /tmp/gem-port/ 2>/dev/null || true
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
# Always capture stderr and check exit code
nix build .#pkgsFilc.ruby_3_3.gems.<name> 2>&1; echo "EXIT: $?"
ls result/ 2>&1
```

## ast-grep Usage

**ALWAYS use ast-grep for pattern-based code fixes.** It handles whitespace variations that break string replacement.

### Selectors
Different C constructs need different selectors:
- `call_expression` - function calls like `rb_attr($A, $B, Qfalse)`
- `switch_statement` - switch blocks with case labels
- `declaration` - variable declarations

### Examples

**Function call replacement:**
```bash
ast-grep run -p 'rb_attr($A, $B, $C, $D, Qfalse)' \
             -r 'rb_attr($A, $B, $C, $D, 0)' \
             -l c --selector call_expression -U .
```

**Switch to if-else (VALUE can't be case label):**
```bash
ast-grep run \
  -p 'switch (rb_range_beg_len($A, $B, $L, $S, $F)) { case Qfalse: break; case Qnil: return Qnil; default: return subseq($X, $Y, $Z); }' \
  -r '{ VALUE r = rb_range_beg_len($A, $B, $L, $S, $F); if (r == Qfalse) { } else if (r == Qnil) { return Qnil; } else { return subseq($X, $Y, $Z); } }' \
  -l c --selector switch_statement -U .
```

**Finding patterns (no -U):**
```bash
ast-grep run -p 'static VALUE $NAME;' -l c .
ast-grep run -p 'case Q$CONST:' -l c .
```

## rubyports.nix Helpers

```nix
# String replacement (fragile - prefer ast-grep)
(replace "path/to/file.c" "old string" "new string")

# ast-grep with call_expression selector
(astGrep "pattern($A)" "replacement($A)")

# ast-grep with custom selector
(astGrepSel "switch_statement" "switch(...)" "if-else...")
```

## Common Patterns

| Issue | Pattern | Fix |
|-------|---------|-----|
| VALUE→ID for rb_intern | `static VALUE id = rb_intern(...)` | `static ID id = ...` |
| int→VALUE in switch | `case Qfalse: case Qnil:` | Convert to if-else |
| VALUE reused for int | `arg = ... (bitwise op)` | Use separate int variable |
| int return from VALUE func | `return 1;` in VALUE function | `return Qtrue;` |

See REFERENCE.md for full patterns, FIXES.md for per-gem solutions, and AST_GREP.md for comprehensive ast-grep documentation.
