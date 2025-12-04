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

### Setup (once per gem)
```bash
mkdir -p /tmp/gem-port && cd /tmp/gem-port
nix develop .#pkgsFilc.ruby.gems.<name> --command bash -c '
  source $stdenv/setup
  gem unpack $src
  cd *-*/
  patchPhase
  cd ext/<name>
  ruby extconf.rb
'
```

### Iterate
```bash
cd /tmp/gem-port/*-*/ext/<name>
nix develop .#pkgsFilc.ruby.gems.<name> --command make
```

Fix errors, re-run make. No need to re-unpack.

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
