# Per-Gem Fixes Catalog

## Working Gems

### openssl
**Issues:** Multiple VALUE/int mismatches

**Fixes:**
```nix
(for "openssl" [
  native
  # rb_attr takes int, not VALUE
  (astGrep "rb_attr($A, $B, $C, $D, Qfalse)" "rb_attr($A, $B, $C, $D, 0)")
  # rb_cstr_to_inum takes int badcheck
  (astGrep "rb_cstr_to_inum($A, $B, Qtrue)" "rb_cstr_to_inum($A, $B, 1)")
  # rb_str_new size cast
  (astGrep "rb_str_new(NULL, (long)$A)" "rb_str_new(NULL, (long)(uintptr_t)$A)")
  # rb_protect VALUE/long cast
  (replace "ext/openssl/ossl.c"
    "str = rb_protect(ossl_str_new_i, len, &state);"
    "str = rb_protect(ossl_str_new_i, (VALUE)(uintptr_t)len, &state);")
  # int ret = Qnil (function returns int)
  (replace "ext/openssl/ossl_pkcs7.c"
    "int i, ret = Qnil;"
    "int i, ret = -1;")
  # VALUE ret stores ID values
  (replace "ext/openssl/ossl_pkey_ec.c"
    "point_conversion_form_t form;\n    VALUE ret;"
    "point_conversion_form_t form;\n    ID ret;")
])
```

### racc
**Issue:** ERROR_TOKEN (int 1) passed where VALUE expected

**Fix:**
```nix
(for "racc" [
  native
  (replace "ext/racc/cparse/cparse.c"
    "SHIFT(v, act, ERROR_TOKEN, val)"
    "SHIFT(v, act, vERROR_TOKEN, val)")
])
```

### msgpack
**Issue:** VALUE array element assigned to unsigned long

**Fixes:**
```nix
(for "msgpack" [
  native
  (replace "ext/msgpack/buffer_class.c"
    "unsigned long max = ((VALUE*) args)[2];"
    "unsigned long max = (unsigned long)(uintptr_t)((VALUE*) args)[2];")
  (replace "ext/msgpack/buffer_class.c"
    "(VALUE) max,"
    "(VALUE)(uintptr_t) max,")
])
```

### ffi
**Issues:** Custom trampolines incompatible, VALUE bitwise ops

**Fixes:**
```nix
(for "ffi" [
  native
  (addCFlag "-DUSE_FFI_ALLOC")
  # Use system libffi
  (replace "ext/ffi_c/extconf.rb"
    "libffi_ok &&= have_library(\"ffi\""
    "$libs << \" -lffi\"; libffi_ok &&= true || have_library(\"ffi\"")
  # VALUE bitwise op
  (replace "ext/ffi_c/Struct.h"
    "#define FIELD_CACHE_LOOKUP(this, sym) ( &(this)->cache_row[((sym) >> 8) & 0xff] )"
    "#define FIELD_CACHE_LOOKUP(this, sym) ( &(this)->cache_row[(((uintptr_t)(sym)) >> 8) & 0xff] )")
])
```

### ruby-terminfo
**Issue:** RTEST with non-VALUE

**Fix:**
```nix
(for "ruby-terminfo" [
  native
  (replace "terminfo.c" "RTEST(ret)" "RTEST((VALUE)ret)")
])
```

### eventmachine
**Issues:** `Intern_*` symbols declared as VALUE but should be ID; int assigned to VALUE var

**Fixes:**
```nix
(for "eventmachine" [
  native
  # Intern_* are IDs from rb_intern(), not VALUEs
  (replace "ext/rubymain.cpp" "static VALUE Intern_" "static ID Intern_")
  # Don't reuse VALUE arg for int
  (replace "ext/rubymain.cpp"
    "arg = (NIL_P(arg)) ? -1 : NUM2INT (arg);"
    "int limit = (NIL_P(arg)) ? -1 : NUM2INT(arg);")
  (replace "ext/rubymain.cpp"
    "return INT2NUM (evma_set_rlimit_nofile (arg));"
    "return INT2NUM(evma_set_rlimit_nofile(limit));")
])
```

### nio4r
**Issues:**
1. VALUE param reused for int bitwise operation results
2. Bundled libev has inline asm `mfence` that Fil-C can't handle

**Fixes:**
```nix
(for "nio4r" [
  native
  # Replace inline asm mfence macro with __atomic_thread_fence in bundled libev
  # ast-grep matches #define as preproc_def with body as preproc_arg (raw text)
  # Must match exact whitespace in the #define line
  (astGrepAny
    "#define ECB_MEMORY_FENCE         __asm__ __volatile__ (\"mfence\"   : : : \"memory\")"
    "#define ECB_MEMORY_FENCE         __atomic_thread_fence(__ATOMIC_SEQ_CST)")
  # Don't reuse VALUE param for int bitwise op results
  (replace "ext/nio4r/monitor.c"
    "interest = monitor->interests | NIO_Monitor_symbol2interest(interest);"
    "int new_interest = monitor->interests | NIO_Monitor_symbol2interest(interest);")
  (replace "ext/nio4r/monitor.c"
    "interest = monitor->interests & ~NIO_Monitor_symbol2interest(interest);"
    "int new_interest = monitor->interests & ~NIO_Monitor_symbol2interest(interest);")
  (replace "ext/nio4r/monitor.c"
    "NIO_Monitor_update_interests(self, (int)interest);"
    "NIO_Monitor_update_interests(self, new_interest);")
])
```

**Note:** Uses bundled libev (not system libev) because it has Ruby GVL-release patches (`rb_thread_call_without_gvl`).

**Note:** This unlocks **puma** (Rails default web server) - tested working!

### curb
**Issues:** `idCall`/`idJoin` declared as VALUE but should be ID; int return from VALUE function

**Fixes:**
```nix
(for "curb" [
  native
  (replace "ext/curb_easy.c" "static VALUE idCall;" "static ID idCall;")
  (replace "ext/curb_easy.c" "static VALUE idJoin;" "static ID idJoin;")
  (replace "ext/curb_multi.c" "static VALUE idCall;" "static ID idCall;")
  (replace "ext/curb_postfield.c" "static VALUE idCall;" "static ID idCall;")
  (replace "ext/curb_multi.c"
    "return method == Qtrue ? 1 : 0;"
    "return (method == Qtrue) ? Qtrue : Qfalse;")
])
```

### nokogiri
**Issues:** `switch` on VALUE (case Qfalse/Qnil) - VALUE is pointer in Fil-C, can't be switch case label

**Fixes:** Use ast-grep with `switch_statement` selector to convert to if-else:
```nix
(for "nokogiri" [
  native
  (astGrepSel "switch_statement"
    "switch (rb_range_beg_len($ARG, $BEG, $LEN, $SIZE, $FLAG)) { case Qfalse: break; case Qnil: return Qnil; default: return subseq($SELF, $B, $L); }"
    "{ VALUE range_result = rb_range_beg_len($ARG, $BEG, $LEN, $SIZE, $FLAG); if (range_result == Qfalse) { } else if (range_result == Qnil) { return Qnil; } else { return subseq($SELF, $B, $L); } }")
])
```

### date
**Issues:** VALUE to st_index_t conversion in hash function (m_nth and m_sf return VALUE)

**Fixes:**
```nix
(for "date" [
  native
  (astGrepSel "assignment_expression" "h[0] = m_nth($X)" "h[0] = (st_index_t)(uintptr_t)m_nth($X)")
  (astGrepSel "assignment_expression" "h[3] = m_sf($X)" "h[3] = (st_index_t)(uintptr_t)m_sf($X)")
])
```

**Note:** This also unlocks **psych** (YAML parser) and **stringio**.

### bigdecimal
**Issues:** switch on VALUE with case Qnil/Qtrue/Qfalse; int functions returning Qfalse; rb_protect int↔VALUE casting

**Fixes:**
```nix
(for "bigdecimal" [
  native
  # Convert switch(val) case Qnil/Qtrue/Qfalse to if-else
  (replace "ext/bigdecimal/bigdecimal.c"
    "switch (val) {\n      case Qnil:\n      case Qtrue:\n      case Qfalse:"
    "if (val == Qnil || val == Qtrue || val == Qfalse) {")
  (replace "ext/bigdecimal/bigdecimal.c"
    "return Qnil;\n\n      default:\n        break;\n    }"
    "return Qnil;\n    }")
  # is_zero()/is_one() return int, not VALUE
  (astGrepSel "case_statement" "case T_BIGNUM: return Qfalse;" "case T_BIGNUM: return 0;")
  # rb_protect callback: store result in struct instead of casting
  (replace "ext/bigdecimal/bigdecimal.c"
    "const char *exp_chr;\n  size_t ne;\n};"
    "const char *exp_chr;\n  size_t ne;\n  int result;\n};")
  (replace "ext/bigdecimal/bigdecimal.c"
    "return (VALUE)VpCtoV(...);"
    "x->result = VpCtoV(...); return Qnil;")
  (replace "ext/bigdecimal/bigdecimal.c"
    "VALUE result = rb_protect(...);"
    "rb_protect(...);")
  (replace "ext/bigdecimal/bigdecimal.c"
    "return (int)result;"
    "return args.result;")
])
```

**Note:** This unlocks **Rails** and its dependencies.

### io-console
**Issues:** switch on VALUE with case Qtrue/Qfalse/Qnil/Qundef

**Fixes:** Cast switch expression and case labels to uintptr_t:
```nix
(for "io-console" [
  native
  # Cast switch expressions to uintptr_t
  (astGrepAny "switch ($X)" "switch ((uintptr_t)$X)")
  # Cast case labels to uintptr_t
  (astGrepAny "case Qtrue:" "case (uintptr_t)Qtrue:")
  (astGrepAny "case Qfalse:" "case (uintptr_t)Qfalse:")
  (astGrepAny "case Qundef:" "case (uintptr_t)Qundef:")
  (astGrepAny "case Qnil:" "case (uintptr_t)Qnil:")
])
```

**Note:** Uses `astGrepAny` (no selector) for switch/case patterns.

### sqlite3, pg
**Status:** Work with just `native` flag (nixpkgs provides deps)

```nix
(for "sqlite3" [ native ])
(for "pg" [ native ])
```

## Known Problematic Gems

(None currently - nokogiri now works!)

## ast-grep Reference

### How ast-grep Parses C Code

ast-grep uses tree-sitter to parse code into an AST. Key insights for C:

1. **Preprocessor Directives**: `#define` macros ARE matchable!
   - Parsed as `preproc_def` nodes
   - Macro body is `preproc_arg` (raw text, not parsed as C code)
   - Must match exact whitespace in the pattern

2. **Function Calls**: Plain `test($A)` may be ambiguous
   - tree-sitter-c may parse as `macro_type_specifier`
   - Add context: use `test($A);` with `--selector call_expression`

3. **Inline ASM**: `__asm__ __volatile__ (...)` parses as `gnu_asm_expression`

### Debugging Patterns

Use `--debug-query` to see how patterns parse:
```bash
ast-grep run --lang c --pattern 'your_pattern' --debug-query=ast
ast-grep run --lang c --pattern 'your_pattern' --debug-query=cst
```

### Our Helpers in rubyports.nix

```nix
# With call_expression selector (for function calls)
astGrep = pattern: rewrite: ...

# Without selector (for switch/case, #define, etc.)
astGrepAny = pattern: rewrite: ...

# With custom selector
astGrepSel = selector: pattern: rewrite: ...
```

### Pattern Examples

```nix
# Function call pattern
(astGrep "rb_attr($A, $B, $C, $D, Qfalse)" "rb_attr($A, $B, $C, $D, 0)")

# Switch statement (must use if-else rewrite in C)
(astGrepSel "switch_statement" "switch (expr) { case Qfalse: ... }" "{ if (expr == Qfalse) ... }")

# Preprocessor macro (exact whitespace matters!)
(astGrepAny
  "#define ECB_MEMORY_FENCE         __asm__ __volatile__ (\"mfence\"   : : : \"memory\")"
  "#define ECB_MEMORY_FENCE         __atomic_thread_fence(__ATOMIC_SEQ_CST)")
```

### Resources

- [ast-grep docs](https://ast-grep.github.io/)
- [Pattern syntax](https://ast-grep.github.io/guide/pattern-syntax.html)
- [C language catalog](https://ast-grep.github.io/catalog/c/)
- [Deep dive on patterns](https://ast-grep.github.io/advanced/pattern-parse.html)
