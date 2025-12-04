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
**Issues:** VALUE param reused for int bitwise operation results

**Fixes:**
```nix
(for "nio4r" [
  native
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

**Note:** This also unlocks **puma** (Rails default web server).

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

### sqlite3, pg
**Status:** Work with just `native` flag (nixpkgs provides deps)

```nix
(for "sqlite3" [ native ])
(for "pg" [ native ])
```

## Known Problematic Gems

### nokogiri
**Issue:** Tries to build libxml2 from source, autoconf doesn't recognize `x86_64-unknown-linux-filc0`.

**Potential fix:** Use `--enable-system-libraries`, but then hits `-Werror` issues with Ruby headers.

**Status:** Needs deeper investigation into Ruby header warnings.
