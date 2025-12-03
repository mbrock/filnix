# Ruby Gem Build Results (Fil-C)

Build sweep of native Ruby gems with C extensions.

## Results: 16/52 OK

### Working Gems (16)
- curses
- digest-sha3
- ethon
- ffi
- magic
- msgpack
- ncursesw
- rbnacl
- rpam2
- ruby-terminfo
- sassc
- scrypt
- semian
- snappy
- sqlite3
- typhoeus

### Failure Categories

| Category | Count | Gems | Fix |
|----------|-------|------|-----|
| VALUE/ID mismatch | ~12 | curb, do_sqlite3, fiddle, iconv, libxml-ruby, nokogiri, openssl, pcaprub | Ruby porting patches |
| Missing pizlonated symbols | 2 | charlock_holmes (ICU), cld3 (math) | Port dependencies |
| rb_funcall overload | 1 | eventmachine | C++ template fix |
| Not in flake | 2 | google-protobuf, grpc | Expose in rubyWithGem |
| Broken upstream dep | 1 | gpgme (gnutls) | Fix gnutls |
| Build system issues | 2 | mysql2, pg | Non-Fil-C issues |
| Skipped | 2 | opus-ruby, taglib-ruby | Known incompatible |

### Common Error Patterns

**VALUE/ID type mismatch:**
```c
// Error: incompatible pointer to integer conversion
idCall = rb_intern("call");  // ID = unsigned long, but assigned VALUE

// Fix: Cast properly
idCall = (ID)(uintptr_t)rb_intern("call");
```

**VALUE comparison with int:**
```c
// Error: comparison between pointer and integer
if (x == Qfalse)

// Fix: Use RTEST or explicit check
if (!RTEST(x))
```

**Passing VALUE where int expected:**
```c
// Error: passing VALUE to int parameter
rb_cstr_to_dbl(value, Qfalse);

// Fix: Use 0/1 directly
rb_cstr_to_dbl(value, 0);
```

See `docs/ruby-filc-porting-patterns.txt` for complete porting guide.
