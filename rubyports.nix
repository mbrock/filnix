# Ruby Gems with Native C Extensions
#
# This file defines:
#   - nativeGems: list of gem names with C extensions (for ruby-maxxed)
#   - ports: Fil-C porting fixes for specific gems
#
# See docs/ruby-filc-porting-patterns.txt for common porting patterns.

{
  pkgs,
  final ? pkgs,  # final has Fil-C packages, pkgs is base nixpkgs
}:
let
  inherit (import ./ports { inherit (pkgs) lib pkgs; })
    for
    use
    addCFlag
    ;

  # Force building native extension (needed for cross-compilation)
  native = use { dontBuild = false; };

  replace = file: old: new:
    use (attrs: {
      postPatch = (attrs.postPatch or "") + ''
        substituteInPlace ${file} \
          --replace-fail ${pkgs.lib.escapeShellArg old} \
                         ${pkgs.lib.escapeShellArg new}
      '';
    });

  # AST-based pattern replacement using ast-grep
  # Use --selector call_expression for C function calls
  astGrep = pattern: rewrite:
    use (attrs: {
      nativeBuildInputs = (attrs.nativeBuildInputs or []) ++ [ pkgs.ast-grep ];
      postPatch = (attrs.postPatch or "") + ''
        ast-grep run -p ${pkgs.lib.escapeShellArg pattern} \
                 -r ${pkgs.lib.escapeShellArg rewrite} \
                 -l c --selector call_expression -U .
      '';
    });

  # AST-grep without selector (for switch/case patterns)
  astGrepAny = pattern: rewrite:
    use (attrs: {
      nativeBuildInputs = (attrs.nativeBuildInputs or []) ++ [ pkgs.ast-grep ];
      postPatch = (attrs.postPatch or "") + ''
        ast-grep run -p ${pkgs.lib.escapeShellArg pattern} \
                 -r ${pkgs.lib.escapeShellArg rewrite} \
                 -l c -U .
      '';
    });

  # AST-grep with custom selector (e.g., switch_statement)
  astGrepSel = selector: pattern: rewrite:
    use (attrs: {
      nativeBuildInputs = (attrs.nativeBuildInputs or []) ++ [ pkgs.ast-grep ];
      postPatch = (attrs.postPatch or "") + ''
        ast-grep run -p ${pkgs.lib.escapeShellArg pattern} \
                 -r ${pkgs.lib.escapeShellArg rewrite} \
                 -l c --selector ${selector} -U .
      '';
    });

in
{
  # Native gems organized by category (excluding GTK3 ecosystem)
  nativeGems = {
    # Database drivers
    database = [
      "do_sqlite3"      # DataObjects SQLite3 adapter
      "mysql2"          # MySQL client
      "pg"              # PostgreSQL client
      "sequel_pg"       # Sequel PostgreSQL optimizations
      "sqlite3"         # SQLite3 bindings
      "tiny_tds"        # TDS protocol (SQL Server/Sybase)
    ];

    # Parsing and serialization
    parsing = [
      "hpricot"         # HTML parser (legacy)
      "libxml-ruby"     # libxml2 bindings
      "msgpack"         # MessagePack serializer
      "nokogiri"        # HTML/XML parser (libxml2/libgumbo)
      "psych"           # YAML parser (libyaml)
      "re2"             # RE2 regex engine bindings
    ];

    # Crypto and security
    crypto = [
      "digest-sha3"     # SHA-3 hashing
      "gpgme"           # GnuPG Made Easy bindings
      "openssl"         # OpenSSL bindings
      "rbnacl"          # NaCl/libsodium bindings
      "scrypt"          # scrypt key derivation
    ];

    # Networking and HTTP
    networking = [
      "curb"            # libcurl bindings
      "ethon"           # libcurl FFI wrapper
      "eventmachine"    # event-driven I/O
      "patron"          # libcurl HTTP client
      "puma"            # threaded HTTP server
      "typhoeus"        # parallel HTTP client
    ];

    # Image processing (non-GTK)
    image = [
      "rmagick"         # ImageMagick bindings
      "ruby-vips"       # libvips image processing
      "rszr"            # image resizing
    ];

    # System and FFI
    system = [
      "ffi"             # Foreign Function Interface
      "fiddle"          # libffi wrapper (stdlib)
      "iconv"           # character encoding
      "curses"          # terminal UI
      "ncursesw"        # wide char terminal UI
      "ruby-terminfo"   # terminfo database
      "magic"           # libmagic file type detection
      "zlib"            # compression
    ];

    # Audio and media
    audio = [
      "opus-ruby"       # Opus audio codec
      "taglib-ruby"     # audio metadata
    ];

    # Virtualization and containers
    virtualization = [
      "ovirt-engine-sdk" # oVirt management
      "ruby-libvirt"    # libvirt bindings
      "ruby-lxc"        # LXC container bindings
    ];

    # Miscellaneous native extensions
    misc = [
      "charlock_holmes" # encoding detection (ICU)
      "cld3"            # language detection
      "google-protobuf" # Protocol Buffers
      "grpc"            # gRPC bindings
      "pcaprub"         # packet capture
      "rpam2"           # PAM authentication
      "rugged"          # libgit2 bindings
      "sassc"           # libsass bindings
      "semian"          # circuit breaker
      "snappy"          # Snappy compression
      "uuid4r"          # UUID generation
      "xapian-ruby"     # Xapian search
      "zookeeper"       # ZooKeeper client
    ];
  };

  # Fil-C porting fixes
  ports = [
    (for "ruby-terminfo" [
      native
      (replace "terminfo.c" "RTEST(ret)" "RTEST((VALUE)ret)")
    ])

    (for "msgpack" [
      native
      (replace "ext/msgpack/buffer_class.c"
        "unsigned long max = ((VALUE*) args)[2];"
        "unsigned long max = (unsigned long)(uintptr_t)((VALUE*) args)[2];")
      (replace "ext/msgpack/buffer_class.c"
        "(VALUE) max,"
        "(VALUE)(uintptr_t) max,")
    ])

    # ffi - Uses Fil-C's libffi (bundled libffi has incompatible asm)
    # - USE_FFI_ALLOC disables custom x86_64 trampolines (incompatible with Fil-C)
    # - VALUE-as-pointer issues fixed
    # - libffi comes from final.defaultGemConfig (Fil-C version)
    (for "ffi" [
      native
      (addCFlag "-DUSE_FFI_ALLOC")
      # Patch extconf.rb to use system libffi
      # Skip cross-compile link test but explicitly add -lffi to linker flags
      (replace "ext/ffi_c/extconf.rb"
        "libffi_ok &&= have_library(\"ffi\""
        "$libs << \" -lffi\"; libffi_ok &&= true || have_library(\"ffi\"")
      # Fix VALUE-as-pointer bitwise op in Struct.h
      (replace "ext/ffi_c/Struct.h"
        "#define FIELD_CACHE_LOOKUP(this, sym) ( &(this)->cache_row[((sym) >> 8) & 0xff] )"
        "#define FIELD_CACHE_LOOKUP(this, sym) ( &(this)->cache_row[(((uintptr_t)(sym)) >> 8) & 0xff] )")
    ])

    # openssl - various VALUE/int mismatches (fixed via ast-grep patterns)
    (for "openssl" [
      native
      # rb_attr takes int, not VALUE - fix Qfalse -> 0
      (astGrep "rb_attr($A, $B, $C, $D, Qfalse)" "rb_attr($A, $B, $C, $D, 0)")
      # rb_cstr_to_inum takes int badcheck, not VALUE
      (astGrep "rb_cstr_to_inum($A, $B, Qtrue)" "rb_cstr_to_inum($A, $B, 1)")
      # rb_str_new size cast needs uintptr_t
      (astGrep "rb_str_new(NULL, (long)$A)" "rb_str_new(NULL, (long)(uintptr_t)$A)")
      # rb_protect expects VALUE, but len is long
      (replace "ext/openssl/ossl.c"
        "str = rb_protect(ossl_str_new_i, len, &state);"
        "str = rb_protect(ossl_str_new_i, (VALUE)(uintptr_t)len, &state);")
      # int ret = Qnil -> int ret = -1 (function returns int, not VALUE)
      (replace "ext/openssl/ossl_pkcs7.c"
        "int i, ret = Qnil;"
        "int i, ret = -1;")
      # VALUE ret stores ID values, should be ID ret
      (replace "ext/openssl/ossl_pkey_ec.c"
        "point_conversion_form_t form;\n    VALUE ret;"
        "point_conversion_form_t form;\n    ID ret;")
    ])

    # racc - ERROR_TOKEN (int) passed where VALUE expected, use vERROR_TOKEN
    (for "racc" [
      native
      (replace "ext/racc/cparse/cparse.c"
        "SHIFT(v, act, ERROR_TOKEN, val)"
        "SHIFT(v, act, vERROR_TOKEN, val)")
    ])

    # eventmachine - Intern_* vars are ID, not VALUE; also int reuse in set_rlimit
    (for "eventmachine" [
      native
      (replace "ext/rubymain.cpp" "static VALUE Intern_" "static ID Intern_")
      (replace "ext/rubymain.cpp"
        "arg = (NIL_P(arg)) ? -1 : NUM2INT (arg);"
        "int limit = (NIL_P(arg)) ? -1 : NUM2INT(arg);")
      (replace "ext/rubymain.cpp"
        "return INT2NUM (evma_set_rlimit_nofile (arg));"
        "return INT2NUM(evma_set_rlimit_nofile(limit));")
    ])

    # date - VALUE to st_index_t conversion for hash function
    (for "date" [
      native
      (astGrepSel "assignment_expression" "h[0] = m_nth($X)" "h[0] = (st_index_t)(uintptr_t)m_nth($X)")
      (astGrepSel "assignment_expression" "h[3] = m_sf($X)" "h[3] = (st_index_t)(uintptr_t)m_sf($X)")
    ])

    # nokogiri - can't switch on VALUE (pointer), convert to if-else
    (for "nokogiri" [
      native
      (astGrepSel "switch_statement"
        "switch (rb_range_beg_len($ARG, $BEG, $LEN, $SIZE, $FLAG)) { case Qfalse: break; case Qnil: return Qnil; default: return subseq($SELF, $B, $L); }"
        "{ VALUE range_result = rb_range_beg_len($ARG, $BEG, $LEN, $SIZE, $FLAG); if (range_result == Qfalse) { } else if (range_result == Qnil) { return Qnil; } else { return subseq($SELF, $B, $L); } }")
    ])

    # nio4r - patch bundled libev inline asm, fix VALUE/int issues
    # Note: bundled libev has GVL-release patches needed for Ruby threading
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

    # curb - idCall/idJoin are ID not VALUE; int return from VALUE function
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

    # bigdecimal - switch on VALUE, rb_protect int<->VALUE casting
    (for "bigdecimal" [
      native
      # Convert switch(val) case Qnil/Qtrue/Qfalse to if-else
      (replace "ext/bigdecimal/bigdecimal.c"
        "switch (val) {
      case Qnil:
      case Qtrue:
      case Qfalse:"
        "if (val == Qnil || val == Qtrue || val == Qfalse) {")
      (replace "ext/bigdecimal/bigdecimal.c"
        "return Qnil;

      default:
        break;
    }"
        "return Qnil;
    }")
      # is_zero()/is_one() return int, not VALUE - return 0 instead of Qfalse
      (astGrepSel "case_statement" "case T_BIGNUM: return Qfalse;" "case T_BIGNUM: return 0;")
      # Fix rb_protect callback: store result in struct instead of casting int<->VALUE
      (replace "ext/bigdecimal/bigdecimal.c"
        "const char *exp_chr;
  size_t ne;
};"
        "const char *exp_chr;
  size_t ne;
  int result;
};")
      (replace "ext/bigdecimal/bigdecimal.c"
        "return (VALUE)VpCtoV(x->a, x->int_chr, x->ni, x->frac, x->nf, x->exp_chr, x->ne);"
        "x->result = VpCtoV(x->a, x->int_chr, x->ni, x->frac, x->nf, x->exp_chr, x->ne);
  return Qnil;")
      (replace "ext/bigdecimal/bigdecimal.c"
        "VALUE result = rb_protect(call_VpCtoV, (VALUE)&args, &state);"
        "rb_protect(call_VpCtoV, (VALUE)&args, &state);")
      (replace "ext/bigdecimal/bigdecimal.c"
        "return (int)result;"
        "return args.result;")
    ])

    # io-console - switch on VALUE needs uintptr_t cast
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

    # Database drivers - just need native flag, nixpkgs provides buildInputs
    (for "sqlite3" [ native ])
    (for "pg" [ native ])
  ];
}
