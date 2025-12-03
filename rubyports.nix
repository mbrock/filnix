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

    # Database drivers - just need native flag, nixpkgs provides buildInputs
    (for "sqlite3" [ native ])
    (for "pg" [ native ])
  ];
}
