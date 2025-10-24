# Fil-C Wrapper Architecture Diagram

## Data Flow During Build

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        Package Build (e.g., bash)                       │
│                     nix build .#bash                                     │
└────────────────────────────┬────────────────────────────────────────────┘
                             │
                             │ Inherits filenv (= fil-c stdenv)
                             │
┌────────────────────────────▼────────────────────────────────────────────┐
│                    CC-Wrapper (filc-wrapped)                             │
│  /nix/store/.../clang-wrapper/bin/clang                                 │
│                                                                           │
│  On invocation:                                                           │
│  1. Read $PWD/nix-support/add-flags.sh                                  │
│  2. Read /nix/support/cc-cflags, libc-cflags, etc. from wrapper         │
│  3. Build: clang -B/path/lib -isystem /path/include -xc -              │
│  4. Pass to linker (ld-wrapper.sh)                                      │
│                                                                           │
│  Key nix-support files:                                                  │
│  ✓ cc-cflags: "-B${filc-libc}/lib -L${filc-libc}/lib"                  │
│  ✓ cc-ldflags: "-rpath ${filc-libc}/lib"                               │
│  ✓ libc-cflags: "-isystem ${filc-libc}/include"                        │
│  ✓ libc-crt1-cflags: "-B${filc-libc}/lib"                              │
│  ✓ libc-ldflags: "-L${filc-libc}/lib"                                  │
└────────────────────────────┬────────────────────────────────────────────┘
                             │
                             │ When linker is invoked
                             │ (e.g., clang calls cc1 → as → ld)
                             │
┌────────────────────────────▼────────────────────────────────────────────┐
│               Bintools-Wrapper (filc-bintools)                           │
│  /nix/store/.../ld-wrapper/bin/ld                                       │
│                                                                           │
│  On invocation:                                                           │
│  1. Read /nix/support/add-flags.sh (from bintools-wrapper)              │
│  2. Read dynamic-linker file: "/nix/store/.../lib/ld-yolo-x86_64.so"   │
│  3. Read libc-ldflags: "-L${filc-libc}/lib"                             │
│  4. Build: ld -L/path/lib -dynamic-linker /nix/.../ld-yolo-x86_64.so   │
│  5. Embed INTERP in ELF: "/nix/store/.../lib/ld-yolo-x86_64.so"       │
│                                                                           │
│  Key nix-support files:                                                  │
│  ✓ dynamic-linker: "${filc-libc}/lib/ld-yolo-x86_64.so"                │
│  ✓ ld-set-dynamic-linker: (empty flag file)                             │
│  ✓ libc-ldflags: "-L${filc-libc}/lib"                                  │
└────────────────────────────┬────────────────────────────────────────────┘
                             │
                             │ Linker produces ELF binary with:
                             │ INTERP = /nix/store/.../lib/ld-yolo-x86_64.so
                             │
┌────────────────────────────▼────────────────────────────────────────────┐
│                       Libc (filc-libc)                                   │
│  /nix/store/.../filc-libc/                                              │
│                                                                           │
│  Contains:                                                                │
│  ├── lib/                                                                │
│  │   ├── libc.so.6 (or libc.a for static)                              │
│  │   ├── ld-yolo-x86_64.so (custom dynamic linker)                     │
│  │   ├── crt1.o (startup code)                                          │
│  │   ├── crti.o (constructor begin)                                     │
│  │   ├── crtn.o (constructor end)                                       │
│  │   ├── yolo-glibc artifacts                                           │
│  │   └── user-glibc artifacts                                           │
│  ├── include/                                                            │
│  │   ├── stdio.h                                                         │
│  │   ├── stdlib.h                                                        │
│  │   └── ... (C library headers)                                        │
│  └── nix-support/                                                        │
│      ├── dynamic-linker                                                  │
│      ├── crt1.o                                                          │
│      ├── crti.o                                                          │
│      └── crtn.o                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

## Environment Variable Flow

```
┌─────────────────────────────────────────────────────────────────┐
│ Build Environment (before any build)                            │
│ filenv = overrideCC base.stdenv filc-wrapped                   │
│ → Sets: NIX_CC = filc-wrapped                                  │
└──────────────────────────┬──────────────────────────────────────┘
                           │
┌──────────────────────────▼──────────────────────────────────────┐
│ Setup-hook.sh runs                                              │
│ (From cc-wrapper/setup-hook.sh)                                │
│                                                                  │
│ Exports:                                                        │
│ - NIX_CC = filc-wrapped                                        │
│ - CC = clang                                                    │
│ - CXX = clang++                                                │
│ - addEnvHooks for ccWrapper_addCVars                          │
└──────────────────────────┬──────────────────────────────────────┘
                           │
┌──────────────────────────▼──────────────────────────────────────┐
│ For each dependency package:                                    │
│ ccWrapper_addCVars is called                                   │
│                                                                  │
│ If dependency has include/:                                    │
│ → Adds to NIX_CFLAGS_COMPILE_${suffixSalt}                    │
│ If dependency has lib/:                                        │
│ → Linker's add-flags.sh will add to NIX_LDFLAGS_${suffixSalt} │
└──────────────────────────┬──────────────────────────────────────┘
                           │
┌──────────────────────────▼──────────────────────────────────────┐
│ Build Phase (e.g., make)                                        │
│                                                                  │
│ $(CC) → cc-wrapper.sh (filc-wrapped/bin/clang)               │
│                                                                  │
│ add-flags.sh Reads:                                            │
│ 1. nix-support/libc-crt1-cflags → NIX_CFLAGS_COMPILE          │
│ 2. nix-support/libc-cflags → NIX_CFLAGS_COMPILE               │
│ 3. nix-support/cc-cflags → NIX_CFLAGS_COMPILE                 │
│ 4. nix-support/cc-ldflags → NIX_LDFLAGS                       │
│                                                                  │
│ Exports:                                                        │
│ NIX_CFLAGS_COMPILE_x86_64_unknown_linux_gnu="-B... -isystem..."│
│ NIX_LDFLAGS_x86_64_unknown_linux_gnu="-L... -rpath..."        │
└──────────────────────────┬──────────────────────────────────────┘
                           │
┌──────────────────────────▼──────────────────────────────────────┐
│ Compilation & Linking                                           │
│                                                                  │
│ clang $NIX_CFLAGS_COMPILE_... -c test.c                        │
│ ld $NIX_LDFLAGS_... test.o                                     │
│                                                                  │
│ Final binary has INTERP = /nix/store/.../lib/ld-yolo-x86_64.so│
└─────────────────────────────────────────────────────────────────┘
```

## nix-support File Hierarchy

```
filc-wrapped (cc-wrapper)
├── nix-support/
│   ├── orig-cc                    (→ ${filc-cc})
│   ├── orig-libc                  (→ ${filc-libc}/lib)
│   ├── orig-libc-dev              (→ ${filc-libc}/include)
│   ├── cc-cflags                  (-B/path/lib -L/path/lib)
│   ├── cc-cflags-before           (empty for fil-c)
│   ├── cc-ldflags                 (-rpath /path/lib)
│   ├── libc-cflags                (-isystem /path/include)
│   ├── libc-crt1-cflags           (-B/path/lib)
│   ├── libc-ldflags               (-L/path/lib)
│   ├── libcxx-cxxflags            (empty for fil-c)
│   ├── libcxx-ldflags             (empty for fil-c)
│   ├── add-flags.sh               (source to build vars)
│   ├── add-hardening.sh           (source for hardening)
│   ├── utils.bash                 (utility functions)
│   └── dynamic-linker → ../../../bintools-wrapper-*/nix-support/dynamic-linker
│
└── (symlinks to bintools-wrapper binaries)

filc-bintools (bintools-wrapper)
├── nix-support/
│   ├── orig-bintools              (→ ${base.binutils})
│   ├── orig-libc                  (→ ${filc-libc}/lib)
│   ├── orig-libc-dev              (→ ${filc-libc}/include)
│   ├── dynamic-linker             (/nix/store/.../lib/ld-yolo-x86_64.so)
│   ├── ld-set-dynamic-linker      (empty flag file)
│   ├── libc-ldflags               (-L/path/lib)
│   ├── add-flags.sh               (source to build linker vars)
│   ├── add-hardening.sh           (source for hardening)
│   ├── utils.bash                 (utility functions)
│   └── ...
│
└── bin/
    ├── ld (wrapper)
    ├── ar, nm, objdump, etc. (symlinks)
    └── ...

filc-libc
├── lib/
│   ├── libc.so.6
│   ├── libc.a (static)
│   ├── ld-yolo-x86_64.so (CUSTOM - This is the key!)
│   ├── crt1.o
│   ├── crti.o
│   ├── crtn.o
│   ├── libm.so.6
│   ├── libdl.so.2
│   └── (yolo-glibc and user-glibc artifacts)
├── include/
│   ├── stdio.h
│   ├── stdlib.h
│   ├── sys/
│   ├── (yolo-glibc headers)
│   └── (user-glibc headers)
└── nix-support/
    ├── dynamic-linker             (/nix/store/.../lib/ld-yolo-x86_64.so)
    ├── crt1.o                     (/nix/store/.../lib/crt1.o)
    ├── crti.o                     (/nix/store/.../lib/crti.o)
    └── crtn.o                     (/nix/store/.../lib/crtn.o)
```

## File Reading Order (Critical!)

### During Compilation (cc-wrapper.sh):
1. `add-flags.sh` reads `nix-support/libc-crt1-cflags` first
   → adds to `NIX_CFLAGS_COMPILE`
2. Reads `nix-support/libc-cflags`
   → adds to `NIX_CFLAGS_COMPILE`
3. Reads `nix-support/cc-cflags`
   → prepends to `NIX_CFLAGS_COMPILE`

**Result**: CRT paths, libc headers, then compiler flags.

### During Linking (ld-wrapper.sh via cc-wrapper calling clang):
1. `add-flags.sh` reads `nix-support/libc-ldflags`
   → sets `NIX_LDFLAGS`
2. Checks if `nix-support/ld-set-dynamic-linker` exists
   → reads `nix-support/dynamic-linker`
   → adds `-dynamic-linker /path/to/ld.so`

**Result**: Linker searches libc.so, then links with custom dynamic linker.

## Key Insight: The suffixSalt

The variable suffix prevents conflicts when multiple cc-wrappers coexist:

```bash
# Target platform: x86_64-unknown-linux-gnu
suffixSalt=x86_64_unknown_linux_gnu

# File contents get converted to:
NIX_CFLAGS_COMPILE_x86_64_unknown_linux_gnu=" ... "
NIX_LDFLAGS_x86_64_unknown_linux_gnu=" ... "

# This allows:
NIX_CFLAGS_COMPILE_aarch64_unknown_linux_gnu=" ... " (different compiler!)
```

So even if you have both x86_64 and aarch64 cc-wrappers, they won't clobber each other.

## Custom Dynamic Linker Resolution

```
Binary built with:
  ld ... -dynamic-linker /nix/store/.../lib/ld-yolo-x86_64.so output.o

ELF INTERP section created:
  readelf -l binary | grep INTERP
  [Requesting program interpreter: /nix/store/.../lib/ld-yolo-x86_64.so]

At runtime, kernel:
  1. Parses ELF INTERP
  2. Loads /nix/store/.../lib/ld-yolo-x86_64.so
  3. Passes control to custom dynamic linker
  4. Custom linker resolves symbols using its own libc

Result: Binary uses fil-c's memory-safe libc instead of system glibc!
```

## Why This Matters for Fil-C

Fil-C's yolo-glibc and user-glibc have security instrumentation. By using a custom dynamic linker, you ensure:

1. **Complete Coverage**: Even dependencies use fil-c's libc
2. **No Mixing**: Can't accidentally link against system libc
3. **Slice Detection**: Fil-c's slice detection works on the entire program
4. **Runtime Support**: Fil-c's runtime libraries are available

The wrapper system ensures this automatically for all packages built with `filenv`.
