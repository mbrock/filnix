# Fil-C CC-Wrapper Implementation Plan

## Executive Summary

This document provides a comprehensive plan for wrapping fil-c's clang compiler with proper nixpkgs integration, supporting fil-c's custom libc (yolo-glibc + user-glibc) and runtime integration.

## Part 1: Nixpkgs Wrapper Infrastructure Overview

### 1.1 Architecture: Three-Layer Wrapping System

The nixpkgs wrapper system consists of three distinct but coordinated layers:

```
┌─────────────────────────────────────────────┐
│  Package Derivation (e.g., curl, bash)      │
│  Uses: NIX_CC, NIX_CFLAGS_COMPILE, etc.    │
└────────────────┬──────────────────────────┘
                 │
┌────────────────▼──────────────────────────────────┐
│  CC-Wrapper (cc-wrapper.sh + setup-hook.sh)      │
│  - Reads: nix-support/cc-cflags, cc-ldflags      │
│  - Reads: nix-support/libc-cflags, libc-ldflags  │
│  - Exports: NIX_CC, NIX_CFLAGS_COMPILE, etc.     │
│  - Manages: C/C++ specific flags & paths          │
└────────────────┬──────────────────────────────────┘
                 │
┌────────────────▼──────────────────────────────────┐
│  Bintools-Wrapper (ld-wrapper.sh + setup-hook.sh)│
│  - Reads: nix-support/dynamic-linker             │
│  - Reads: nix-support/libc-ldflags               │
│  - Exports: NIX_BINTOOLS, LD, etc.               │
│  - Manages: Linking & dynamic linker             │
└────────────────┬──────────────────────────────────┘
                 │
┌────────────────▼──────────────────────────────────┐
│  Libc (glibc, musl, yolo-glibc, etc.)            │
│  Provides: Headers, runtime libraries, dynamic   │
│            linker, CRT files, etc.               │
└─────────────────────────────────────────────────────┘
```

### 1.2 Core Concepts

#### wrapBintoolsWith
- **Purpose**: Wraps binutils (or lld) to integrate with a libc
- **Input**: `bintools` (unwrapped linker/tools), `libc` (C library package)
- **Output**: Wrapper that properly routes all libc paths
- **Key Files Generated**:
  - `nix-support/dynamic-linker`: Path to dynamic linker (e.g., `/nix/store/.../lib/ld-yolo-x86_64.so`)
  - `nix-support/libc-ldflags`: Linker search paths
  - `nix-support/ld-set-dynamic-linker`: Flag indicating dynamic linker is set
  - `nix-support/orig-libc`, `nix-support/orig-libc-dev`: Original libc references

#### wrapCCWith
- **Purpose**: Wraps a compiler (gcc/clang) to integrate with libc and bintools
- **Input**: `cc` (unwrapped compiler), `libc`, `bintools` (already wrapped)
- **Output**: Fully functional compiler with proper include paths and linking
- **Key Files Generated**:
  - `nix-support/cc-cflags`: Compiler include paths, libc paths, and flags
  - `nix-support/cc-ldflags`: Linker flags from compiler's perspective
  - `nix-support/libc-cflags`: Include paths for C headers
  - `nix-support/libc-crt1-cflags`: Paths to CRT files (crt1.o, crti.o, etc.)

### 1.3 The nix-support File Mechanism

The `nix-support/` directory inside wrapped compilers contains configuration files read by wrapper scripts:

#### Files in cc-wrapper's nix-support/

| File | Purpose | Content Example |
|------|---------|-----------------|
| `cc-cflags` | Compiler flags | `-B/path/lib -I/path/include` |
| `cc-cflags-before` | Flags applied before user flags | `-march=x86-64 -mno-omit-frame-pointer` |
| `cc-ldflags` | Linker flags from cc perspective | `-L/path/lib -rpath /path/lib` |
| `libc-cflags` | C library include paths | `-isystem /path/include` |
| `libc-crt1-cflags` | CRT object file paths | `-B/path/lib` |
| `libc-ldflags` | C library linker flags | `-L/path/lib` |
| `libcxx-cxxflags` | C++ library include paths | `-isystem /path/include/c++/v1` |
| `libcxx-ldflags` | C++ library linker flags | `-stdlib=libc++` |
| `orig-cc` | Path to unwrapped compiler | `/nix/store/.../clang` |
| `orig-libc` | Path to libc library output | `/nix/store/.../glibc/lib` |
| `orig-libc-dev` | Path to libc dev output | `/nix/store/.../glibc.dev/include` |

#### Files in bintools-wrapper's nix-support/

| File | Purpose | Content Example |
|------|---------|-----------------|
| `dynamic-linker` | Path to dynamic linker | `/nix/store/.../lib/ld-linux-x86-64.so.2` |
| `ld-set-dynamic-linker` | Flag to auto-set dynamic linker | (empty file presence indicates flag) |
| `dynamic-linker-m32` | 32-bit dynamic linker | `/nix/store/.../lib/ld-linux.so.2` |
| `libc-ldflags` | C library linker flags | `-L/path/lib` |
| `libc-ldflags-before` | Linker flags applied first | (rarely used) |
| `orig-bintools` | Path to unwrapped bintools | `/nix/store/.../binutils/bin` |
| `orig-libc` | Path to libc library output | `/nix/store/.../glibc/lib` |
| `orig-libc-dev` | Path to libc dev output | `/nix/store/.../glibc.dev/include` |

### 1.4 Flag Processing Pipeline

#### During cc-wrapper.sh execution:
1. `cc-wrapper.sh` reads user flags from command line
2. Calls `add-flags.sh` which:
   - Reads `nix-support/libc-crt1-cflags` → `NIX_CFLAGS_COMPILE`
   - Reads `nix-support/libc-cflags` → `NIX_CFLAGS_COMPILE`
   - Reads `nix-support/cc-cflags` → `NIX_CFLAGS_COMPILE`
   - Reads `nix-support/cc-cflags-before` → `NIX_CFLAGS_COMPILE_BEFORE`
   - Reads `nix-support/libcxx-cxxflags` → `NIX_CXXSTDLIB_COMPILE` (C++ only)
3. Constructs final command: `clang -B/path/lib -I/path/include <user-flags>`

#### During ld-wrapper.sh execution:
1. `ld-wrapper.sh` reads linker invocation
2. Calls `add-flags.sh` which:
   - Reads `nix-support/libc-ldflags` → `NIX_LDFLAGS`
   - Reads `nix-support/dynamic-linker` → `NIX_DYNAMIC_LINKER`
   - If `ld-set-dynamic-linker` exists, auto-sets `-dynamic-linker /path/to/ld.so`
3. Constructs final command: `ld -L/path/lib -dynamic-linker /path/to/ld.so <user-flags>`

### 1.5 Environment Variable Hygiene (suffixSalt)

To support multiple cc-wrappers (e.g., for cross-compilation), environment variables use a suffix based on the target platform:

```bash
# Instead of:
export NIX_CFLAGS_COMPILE="-march=x86-64"

# Actually uses:
export NIX_CFLAGS_COMPILE_x86_64_unknown_linux_gnu="-march=x86-64"
```

This allows many cc-wrappers to be in scope simultaneously without clobbering each other.

## Part 2: How Libc Integration Works

### 2.1 Libc Package Structure

A libc package in nixpkgs has this structure:

```
${libc}
├── lib/
│   ├── libc.so.6          # Main C library
│   ├── ld-linux-x86-64.so.2  # Dynamic linker
│   ├── crt1.o             # Startup code
│   ├── crti.o             # Constructor hooks
│   ├── crtn.o             # Constructor/destructor trampolines
│   └── lib*.so*           # Other libraries (libm, libdl, etc.)
├── include/
│   ├── stdio.h
│   ├── stdlib.h
│   ├── ...
│   └── sys/
└── nix-support/
    ├── dynamic-linker     # Explicit linker path (optional)
    └── crt*.o files (optional, for integration)
```

### 2.2 Libc Integration During wrapBintoolsWith

```nix
filc-bintools = base.wrapBintoolsWith {
  bintools = base.binutils;  # Or lld
  libc = filc-libc;          # Your custom libc
};
```

What happens:
1. `wrapBintoolsWith` extracts:
   - `libc_lib = getLib filc-libc` → `/nix/store/.../lib`
   - `libc_dev = getDev filc-libc` → `/nix/store/.../` (same, usually)
   - `libc_bin = getBin filc-libc` → `/nix/store/.../bin`

2. Generates `nix-support/dynamic-linker`:
   ```bash
   echo "${filc-libc}/lib/ld-yolo-x86_64.so" > $out/nix-support/dynamic-linker
   ```

3. Generates `nix-support/libc-ldflags`:
   ```bash
   echo "-L${libc_lib}${libc.libdir or "/lib"}" >> $out/nix-support/libc-ldflags
   ```

### 2.3 Libc Integration During wrapCCWith

```nix
filc-wrapped = base.wrapCCWith {
  cc = filc-cc;
  libc = filc-libc;
  bintools = filc-bintools;
};
```

What happens:
1. Extracts libc paths same as above
2. Generates `nix-support/libc-crt1-cflags`:
   ```bash
   echo "-B${libc_lib}${libc.libdir or "/lib/"}" >> $out/nix-support/libc-crt1-cflags
   ```
   This ensures CRT files are found.

3. Generates `nix-support/libc-cflags`:
   ```bash
   include "-idirafter" "${libc_dev}${libc.incdir or "/include"}" >> $out/nix-support/libc-cflags
   ```
   This adds libc headers to include search path.

4. Creates `nix-support/orig-libc` and `nix-support/orig-libc-dev` for reference.

## Part 3: Handling Custom Dynamic Linkers

### 3.1 Fil-C's Custom Linker: ld-yolo-x86_64.so

Fil-C uses a custom dynamic linker: `ld-yolo-x86_64.so` (instead of standard `ld-linux-x86-64.so.2`).

This requires:

1. **In filc-libc**:
   ```nix
   filc-libc = base.runCommand "filc-libc" {} ''
     mkdir -p $out/{include,lib} $out/nix-support
     # Copy yolo-glibc and user-glibc artifacts
     cp -r ${filc-unwrapped}/pizfix/lib/. $out/lib/
     
     # CRITICAL: Explicitly specify the custom dynamic linker
     echo "$out/lib/ld-yolo-x86_64.so" > $out/nix-support/dynamic-linker
     
     # OPTIONAL: Create symlink for compatibility (but NOT actually used)
     ln -s "$out/lib/ld-yolo-x86_64.so" "$out/lib/ld-linux-x86-64.so.2"
   '';
   ```

2. **How it flows**:
   - `wrapBintoolsWith` reads `dynamic-linker` from filc-libc's nix-support
   - Writes it to bintools-wrapper's `nix-support/dynamic-linker`
   - Creates `nix-support/ld-set-dynamic-linker` (empty file)
   - During linking, `ld-wrapper.sh` uses:
     ```bash
     NIX_DYNAMIC_LINKER=$(< @out@/nix-support/dynamic-linker)
     # Results in: -dynamic-linker /nix/store/.../lib/ld-yolo-x86_64.so
     ```

### 3.2 ELF Header Interpretation

When linker wraps a binary:
```bash
ld ... -dynamic-linker /nix/store/.../lib/ld-yolo-x86_64.so output.o
```

The resulting ELF binary's INTERP section contains: `/nix/store/.../lib/ld-yolo-x86_64.so`

The kernel then loads this custom dynamic linker instead of the system default.

## Part 4: Clang-Specific Considerations

### 4.1 Resource Directory

Clang has a resource directory containing:
- Built-in headers (e.g., `stdint.h`, `limits.h`)
- Compiler intrinsics
- Runtime libraries (libclang_rt)

Location: `${clang}/lib/clang/${version}/`

**For fil-c wrapping**: No special action needed. The clang binary knows its resource directory at compile time.

### 4.2 Clang's Standard Library Search

Clang looks for headers in:
1. `-I` paths (explicit)
2. `-isystem` paths (C library headers)
3. Resource directory
4. System defaults (typically `/usr/include`)

In nixpkgs, `-nostdlibinc` is added to prevent system headers from leaking through.

### 4.3 Clang-Specific Wrapper Setup

From `cc-wrapper/default.nix`, clang gets special treatment:

```nix
useCcForLibs = isClang then true else ...
```

This ensures:
- `-B` flags point to libstdc++ directory (GCC's C++ library)
- `-L` flags include GCC's compiler-rt/libgcc paths

**For fil-c**: This is actually beneficial because fil-c can use these libraries if needed.

### 4.4 GCC Compatibility

```nix
filc-wrapped = base.wrapCCWith {
  cc = filc-cc;
  libc = filc-libc;
  bintools = filc-bintools;
  isClang = true;
  
  extraBuildCommands = ''
    ln -s clang $out/bin/gcc
    ln -s clang++ $out/bin/g++
  '';
};
```

This creates gcc/g++ symlinks to clang so configure scripts find them.

## Part 5: Concrete Implementation Plan for Fil-C

### 5.1 Current State (from flake.nix)

The current setup already does most of this correctly:

```nix
filc-libc = base.runCommand "filc-libc" {} ''
  mkdir -p $out/{include,lib} $out/nix-support
  cp -r ${filc-unwrapped}/pizfix/include/. $out/include/
  cp -r ${filc-unwrapped}/pizfix/lib/. $out/lib/
  
  # Correctly sets custom linker
  echo "$out/lib/ld-yolo-x86_64.so" > $out/nix-support/dynamic-linker
  
  # CRT files (optional but helpful)
  for crt in crt1.o rcrt1.o Scrt1.o crti.o crtn.o; do
    if [ -f "$out/lib/$crt" ]; then
      echo "$out/lib/$crt" > "$out/nix-support/$crt"
    fi
  done
'';

filc-bintools = base.wrapBintoolsWith {
  bintools = base.binutils;
  libc = filc-libc;
};

filc-wrapped = base.wrapCCWith {
  cc = filc-cc;
  libc = filc-libc;
  bintools = filc-bintools;
  isClang = true;
  
  extraBuildCommands = ''
    echo "-L${filc-libc}/lib" >> $out/nix-support/cc-cflags
    echo "-rpath ${filc-libc}/lib" >> $out/nix-support/cc-ldflags
    ln -s clang $out/bin/gcc
    ln -s clang++ $out/bin/g++
  '';
};

filenv = base.overrideCC base.stdenv filc-compat;
```

### 5.2 Recommended Enhancements

#### 1. Add Clang-Specific Resource Directory Handling

```nix
filc-wrapped = base.wrapCCWith {
  cc = filc-cc.overrideAttrs (old: {
    passthru = (old.passthru or {}) // {
      # Ensure resource directory is available
      libllvm = base.llvmPackages_20.libllvm;
    };
  });
  libc = filc-libc;
  bintools = filc-bintools;
  isClang = true;
  
  extraBuildCommands = ''
    # Clang-specific flags
    echo "-nostdlibinc" >> $out/nix-support/cc-cflags
    
    # Ensure fil-c libraries are found during linking
    echo "-L${filc-libc}/lib" >> $out/nix-support/cc-cflags
    echo "-rpath ${filc-libc}/lib" >> $out/nix-support/cc-ldflags
    
    # Add compatibility symlinks
    ln -s clang $out/bin/gcc
    ln -s clang++ $out/bin/g++
  '';
};
```

#### 2. Enhanced filc-libc with Better Structure

```nix
filc-libc = base.runCommand "filc-libc" {} ''
  set -euo pipefail
  mkdir -p $out/{include,lib,nix-support}
  
  # Copy yolo-glibc artifacts
  cp -r ${filc-unwrapped}/pizfix/include/. $out/include/ 2>/dev/null || true
  cp -r ${filc-unwrapped}/pizfix/lib/. $out/lib/ 2>/dev/null || true
  
  # Copy user-glibc artifacts if they exist
  cp -r ${filc-unwrapped}/pizfix/stdfil-include/. $out/include/ 2>/dev/null || true
  
  # Add OS headers for compilation
  mkdir -p $out/include/sys
  cp -r ${base.linuxHeaders}/include/. $out/include/ 2>/dev/null || true
  
  # Register custom dynamic linker (CRITICAL)
  echo "$out/lib/ld-yolo-x86_64.so" > $out/nix-support/dynamic-linker
  
  # Compatibility symlink (optional, but doesn't hurt)
  ln -s "$out/lib/ld-yolo-x86_64.so" "$out/lib/ld-linux-x86-64.so.2" || true
  
  # Register CRT files for proper startup code
  for crt in crt1.o rcrt1.o Scrt1.o crti.o crtn.o; do
    if [ -f "$out/lib/$crt" ]; then
      echo "$out/lib/$crt" > "$out/nix-support/$crt"
    fi
  done
  
  # Optional: Register library search directory
  echo "-L$out/lib" > $out/nix-support/libc-ldflags
'';
```

#### 3. Prevent Mixing Fil-C and Non-Fil-C Code

Create validation in stdenv.mkDerivation to prevent mixing:

```nix
filenv = base.overrideCC base.stdenv filc-compat;

# Optional: Wrap mkDerivation to enforce fil-c only
filenv-pure = filenv.override {
  allowImpure = false;
};

# For packages that should use fil-c
withFilC = pkg: pkg.override { stdenv = filenv; };

# Build time check (optional but recommended)
checkFilCIntegrity = pkg:
  if pkg ? stdenv && pkg.stdenv != filenv then
    builtins.warn "Package ${pkg.name or "unknown"} not using fil-c stdenv!"
  else
    pkg;
```

### 5.3 Critical Files Verification Checklist

When building with fil-c-wrapped, verify:

```bash
# In nix-support of wrapped compiler:
✓ cc-cflags contains "-L${filc-libc}/lib"
✓ cc-ldflags contains linker flags
✓ libc-cflags contains "-isystem ${filc-libc}/include"
✓ libc-crt1-cflags contains "-B${filc-libc}/lib"
✓ libc-ldflags contains "-L${filc-libc}/lib"

# In nix-support of bintools:
✓ dynamic-linker contains "${filc-libc}/lib/ld-yolo-x86_64.so"
✓ ld-set-dynamic-linker file exists (empty)
✓ libc-ldflags contains "-L${filc-libc}/lib"

# In compiled binaries:
$ readelf -l binary | grep INTERP
  [Requesting program interpreter: /nix/store/.../lib/ld-yolo-x86_64.so]
```

## Part 6: Detailed nix-support File Reference

### 6.1 cc-wrapper nix-support Files

#### cc-cflags
**When read**: By `add-flags.sh` in cc-wrapper.sh
**Content**: C compiler-specific flags
**Example for fil-c**:
```
-B/nix/store/.../lib -L/nix/store/.../lib -nostdlibinc
```
**Generated by**: `postFixup` of `wrapCCWith`

#### cc-ldflags
**When read**: By `add-flags.sh` in cc-wrapper.sh
**Content**: Linker-specific flags
**Example for fil-c**:
```
-L/nix/store/.../lib -rpath /nix/store/.../lib
```
**Role**: Passed to linker, ensures runtime library discovery

#### libc-crt1-cflags
**When read**: By `add-flags.sh` in cc-wrapper.sh (first)
**Content**: CRT search paths
**Example**:
```
-B/nix/store/.../lib
```
**Role**: Ensures startup code (crt1.o, etc.) is found

#### libc-cflags
**When read**: By `add-flags.sh` in cc-wrapper.sh (second)
**Content**: C library include paths
**Example**:
```
-isystem /nix/store/.../include
```
**Role**: Adds C library headers to search path

#### libc-ldflags
**When read**: By `add-flags.sh` in cc-wrapper.sh
**Content**: C library linker flags
**Example**:
```
-L/nix/store/.../lib
```
**Role**: Enables linking against C library

### 6.2 bintools-wrapper nix-support Files

#### dynamic-linker
**When read**: By `add-flags.sh` in ld-wrapper.sh
**Content**: Absolute path to dynamic linker
**Example for fil-c**:
```
/nix/store/...-filc-libc/lib/ld-yolo-x86_64.so
```
**Role**: Becomes `-dynamic-linker` flag in final ELF binary

#### ld-set-dynamic-linker
**When read**: Checked for existence by `add-flags.sh`
**Content**: Empty file (presence matters, not content)
**Role**: Signals that `dynamic-linker` should be auto-applied

#### libc-ldflags
**When read**: By `add-flags.sh` in ld-wrapper.sh
**Content**: C library search paths for linker
**Example**:
```
-L/nix/store/.../lib
```
**Role**: Ensures libc.so is found during linking

## Part 7: Complete Working Example

Here's a complete, production-ready setup:

```nix
{
  description = "Fil-C wrapped as a Nix stdenv";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    filc-src = {
      url = "git+file:///home/mbrock/fil-c";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, filc-src, ... }:
  let
    system = "x86_64-linux";
    base = import nixpkgs { inherit system; };

    # Build fil-c with both glibc variants
    filc-unwrapped = base.llvmPackages_20.libcxxStdenv.mkDerivation {
      pname = "filc";
      version = "git";
      src = filc-src;
      
      nativeBuildInputs = with base; [
        cmake ninja python3 git file patchelf gnumake pkg-config
      ];
      
      buildInputs = with base; [
        glibc.dev glibc.static linuxHeaders llvmPackages_20.libcxx
      ];
      
      hardeningDisable = [ "fortify" "stackprotector" "pie" ];
      dontUpdateAutotoolsGnuConfigScripts = true;
      
      ALTYOLO = "./build_yolo_glibc.sh";
      ALTUSER = "./build_user_glibc.sh";
      ALTLLVMLIBCOPT = " ";
      
      postPatch = ''
        rm -rf projects
      '';
      
      configurePhase = ''
        runHook preConfigure
        export HOME=$TMPDIR HOSTNAME=nix-build
        unset NIX_CFLAGS_COMPILE NIX_CXXSTDLIB_COMPILE
        patchShebangs configure_llvm.sh build_clang.sh build_base.sh \
                       build_os_include.sh build_yolo_glibc.sh \
                       build_user_glibc.sh build_runtime.sh build_cxx.sh libpas
        runHook postConfigure
      '';
      
      buildPhase = ''
        runHook preBuild
        ./build_base.sh
        runHook postBuild
      '';
      
      installPhase = ''
        runHook preInstall
        mkdir -p $out
        cp -r build pizfix $out/
        
        for d in "$out/build/bin" "$out/pizfix/bin"; do
          if [ -d "$d" ]; then
            for exe in "$d"/*; do
              if [ -x "$exe" ] && file "$exe" | grep -q ELF; then
                patchelf --set-rpath "$out/pizfix/lib" "$exe" || true
              fi
            done
          fi
        done
        
        chmod -R u+w $out/pizfix || true
        mkdir -p $out/pizfix/os-include
        cp -r ${base.linuxHeaders}/include/. $out/pizfix/os-include/
        runHook postInstall
      '';
      
      enableParallelBuilding = true;
      
      meta = with base.lib; {
        description = "Fil-C memory-safe C/C++ compiler (from source)";
        platforms = platforms.linux;
      };
    };

    # Create libc package with proper nix-support
    filc-libc = base.runCommand "filc-libc" {} ''
      set -euo pipefail
      mkdir -p $out/{include,lib,nix-support}
      
      # Copy yolo-glibc and user-glibc
      cp -r ${filc-unwrapped}/pizfix/include/. $out/include/ 2>/dev/null || true
      cp -r ${filc-unwrapped}/pizfix/lib/. $out/lib/ 2>/dev/null || true
      cp -r ${filc-unwrapped}/pizfix/stdfil-include/. $out/include/ 2>/dev/null || true
      
      # Add OS headers
      mkdir -p $out/include/sys
      cp -r ${base.linuxHeaders}/include/. $out/include/ 2>/dev/null || true
      
      # CRITICAL: Register custom dynamic linker
      if [ -f "$out/lib/ld-yolo-x86_64.so" ]; then
        echo "$out/lib/ld-yolo-x86_64.so" > $out/nix-support/dynamic-linker
      else
        echo "ERROR: ld-yolo-x86_64.so not found in $out/lib" >&2
        ls -la $out/lib/ >&2
        exit 1
      fi
      
      # Compatibility symlink
      ln -sf "$out/lib/ld-yolo-x86_64.so" "$out/lib/ld-linux-x86-64.so.2" || true
      
      # Register CRT files
      for crt in crt1.o rcrt1.o Scrt1.o crti.o crtn.o; do
        if [ -f "$out/lib/$crt" ]; then
          echo "$out/lib/$crt" > "$out/nix-support/$crt"
        fi
      done
      
      # Register library search
      echo "-L$out/lib" > $out/nix-support/libc-ldflags
    '';

    # Wrap bintools with fil-c's libc
    filc-bintools = base.wrapBintoolsWith {
      bintools = base.binutils;
      libc = filc-libc;
    };

    # Create compiler wrapper
    filc-cc = base.runCommand "filc-cc" {
      nativeBuildInputs = [ base.patchelf base.file ];
    } ''
      mkdir -p $out/bin
      cp -r ${filc-unwrapped}/build $out/
      cp -r ${filc-unwrapped}/pizfix $out/
      
      cat > $out/bin/clang << 'WRAPPER'
      #!/bin/bash
      exec ${filc-unwrapped}/build/bin/clang "$@"
      WRAPPER
      chmod +x $out/bin/clang
      
      cat > $out/bin/clang++ << 'WRAPPER'
      #!/bin/bash
      exec ${filc-unwrapped}/build/bin/clang++ "$@"
      WRAPPER
      chmod +x $out/bin/clang++
    '';

    # Wrap compiler with libc integration
    filc-wrapped = base.wrapCCWith {
      cc = filc-cc.overrideAttrs (old: {
        passthru = (old.passthru or {}) // {
          libllvm = base.llvmPackages_20.libllvm;
        };
      });
      libc = filc-libc;
      bintools = filc-bintools;
      isClang = true;
      
      extraBuildCommands = ''
        # Clang-specific flags
        echo "-nostdlibinc" >> $out/nix-support/cc-cflags
        
        # Ensure fil-c libraries are discoverable
        echo "-L${filc-libc}/lib" >> $out/nix-support/cc-cflags
        echo "-rpath ${filc-libc}/lib" >> $out/nix-support/cc-ldflags
        
        # GCC compatibility
        ln -s clang $out/bin/gcc
        ln -s clang++ $out/bin/g++
      '';
    };

    # Create stdenv using fil-c
    filenv = base.overrideCC base.stdenv filc-wrapped;

    # Utility to wrap packages with fil-c
    withFilC = pkg: pkg.override { stdenv = filenv; };

    # Full nixpkgs with fil-c as default compiler
    filpkgs = import nixpkgs {
      inherit system;
      config.replaceStdenv = { pkgs, ... }:
        pkgs.overrideCC pkgs.stdenv filc-wrapped;
    };

  in {
    packages.${system} = {
      inherit filpkgs filc-unwrapped;
      
      # Example packages built with fil-c
      gawk = withFilC base.gawk;
      gnused = withFilC base.gnused;
      gnutar = withFilC base.gnutar;
      sqlite = withFilC base.sqlite;
    };

    devShells.${system}.default = filenv.mkDerivation {
      name = "filc";
      buildInputs = [];
      shellHook = ''
        echo "Fil-C development environment"
        echo "Compiler: $(type -p clang)"
        clang --version | head -1
      '';
    };
  };
}
```

## Part 8: Troubleshooting and Verification

### 8.1 Common Issues

#### Issue: "ld-yolo-x86_64.so not found"
**Cause**: `filc-libc` not copying library files from build
**Solution**:
```bash
# Debug: Check what's in the build
ls -la ${filc-unwrapped}/pizfix/lib/
# Ensure files are being copied
cp -v ${filc-unwrapped}/pizfix/lib/. $out/lib/
```

#### Issue: "Undefined reference to libc functions"
**Cause**: Linker not finding libc.so
**Solution**:
- Verify `filc-bintools/nix-support/libc-ldflags` contains `-L/path/to/lib`
- Verify `filc-wrapped/nix-support/cc-ldflags` contains `-L/path/to/lib`

#### Issue: Binary uses wrong dynamic linker
**Cause**: `dynamic-linker` file not set correctly
**Solution**:
```bash
# Check what linker was embedded
readelf -l binary | grep INTERP

# Should show: /nix/store/.../lib/ld-yolo-x86_64.so
# NOT: /lib64/ld-linux-x86-64.so.2
```

#### Issue: "Cannot find -lc"
**Cause**: C library linker flags not properly inherited
**Solution**:
- Verify `filc-cc` is correctly built
- Verify `wrapCCWith` is properly called with `libc = filc-libc`
- Check that `add-flags.sh` is sourcing nix-support files

### 8.2 Debug Builds

Enable verbose output:

```bash
export NIX_DEBUG=7  # Maximum debug output
nix build . -L  # Show full build logs
```

Inspect wrapper state:

```bash
# After building wrapped compiler
cat result/nix-support/cc-cflags
cat result/nix-support/cc-ldflags
cat result/nix-support/libc-cflags
cat result/nix-support/dynamic-linker
```

### 8.3 Verification Script

```bash
#!/bin/bash
set -euo pipefail

CC_WRAPPER="result"
BINTOOLS="$CC_WRAPPER/nix-support/../../../bintools-wrapper-*"

echo "=== CC-Wrapper nix-support ==="
for f in "$CC_WRAPPER/nix-support"/*flags* "$CC_WRAPPER/nix-support/orig-*"; do
    if [ -f "$f" ]; then
        echo "$(basename $f): $(cat $f)"
    fi
done

echo ""
echo "=== Bintools-Wrapper nix-support ==="
if [ -d "$BINTOOLS/nix-support" ]; then
    for f in "$BINTOOLS/nix-support"/{dynamic-linker,libc-ldflags,orig-*}; do
        if [ -f "$f" ]; then
            echo "$(basename $f): $(cat $f)"
        fi
    done
fi

echo ""
echo "=== Clang Version ==="
"$CC_WRAPPER/bin/clang" --version

echo ""
echo "=== Test Compilation ==="
cat > /tmp/test.c << 'TESTC'
#include <stdio.h>
int main() { printf("Hello\n"); return 0; }
TESTC

"$CC_WRAPPER/bin/clang" -o /tmp/test /tmp/test.c
echo "Compilation successful!"

echo ""
echo "=== Binary Linker Check ==="
readelf -l /tmp/test | grep INTERP
```

## Part 9: Integration with External Packages

### 9.1 Using withFilC

```nix
packages.${system} = {
  # Individual packages with fil-c
  bash = withFilC base.bash;
  nginx = (withFilC base.nginx).override { openssl = openssl; };
  
  # Recursive override for dependencies
  myapp = withFilC (base.myapp.override {
    libc = filc-libc;
  });
};
```

### 9.2 Entire Nixpkgs with Fil-C

```nix
filpkgs = import nixpkgs {
  inherit system;
  config.replaceStdenv = { pkgs, ... }:
    pkgs.overrideCC pkgs.stdenv filc-wrapped;
};

packages.${system}.allWithFilC = filpkgs;
```

All packages built from this will use fil-c by default.

## Part 10: Summary Table

| Concept | Purpose | Location |
|---------|---------|----------|
| **wrapBintoolsWith** | Integrate binutils with libc | `cc-wrapper/default.nix` & `bintools-wrapper/default.nix` |
| **wrapCCWith** | Integrate compiler with libc and bintools | `cc-wrapper/default.nix` |
| **filc-libc** | Package fil-c's custom libc with metadata | `flake.nix` |
| **filc-bintools** | Bintools wrapper for fil-c libc | `flake.nix` |
| **filc-wrapped** | Final compiler ready for use | `flake.nix` |
| **filenv** | stdenv using fil-c | `flake.nix` |
| **nix-support/** | Configuration files for wrappers | Inside wrapped derivations |
| **dynamic-linker** | Custom dynamic linker path | `bintools-wrapper/nix-support/` |
| **libc-ldflags** | Linker library search paths | Both wrappers' `nix-support/` |
| **cc-cflags** | Compiler include paths | `cc-wrapper/nix-support/` |
| **ld-yolo-x86_64.so** | Fil-c's custom dynamic linker | `filc-libc/lib/` |

---

**End of Document**
