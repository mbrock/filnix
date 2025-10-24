# Fil-C CC-Wrapper Implementation - Quick Reference

## Current Status
Your current `flake.nix` implementation is already **very close to correct**. The architecture is sound.

## Three-Layer Wrapper Architecture

```
Package (e.g., bash)
    ↓
CC-Wrapper (clang/gcc + headers/flags)
    ↓
Bintools-Wrapper (ld + linker/linking)
    ↓
Libc (yolo-glibc + user-glibc)
```

## Key Components Already Correct in Your Flake

### 1. filc-libc (Perfect structure)
```nix
filc-libc = base.runCommand "filc-libc" {} ''
  mkdir -p $out/{include,lib} $out/nix-support
  # Copies yolo-glibc and user-glibc
  # CRITICAL: Sets dynamic-linker to ld-yolo-x86_64.so
  echo "$out/lib/ld-yolo-x86_64.so" > $out/nix-support/dynamic-linker
  # Registers CRT files
'';
```

### 2. filc-bintools (Correct usage)
```nix
filc-bintools = base.wrapBintoolsWith {
  bintools = base.binutils;
  libc = filc-libc;  # Links to your custom libc
};
```

What this does:
- Reads `dynamic-linker` from filc-libc's nix-support
- Creates bintools-wrapper/nix-support/dynamic-linker
- Ensures linker uses ld-yolo-x86_64.so

### 3. filc-wrapped (Structure is good)
```nix
filc-wrapped = base.wrapCCWith {
  cc = filc-cc;
  libc = filc-libc;
  bintools = filc-bintools;
  isClang = true;
  extraBuildCommands = ''
    echo "-L${filc-libc}/lib" >> $out/nix-support/cc-cflags
    echo "-rpath ${filc-libc}/lib" >> $out/nix-support/cc-ldflags
  '';
};
```

## Critical nix-support Files Reference

### In cc-wrapper's nix-support/:
- **cc-cflags**: `-B/path/lib -L/path/lib` → compiler search paths
- **cc-ldflags**: `-L/path/lib -rpath /path/lib` → linker search paths
- **libc-cflags**: `-isystem /path/include` → C header paths
- **libc-crt1-cflags**: `-B/path/lib` → startup code paths
- **libc-ldflags**: `-L/path/lib` → C library linking

### In bintools-wrapper's nix-support/:
- **dynamic-linker**: `/nix/store/.../lib/ld-yolo-x86_64.so` → custom linker path
- **ld-set-dynamic-linker**: (empty file) → flag to auto-apply dynamic linker
- **libc-ldflags**: `-L/path/lib` → linker library search

## How It Works: The Pipeline

### During Compilation:
1. `cc-wrapper.sh` is invoked
2. Reads nix-support files in order:
   - libc-crt1-cflags (startup code)
   - libc-cflags (C headers)
   - cc-cflags (compiler flags)
3. Final command: `clang -B/path/lib -isystem /path/include <user-code>`

### During Linking:
1. `ld-wrapper.sh` is invoked
2. Reads nix-support files:
   - libc-ldflags (-L paths)
   - dynamic-linker (ld-yolo-x86_64.so)
3. Final command: `ld -L/path/lib -dynamic-linker /nix/store/.../ld-yolo-x86_64.so <objs>`
4. Resulting binary's ELF INTERP section: `/nix/store/.../lib/ld-yolo-x86_64.so`

## Environment Variable System

Variables use `suffixSalt` to avoid conflicts when multiple cc-wrappers are active:

```bash
# NOT: export NIX_CFLAGS_COMPILE="-march=x86-64"
# BUT: export NIX_CFLAGS_COMPILE_x86_64_unknown_linux_gnu="-march=x86-64"
```

This allows many cc-wrappers to coexist without clobbering each other.

## Recommended Minor Enhancements

### 1. Add explicit -nostdlibinc for Clang
```nix
extraBuildCommands = ''
  echo "-nostdlibinc" >> $out/nix-support/cc-cflags
  echo "-L${filc-libc}/lib" >> $out/nix-support/cc-cflags
  echo "-rpath ${filc-libc}/lib" >> $out/nix-support/cc-ldflags
'';
```

### 2. Enhanced filc-libc with error checking
```nix
filc-libc = base.runCommand "filc-libc" {} ''
  set -euo pipefail
  mkdir -p $out/{include,lib,nix-support}
  
  cp -r ${filc-unwrapped}/pizfix/include/. $out/include/ 2>/dev/null || true
  cp -r ${filc-unwrapped}/pizfix/lib/. $out/lib/ 2>/dev/null || true
  
  # ERROR CHECK for custom linker
  if [ -f "$out/lib/ld-yolo-x86_64.so" ]; then
    echo "$out/lib/ld-yolo-x86_64.so" > $out/nix-support/dynamic-linker
  else
    echo "ERROR: ld-yolo-x86_64.so not found" >&2
    exit 1
  fi
  
  # CRT registration
  for crt in crt1.o rcrt1.o Scrt1.o crti.o crtn.o; do
    if [ -f "$out/lib/$crt" ]; then
      echo "$out/lib/$crt" > "$out/nix-support/$crt"
    fi
  done
  
  # Library search path
  echo "-L$out/lib" > $out/nix-support/libc-ldflags
'';
```

### 3. Add libllvm passthru
```nix
filc-wrapped = base.wrapCCWith {
  cc = filc-cc.overrideAttrs (old: {
    passthru = (old.passthru or {}) // {
      libllvm = base.llvmPackages_20.libllvm;
    };
  });
  # ... rest stays same
};
```

## Verification Checklist

After building, verify these files exist and have correct content:

```bash
# CC-Wrapper (should contain fil-c paths)
cat $result/nix-support/cc-cflags        # Should have -L...filc-libc/lib
cat $result/nix-support/cc-ldflags       # Should have -rpath...filc-libc/lib
cat $result/nix-support/libc-cflags      # Should have -isystem...include
cat $result/nix-support/libc-crt1-cflags # Should have -B...lib

# Bintools-Wrapper (should reference fil-c's custom linker)
cat $bintools/nix-support/dynamic-linker      # Should be ld-yolo-x86_64.so
cat $bintools/nix-support/libc-ldflags        # Should have -L...filc-libc/lib

# Test binary (should use custom linker)
readelf -l /tmp/test | grep INTERP
# Expected: [Requesting program interpreter: /nix/store/.../lib/ld-yolo-x86_64.so]
```

## Clang-Specific Notes

1. **Resource Directory**: Clang bakes its resource directory at compile time - no special handling needed
2. **nostdlibinc**: Prevents system /usr/include from leaking in
3. **GCC Compatibility**: Your symlinks (gcc → clang, g++ → clang++) are correct
4. **LibLLVM**: Clang may need access to LLVM runtime libraries via passthru

## Debugging Commands

```bash
# See what wrapper is actually doing
export NIX_DEBUG=7
nix build . -L

# Inspect wrapper environment
cat result/nix-support/cc-cflags
cat result/nix-support/cc-ldflags

# Check compiled binary
readelf -l /tmp/binary | head -20

# Trace compilation
clang -v -c test.c

# Verify dynamic linker
ldd /tmp/binary
```

## Files to Understand

- `/tmp/nixpkgs-nixos-unstable/pkgs/build-support/cc-wrapper/default.nix` (1000+ lines)
  - Main wrapper logic, generates nix-support files in postFixup

- `/tmp/nixpkgs-nixos-unstable/pkgs/build-support/bintools-wrapper/default.nix` (500+ lines)
  - Binutils wrapper, handles dynamic-linker integration

- `/tmp/nixpkgs-nixos-unstable/pkgs/build-support/cc-wrapper/add-flags.sh` (80 lines)
  - Reads nix-support files, builds NIX_* environment variables

- `/tmp/nixpkgs-nixos-unstable/pkgs/build-support/bintools-wrapper/add-flags.sh` (40 lines)
  - Similar for linker flags

- `/tmp/nixpkgs-nixos-unstable/pkgs/build-support/cc-wrapper/cc-wrapper.sh` (200+ lines)
  - Main wrapper script, calls add-flags.sh

- `/tmp/nixpkgs-nixos-unstable/pkgs/build-support/bintools-wrapper/ld-wrapper.sh` (200+ lines)
  - Linker wrapper script

## Summary

Your current implementation is **architecturally correct** and follows nixpkgs conventions properly:

✓ Custom libc (filc-libc) with yolo-glibc + user-glibc
✓ Proper dynamic linker setup (ld-yolo-x86_64.so)
✓ Bintools integration (wrapBintoolsWith)
✓ CC wrapper setup (wrapCCWith with isClang=true)
✓ stdenv integration (overrideCC)

The recommended enhancements above are minor refinements for robustness, not critical fixes.

## Next Steps

1. Apply the enhanced filc-libc with error checking
2. Add explicit `-nostdlibinc` to extraBuildCommands
3. Test with: `nix build .#gawk` (or another simple package)
4. Verify binary uses ld-yolo-x86_64.so: `readelf -l result/bin/gawk | grep INTERP`
5. Run the verification script from the full analysis document

See `/home/mbrock/filnix/NIX_WRAPPER_ANALYSIS.md` for the complete deep-dive reference.
