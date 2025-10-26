# Fil-C Driver Flag Support

This document describes the new command-line flags added to the Fil-C Clang driver to make it more Nix-friendly and eliminate the need for strict directory layout requirements.

## Problem

Previously, the Fil-C driver discovered its resources (headers, libraries, CRT files, dynamic linker) by:
1. Finding the clang binary's real filesystem location
2. Walking up the directory tree to find `../../../pizfix`
3. Using hardcoded relative paths from there

This caused issues in Nix because:
- Symlinks and wrappers don't work (driver resolves to real path)
- Required copying everything into a specific directory layout
- Couldn't easily compose different library versions

## Solution

Added explicit command-line flags that override the automatic discovery, with fallback to existing behavior:

### New Flags

- `--filc-resource-dir=PATH` - Override the entire pizfix root directory
- `--filc-dynamic-linker=PATH` - Override path to `ld-yolo-x86_64.so`
- `--filc-crt-path=PATH` - Override directory containing CRT objects and libraries
- `--filc-stdfil-include=PATH` - Override Fil-C runtime headers directory
- `--filc-os-include=PATH` - Override kernel headers directory
- `--filc-include=PATH` - Override libc headers directory

### Precedence

For each resource, the driver checks in this order:
1. Explicit flag (highest priority)
2. Discovered `pizfix` directory (via `../../../pizfix` from binary)
3. `/opt/fil` installation
4. System defaults (`/usr`, `/lib`)

### Implementation

#### Options.td
Added option definitions for all six flags in `include/clang/Driver/Options.td`.

#### Driver.cpp
- Added `PizfixRoot` member to `Driver` class
- Set `PizfixRoot` when discovering pizfix directory
- Check `--filc-resource-dir` flag in `BuildCompilation()` and override if present

#### Linux.cpp
- `getDynamicLinker()` - Check `--filc-dynamic-linker` flag first
- `AddClangSystemIncludeArgs()` - Check individual include flags, fall back to `PizfixRoot` subdirectories

#### Gnu.cpp
- Updated `GetYoloLibPath()` lambda to check `--filc-crt-path` flag
- Updated library search paths to use flag-based paths
- Simplified `filc_crt.o`/`filc_mincrt.o` handling using `GetYoloLibPath()`

## Nix Integration

### Before

```nix
mkFilcClang = pizfix: base.runCommand "pizfix-filc" {
  nativeBuildInputs = [base.makeWrapper];
} ''
  mkdir -p $out/clang/bin
  cp -r ${pizfix} $out/pizfix           # Copy entire pizfix structure
  chmod -R u+w $out/pizfix
  
  cp ${filc0}/bin/clang-${llvmMajor} $out/clang/bin/clang-${llvmMajor}
  chmod +x $out/clang/bin/clang-${llvmMajor}
  
  wrapProgram $out/clang/bin/clang-${llvmMajor} \
    --add-flags "--gcc-toolchain=${gcc.cc}" \
    --add-flags "-resource-dir ${filc0}/lib/clang/${llvmMajor}"
  
  mkdir -p $out/bin
  ln -s ../clang/bin/clang-${llvmMajor} $out/bin/clang
  ln -s ../clang/bin/clang-${llvmMajor} $out/bin/clang++
'';
```

### After

```nix
mkFilcClang = { crtLib, yoloInclude, osInclude, stdfilInclude }: 
  base.runCommand "filc" {
    nativeBuildInputs = [base.makeWrapper];
  } ''
    mkdir -p $out/bin
    
    makeWrapper ${filc0}/bin/clang-${llvmMajor} $out/bin/clang \
      --add-flags "--gcc-toolchain=${gcc.cc}" \
      --add-flags "-resource-dir ${filc0}/lib/clang/${llvmMajor}" \
      --add-flags "--filc-dynamic-linker=${crtLib}/ld-yolo-x86_64.so" \
      --add-flags "--filc-crt-path=${crtLib}" \
      --add-flags "--filc-stdfil-include=${stdfilInclude}" \
      --add-flags "--filc-os-include=${osInclude}" \
      --add-flags "--filc-include=${yoloInclude}"
    
    ln -s clang $out/bin/clang++
  '';
```

## Benefits

1. **No directory copying** - Just reference existing store paths
2. **Symlinks work** - Wrapper doesn't need special directory layout
3. **Explicit dependencies** - Clear which paths are used where
4. **Easy composition** - Can mix different library/header versions
5. **Backwards compatible** - Existing pizfix and /opt/fil setups still work

## Testing

Existing pizfix-based setups continue to work unchanged. The flags only override when explicitly provided.

Test that the new approach works:
```bash
nix build .#filc2
./result/bin/clang --version
./result/bin/clang -### test.c  # Shows all paths being used
```
