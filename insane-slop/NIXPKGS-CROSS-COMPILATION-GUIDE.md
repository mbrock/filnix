# Fil-C as a Pseudo-Cross Target in Nixpkgs
## Comprehensive Integration Pattern Guide

### Executive Summary

This document provides detailed patterns for treating Fil-C as a "pseudo-cross compilation target" in Nixpkgs, even when running on the same architecture (x86_64-linux). This approach leverages nixpkgs' well-established cross-compilation infrastructure to treat Fil-C as an ABI-incompatible target that requires special handling for interoperability with standard glibc code.

---

## 1. Key Areas of Nixpkgs Cross-Compilation Infrastructure

### 1.1 lib/systems/default.nix - Platform Elaboration

The core elaboration function (`elaborate`) at lines 71-620 takes a system specification and produces a complete platform definition with:

- **Parsed system**: CPU, vendor, kernel, ABI information
- **Computed attributes**: libc, linker, hasSharedLibraries, canExecute rules
- **Platform predicates**: isLinux, isAndroid, isDarwin, etc.
- **Compiler settings**: gcc flags, rust platform mappings, golang GOARCH

**Key Pattern for Fil-C:**
```nix
# In lib/systems/parse.nix, ABI definitions control how the platform behaves
abis = setTypes types.openAbi {
  filc = {
    # Optional: float convention or other attributes
    float = "hard";  # or define custom attributes
    assertions = [
      {
        assertion = platform: platform.isLinux && platform.isx86_64;
        message = "Fil-C is only available for x86_64-linux";
      }
    ];
  };
};
```

### 1.2 lib/systems/parse.nix - System String Parsing

**Triple/Quadruple Format Parsing (lines 776-875):**
- 1-part: Just CPU (e.g., "avr")
- 2-part: Ambiguous, resolved by heuristics (e.g., "arm-cygwin")
- 3-part: CPU-vendor-OS or CPU-kernel-ABI (e.g., "x86_64-unknown-linux-gnu")
- 4-part: CPU-vendor-kernel-ABI (e.g., "x86_64-unknown-linux-filc")

**Critical: CPU Type Definition (lines 121-400)**

CPU types are registered with properties:
```nix
cpuTypes.x86_64 = {
  bits = 64;
  significantByte = littleEndian;
  family = "x86";
  arch = "x86-64";
};
```

**Pattern for Fil-C:**
```nix
# If treating Fil-C as separate "ABI", use standard CPU with custom ABI
# config triple: x86_64-unknown-linux-filc
# Parsed as: CPU=x86_64, vendor=unknown, kernel=linux, abi=filc

# OR: Create pseudo-vendor to distinguish from glibc
# config triple: x86_64-filc-linux-gnu
# This creates: CPU=x86_64, vendor=filc, kernel=linux, abi=gnu
```

### 1.3 lib/systems/examples.nix - System Examples

Lines 8-444 show how platforms are defined for nixpkgs:
```nix
sheevaplug = {
  config = "armv5tel-unknown-linux-gnueabi";
}
// platforms.sheevaplug;

aarch64-android = {
  config = "aarch64-unknown-linux-android";
  androidSdkVersion = "35";
  androidNdkVersion = "27";
  libc = "bionic";
  useAndroidPrebuilt = false;
  useLLVM = true;
};
```

**Pattern for Fil-C:**
```nix
filc-x86_64 = {
  config = "x86_64-unknown-linux-filc";
  # OR use pseudo-vendor:
  # config = "x86_64-filc-linux-gnu";
  
  # Mark this as using a custom libc to trigger cross-compilation mode
  libc = "filc";  # CRITICAL: Different from "glibc"
  
  # Optional: Mark as using special compiler
  # This prevents automatic "native" stdenv selection
  useLLVM = true;
};
```

### 1.4 pkgs/stdenv/cross/default.nix - Cross-Compilation Stdenv

Lines 1-139 show the cross-compilation stdenv construction:

**Key Pattern:**
```nix
# Line 44: Cross-compilation is triggered by:
if crossSystem != localSystem || crossOverlays != [ ] then
  stagesCross
```

**For Fil-C to be treated as cross-compilation:**
```nix
# Option 1: Different system string
localSystem = "x86_64-unknown-linux-gnu"
crossSystem = "x86_64-unknown-linux-filc"  # Different string

# Option 2: Same system string but marker in crossSystem
crossSystem = {
  system = "x86_64-linux";
  libc = "filc";  # Different libc triggers cross-compile behavior
}
```

The cross stdenv does:
1. Creates stdenvNoCC with buildPlatform != hostPlatform (line 54-88)
2. Sets extraNativeBuildInputs like updateAutotoolsGnuConfigScriptsHook (line 72-86)
3. Ensures old overrides are disabled (line 62)
4. Selects appropriate compiler (lines 106-128)

### 1.5 pkgs/top-level/stage.nix - Cross-Compilation Package Sets

Lines 238 creates pkgsCross:
```nix
pkgsCross = lib.mapAttrs (n: crossSystem: nixpkgsFun { inherit crossSystem; }) 
            lib.systems.examples;
```

**For Fil-C integration:**
```nix
# Add to lib/systems/examples.nix
filc = {
  config = "x86_64-unknown-linux-filc";
  libc = "filc";
};

# Then pkgsCross.filc becomes available automatically
# pkgsCross.filc.hello builds hello with Fil-C
```

---

## 2. ABI Incompatibility Handling Patterns

### 2.1 ABI Definition in lib/systems/parse.nix (lines 649-748)

The key insight: **ABIs are attributes in a `setTypes` registry**

```nix
abis = setTypes types.openAbi {
  gnu = {
    assertions = [
      {
        assertion = platform: !platform.isAarch32;
        message = "gnu ABI is ambiguous on 32-bit ARM";
      }
    ];
  };
  
  # NEW: Add Fil-C ABI
  filc = {
    # Optionally store fil-c specific attributes
    # Example: How to pass Fil-C-specific flags
    assertions = [
      {
        assertion = platform: platform.isLinux && platform.isx86_64;
        message = "Fil-C is only available on x86_64-linux";
      }
    ];
  };
};
```

**Implementation Pattern:**
```nix
# 1. Register the ABI in parse.nix
# 2. Register the libc in default.nix (line 120-159)
libc =
  if final.isLinux && final.parsed.abi.name == "filc" then
    "filc"
  else if final.isLinux then
    "glibc"
  # ... other cases ...
  else
    "native/impure";
```

### 2.2 Libc Specification Pattern

Lines 120-159 in lib/systems/default.nix show how libc is inferred:

**Key: libc affects header paths, linking, and runtime behavior**

```nix
# Example: Android
libc =
  if final.isAndroid then
    "bionic"  # Different libc = different cross-compilation mode
  else if final.isLinux then
    "glibc"
  else
    "native/impure";
```

**For Fil-C:**
```nix
# In lib/systems/default.nix, add:
libc =
  if final.parsed.abi.name == "filc" then
    "filc"  # CRITICAL: Different from "glibc"
  else if final.isDarwin then
    "libSystem"
  # ... rest of conditions ...
```

**Why this matters:**
- `libc != buildPlatform.libc` triggers cross-compilation mode
- Different libc means: separate header paths, runtime, linking rules
- Allows proper stdenv selection (lines 44-50 in pkgs/stdenv/default.nix)

### 2.3 Cross-Compilation Triggering Mechanism

From pkgs/stdenv/default.nix lines 44-50:
```nix
if crossSystem != localSystem || crossOverlays != [ ] then
  stagesCross
else if config ? replaceStdenv then
  stagesCustom
else if localSystem.isLinux then
  stagesLinux
```

**Method 1: Different system strings**
```nix
localSystem = {
  config = "x86_64-unknown-linux-gnu";
  libc = "glibc";
};
crossSystem = {
  config = "x86_64-unknown-linux-filc";
  libc = "filc";
};
# crossSystem != localSystem → triggers stagesCross
```

**Method 2: Same system string, different attributes**
```nix
localSystem = {
  config = "x86_64-linux";
  libc = "glibc";
};
crossSystem = {
  config = "x86_64-linux";
  libc = "filc";
  # If "system" attribute differs, cross-compilation triggers
};
```

**Key Detail:** In lib/systems/default.nix, the `system` attribute is computed from `parsed`:
```nix
# Line 90: system is derived from parsed
system = parse.doubleFromSystem final.parsed;  # e.g., "x86_64-linux"
```

If two platforms have different `parsed.abi` but same `system`, they may not be treated as cross-compilation by `!=` comparison. **Solution: Use different `config` triple strings.**

---

## 3. Compiler and Linker Flag Propagation

### 3.1 GCC Configuration in lib/systems/platforms.nix

Lines 10-637 show platform-specific GCC settings:

```nix
armv7l-hf-multiplatform = {
  linux-kernel = { ... };
  gcc = {
    arch = "armv7-a";
    fpu = "vfpv3-d16";
  };
};

# These flow through to:
# - buildInputs for gcc
# - Compiler flags added to stdenv
```

### 3.2 Compiler Selection in pkgs/stdenv/cross/default.nix

Lines 106-128 show compiler selection based on platform attributes:

```nix
cc =
  if crossSystem.useiOSPrebuilt or false then
    buildPackages.darwin.iosSdkPkgs.clang
  else if crossSystem.useAndroidPrebuilt or false then
    buildPackages."androidndkPkgs_${crossSystem.androidNdkVersion}".clang
  else if crossSystem.isDarwin then
    buildPackages.llvmPackages.systemLibcxxClang
  else if crossSystem.useLLVM or false then
    buildPackages.llvmPackages.clang
  else if crossSystem.useZig or false then
    buildPackages.zig.cc
  else
    buildPackages.gcc;
```

**Pattern for Fil-C:**
```nix
# Option 1: Add Fil-C flag
else if crossSystem.useFilC or false then
  buildPackages.filc-wrapped
else if crossSystem.useLLVM or false then
  buildPackages.llvmPackages.clang

# Option 2: Create inspection predicate
# In lib/systems/inspect.nix, add:
patterns = {
  isFilC = {
    libc = "filc";
  };
};
# Then in cross/default.nix:
else if crossSystem.isFilC then
  buildPackages.filc-wrapped
```

### 3.3 stdenv Overrides for Fil-C

In pkgs/stdenv/generic/make-derivation.nix, flags are added:

**Pattern:**
```nix
# Add to stdenv construction
extraBuildInputs = lib.optionals hostPlatform.isFilC [
  buildPackages.filc-compatibility-layer
];

extraNativeBuildInputs = old.extraNativeBuildInputs
  ++ lib.optionals hostPlatform.isFilC [
    buildPackages.updateAutotoolsGnuConfigScriptsHook
  ];
```

---

## 4. Making Fil-C Appear as a "Cross" Target

### 4.1 System Definition Pattern

**Primary approach: Use pseudo-vendor or custom ABI**

```nix
# In lib/systems/examples.nix
filc-x86_64-linux = {
  # Method A: Custom ABI suffix
  config = "x86_64-unknown-linux-filc";
  
  # Mark as different from standard glibc
  libc = "filc";
  
  # Optional: Mark special properties
  isFilC = true;  # For easy detection
  useFilC = true; # For compiler selection
};

# OR Method B: Pseudo-vendor for clarity
filc-x86_64-linux = {
  config = "x86_64-filc-linux-gnu";
  libc = "filc";
  useFilC = true;
};
```

### 4.2 Registration in lib/systems/

**1. Add ABI to parse.nix:**
```nix
abis = setTypes types.openAbi {
  # ... existing abis ...
  filc = {
    assertions = [
      {
        assertion = platform: platform.isLinux && platform.isx86_64;
        message = "Fil-C ABI only supported on x86_64-linux";
      }
    ];
  };
};
```

**2. Add Libc handling to default.nix (line ~140):**
```nix
libc =
  if final.isDarwin then
    "libSystem"
  else if final.isMsvc then
    "ucrt"
  # INSERT HERE:
  else if final.parsed.abi.name == "filc" then
    "filc"
  else if final.isMusl then
    "musl"
  # ... rest ...
```

**3. Add to inspect.nix for predicates:**
```nix
patterns = {
  isFilC = {
    libc = "filc";
  };
  # Or:
  isFilC = {
    abi = abis.filc;
  };
};
```

### 4.3 Example Definition Pattern

**In lib/systems/examples.nix:**
```nix
rec {
  # ... existing definitions ...
  
  # Fil-C targets
  filc-x86_64 = {
    config = "x86_64-unknown-linux-filc";
    libc = "filc";
    useFilC = true;
  };
  
  # Also provide the example without filc suffix for backwards compatibility
  x86_64-filc = filc-x86_64;
}
```

---

## 5. Compiler and Linker Flag Propagation for Fil-C

### 5.1 Wrapper Script Pattern

Current filnix uses simple wrapper scripts:

```nix
filc-clang = base.writeShellScriptBin "clang" ''
  exec ${filc-unwrapped}/build/bin/clang "$@"
'';
```

**For cross-compilation mode, enhance with platform detection:**
```nix
filc-wrapped = base.wrapCCWith {
  cc = filc-cc;
  libc = filc-libc;
  bintools = filc-bintools;
  isClang = true;
  
  extraBuildCommands = ''
    # Disable incompatible flags from glibc stdenv
    sed -i '/NIX_CFLAGS_COMPILE/d' $out/nix-support/cc-cflags || true
    
    # Add Fil-C specific flags
    echo "-Qunused-arguments" >> $out/nix-support/cc-cflags
    echo "-L${filc-libc}/lib" >> $out/nix-support/cc-cflags
    
    # Set Fil-C runtime library path
    echo "-rpath ${filc-libc}/lib" >> $out/nix-support/cc-ldflags
  '';
};
```

### 5.2 Standard Environment Integration

**Pattern in pkgs/stdenv/cross/default.nix:**

```nix
baseStdenv = stdenvNoCC.override {
  cc =
    if crossSystem.isFilC then
      buildPackages.filc-wrapped
    else if crossSystem.isDarwin then
      buildPackages.llvmPackages.systemLibcxxClang
    # ... rest of conditions ...
  
  # Add Fil-C compatibility layer when needed
  extraBuildInputs = lib.optionals hostPlatform.isFilC [
    buildPackages.filc-compat-layer
  ];
};
```

### 5.3 Make-Derivation Integration

**Pattern to add Fil-C awareness:**

In pkgs/stdenv/generic/make-derivation.nix, near line 150-200 where flags are set:

```nix
# Fil-C specific flag handling
+ lib.optionalString (stdenv.hostPlatform.isFilC) ''
  # Disable incompatible hardening measures
  # (fil-c has its own safety mechanisms)
  ''
  
+ lib.optionalString (stdenv.targetPlatform.isFilC) ''
  # When targeting fil-c for runtime
  export NIX_FILC_RUNTIME="${filc-runtime}"
  ''
```

---

## 6. Integration Strategy for Filnix

### 6.1 Minimal Integration (Current Approach Enhancement)

Keep using the custom stdenv approach but add cross-compilation support:

```nix
# In flake.nix

filc-platform = lib.systems.examples.filc-x86_64;

# Build with filc as cross-target
filpkgs-cross = import nixpkgs {
  inherit system;
  localSystem = "x86_64-linux";
  crossSystem = filc-platform;
};

# Packages
packages.${system}.filc-nginx = filpkgs-cross.nginx;
```

### 6.2 Full Integration (Upstream Approach)

1. **Prepare patches for nixpkgs:**
   - Add fil-c ABI to lib/systems/parse.nix
   - Add libc detection to lib/systems/default.nix
   - Add inspect patterns to lib/systems/inspect.nix
   - Add example to lib/systems/examples.nix

2. **Create overlay in filnix:**
```nix
filc-nixpkgs = final: prev: {
  # Override compiler selection for filc targets
  stdenvAdapters = prev.stdenvAdapters // {
    makeFilC = stdenv: prev.overrideCC stdenv final.filc-wrapped;
  };
};
```

3. **Use in flake:**
```nix
filpkgs = import nixpkgs {
  system = "x86_64-linux";
  crossSystem = "x86_64-unknown-linux-filc";
  overlays = [
    filc-nixpkgs
    # ... other overlays
  ];
};
```

### 6.3 Advantages of Cross-Compilation Approach

1. **Automatic native build tools:** stdenv handles native vs. cross correctly
2. **Hook integration:** updateAutotoolsGnuConfigScriptsHook applied automatically
3. **Splicing:** buildPackages vs. hostPackages handled correctly
4. **Standards compliance:** Uses established Nix patterns

---

## 7. Specific Implementation Patterns

### 7.1 ABI String Pattern

**For x86_64-linux with Fil-C:**

Option A (Custom ABI):
```
x86_64-unknown-linux-filc
  └─ Parsed as: CPU=x86_64, vendor=unknown, kernel=linux, abi=filc
  └─ Advantages: Clear in triple, parsed.abi.name == "filc"
  └─ Challenges: Requires parse.nix changes for every ABI variant
```

Option B (Pseudo-vendor):
```
x86_64-filc-linux-gnu
  └─ Parsed as: CPU=x86_64, vendor=filc, kernel=linux, abi=gnu
  └─ Advantages: Vendor distinction doesn't require parse.nix changes
  └─ Challenges: Vendor isn't standard interpretation
```

**Recommendation: Use Option A (custom ABI) because:**
- ABIs are designed for exactly this: distinguishing binary interfaces
- parse.nix already has ABI definition infrastructure
- Matches existing patterns (musl, uclibc, bionic)
- Easier to detect: `platform.parsed.abi.name == "filc"`

### 7.2 Libc Attribute Pattern

**Critical for cross-compilation detection:**

```nix
# In lib/systems/default.nix
libc =
  if final.isDarwin then "libSystem"
  else if final.isMsvc then "ucrt"
  else if final.isMinGW then "msvcrt"
  else if final.isCygwin then "cygwin"
  else if final.isMusl then "musl"
  else if final.parsed.abi.name == "filc" then "filc"  # ADD HERE
  else if final.isLinux then "glibc"
  else "native/impure";
```

**This enables:**
```nix
# Cross-compilation detection
if crossSystem.libc != localSystem.libc then
  # Trigger cross-compilation stdenv (automatically happens)
```

### 7.3 Compiler Selection Pattern

**In pkgs/stdenv/cross/default.nix:**

```nix
cc =
  if crossSystem.isFilC then
    buildPackages.filc-wrapped
  else if crossSystem.isDarwin then
    buildPackages.llvmPackages.systemLibcxxClang
  else if crossSystem.useLLVM or false then
    buildPackages.llvmPackages.clang
  else
    buildPackages.gcc;
```

Requires lib/systems/inspect.nix to have:
```nix
patterns.isFilC = {
  abi = abis.filc;
};
# OR
patterns.isFilC = {
  libc = "filc";
};
```

---

## 8. Key Files to Modify in Nixpkgs for Full Integration

### 8.1 lib/systems/parse.nix (lines 649-748)

Add Fil-C ABI definition:
```nix
abis = setTypes types.openAbi {
  # ... existing entries ...
  
  filc = {
    assertions = [
      {
        assertion = platform: platform.isLinux && platform.isx86_64;
        message = "The \"filc\" ABI is only available on x86_64-linux";
      }
    ];
  };
};
```

### 8.2 lib/systems/default.nix (lines 120-159)

Add libc detection:
```nix
libc =
  if final.isDarwin then "libSystem"
  else if final.isMsvc then "ucrt"
  else if final.isMinGW then "msvcrt"
  else if final.isCygwin then "cygwin"
  else if final.isWasi then "wasilibc"
  else if final.isMusl then "musl"
  else if final.parsed.abi.name == "filc" then "filc"  # ADD
  else if final.isUClibc then "uclibc"
  # ... rest of branches ...
```

### 8.3 lib/systems/inspect.nix (around line 30-440)

Add predicate:
```nix
patterns = rec {
  # ... existing patterns ...
  
  isFilC = {
    abi = abis.filc;
  };
};
```

### 8.4 lib/systems/examples.nix (end of file)

Add example target:
```nix
filc-x86_64 = {
  config = "x86_64-unknown-linux-filc";
};
```

### 8.5 pkgs/stdenv/cross/default.nix (lines 106-128)

Add compiler selection:
```nix
cc =
  if crossSystem.isFilC then
    buildPackages.filc-wrapped
  else if crossSystem.isDarwin then
    buildPackages.llvmPackages.systemLibcxxClang
  # ... rest ...
```

---

## 9. Practical Integration Checklist

### Phase 1: Minimal Integration (Works Today)

- [x] Current filnix approach with custom stdenv override
- [ ] Add `isFilC` predicate to flake overlay
- [ ] Document current stdenv override approach

### Phase 2: Enhanced Integration

- [ ] Create nixpkgs patches for parse.nix, default.nix, inspect.nix
- [ ] Test with patched nixpkgs: `mkCross` with filc target
- [ ] Verify cross-compilation stdenv is used
- [ ] Test updateAutotoolsGnuConfigScriptsHook application

### Phase 3: Upstreamable Integration

- [ ] Clean up patches for nixpkgs submission
- [ ] Add tests to nixpkgs/tests/cross/default.nix
- [ ] Document in nixpkgs manual
- [ ] Add pkgsCross.filc-x86_64 to stage.nix

---

## 10. Code Examples

### 10.1 Complete Platform Definition

```nix
# lib/systems/examples.nix
filc-x86_64 = {
  config = "x86_64-unknown-linux-filc";
  # libc is inferred as "filc" from parse.nix
};

# Also provide shorthand
filc = filc-x86_64;
```

### 10.2 Minimal Overlay for Current Integration

```nix
# In filnix flake.nix
filc-overlay = final: prev: {
  lib = prev.lib // {
    systems = prev.lib.systems // {
      examples = prev.lib.systems.examples // {
        filc-x86_64 = {
          config = "x86_64-unknown-linux-filc";
        };
        filc = final.lib.systems.examples.filc-x86_64;
      };
    };
  };
};

filpkgs = import nixpkgs {
  system = "x86_64-linux";
  crossSystem = "x86_64-unknown-linux-filc";
  overlays = [filc-overlay];
};
```

### 10.3 Complete Inspect Pattern

```nix
# lib/systems/inspect.nix
patterns = rec {
  # ... existing patterns ...
  
  isFilC = {
    abi = abis.filc;
  };
  
  isFilCTarget = [
    # Match filc ABI regardless of architecture
    { abi = abis.filc; }
  ];
};

# predicates.isFilC(platform.parsed) -> bool
```

---

## 11. Important Caveats and Considerations

### 11.1 ABI String Stability

- Custom ABI strings (e.g., "filc") must be **stable** once defined
- They affect package store paths via system string
- Changing ABI name invalidates all packages
- Version with `-gnu` suffix for compatibility: consider "filc-gnuabi"

### 11.2 Libc vs. Runtime

- `libc = "filc"` is detected by cross-compilation logic
- Actual libc at runtime is still provided by `filc-libc` wrapper
- Don't confuse: `parse.abi.name` vs. runtime libc implementation

### 11.3 Cross-Compilation Overhead

- Cross-compilation mode means: native build tools need separate derivation
- For same-architecture targets, there's a performance cost
- Consider: lazy evaluation, binary cache

### 11.4 Compatibility Shims

- Some configure scripts may not recognize "filc" ABI
- May need wrapper/compatibility scripts:
  ```bash
  config.sub: *-*-*filc*) ... ;;
  ```

---

## 12. Summary Table: Integration Approaches

| Approach | Current | Enhanced | Full |
|----------|---------|----------|------|
| **Location** | filnix only | filnix + overlay | upstream nixpkgs |
| **ABI registered** | No | filnix overlay | parse.nix |
| **Libc detection** | Manual override | Overlay pattern | default.nix |
| **Cross-compilation** | Custom stdenv | Explicit cross | Automatic |
| **pkgsCross.filc** | Manual | Manual + wrapper | Automatic |
| **Complexity** | Low | Medium | High |
| **Usability** | Good | Excellent | Excellent |
| **Upstream-able** | No | Partial | Yes |

---

## References

Key nixpkgs files analyzed:
- `/home/mbrock/nixpkgs/lib/systems/default.nix` (620 lines) - Platform elaboration
- `/home/mbrock/nixpkgs/lib/systems/parse.nix` (970 lines) - System parsing and ABI/CPU definitions
- `/home/mbrock/nixpkgs/lib/systems/examples.nix` (444 lines) - Example platform definitions
- `/home/mbrock/nixpkgs/lib/systems/inspect.nix` (489 lines) - Platform predicates
- `/home/mbrock/nixpkgs/pkgs/stdenv/cross/default.nix` (139 lines) - Cross-compilation stdenv
- `/home/mbrock/nixpkgs/pkgs/top-level/stage.nix` (358 lines) - Package set construction (pkgsCross)

