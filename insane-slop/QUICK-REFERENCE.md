# Fil-C as Pseudo-Cross Target: Quick Reference

## The Core Concept

Fil-C can be treated as an ABI-incompatible target using nixpkgs' cross-compilation infrastructure, even on the same x86_64-linux architecture. This leverages the fact that:

1. **Different ABI = Different binary interface** (fil-c vs glibc)
2. **Different libc = Different stdenv selection** (triggers `stagesCross`)
3. **Cross-compilation stdenv = Automatic hook application** (fixes configure scripts)

## System String Pattern

### Recommended: Custom ABI

```
x86_64-unknown-linux-filc
├── CPU: x86_64
├── Vendor: unknown
├── Kernel: linux
└── ABI: filc  ← This is the key difference
```

Parsed as:
```nix
{
  cpu.name = "x86_64",
  vendor.name = "unknown", 
  kernel.name = "linux",
  abi.name = "filc"
}
```

## The 5 Minimal Patches for Nixpkgs

### 1. Register ABI in `lib/systems/parse.nix` (line ~750)

```nix
abis = setTypes types.openAbi {
  # ... existing entries ...
  filc = {
    assertions = [{
      assertion = platform: platform.isLinux && platform.isx86_64;
      message = "Fil-C ABI only available on x86_64-linux";
    }];
  };
};
```

### 2. Add Libc Detection in `lib/systems/default.nix` (line ~140)

```nix
libc =
  if final.isDarwin then "libSystem"
  else if final.parsed.abi.name == "filc" then "filc"
  else if final.isLinux then "glibc"
  # ... rest of cases ...
```

### 3. Add Predicate in `lib/systems/inspect.nix` (line ~430)

```nix
patterns = rec {
  # ... existing ...
  isFilC = { abi = abis.filc; };
};
```

### 4. Add Example in `lib/systems/examples.nix` (line ~444)

```nix
filc-x86_64 = {
  config = "x86_64-unknown-linux-filc";
};
filc = filc-x86_64;
```

### 5. Add Compiler Selection in `pkgs/stdenv/cross/default.nix` (line ~107)

```nix
cc =
  if crossSystem.isFilC then
    buildPackages.filc-wrapped
  else if crossSystem.isDarwin then
    buildPackages.llvmPackages.systemLibcxxClang
  # ... rest ...
```

## How It Works

### Triggering Cross-Compilation

```nix
# In pkgs/stdenv/default.nix (line 44)
if crossSystem != localSystem || crossOverlays != [ ] then
  stagesCross
```

For fil-c, this triggers because:

```nix
localSystem = { config = "x86_64-unknown-linux-gnu"; libc = "glibc"; }
crossSystem = { config = "x86_64-unknown-linux-filc"; libc = "filc"; }
# → crossSystem != localSystem → uses stagesCross
```

### What Cross-Compilation Stdenv Does

1. **Separates build vs. host** (lines 54-88 of cross/default.nix)
   - Build tools run on native glibc
   - Target libraries run on fil-c

2. **Applies autotools hooks** (lines 72-86)
   - Automatically fixes configure scripts
   - Makes packages adapt to "different" platform

3. **Selects correct compiler** (lines 106-128)
   - Uses `buildPackages.filc-wrapped` for cross-compilation
   - Not used when building native tools

## Integration Levels

| Aspect | Level 1 (Current) | Level 2 (Enhanced) | Level 3 (Full) |
|--------|-------------------|-------------------|----------------|
| **Location** | filnix only | filnix overlay | nixpkgs core |
| **ABI registered** | No | filnix | parse.nix |
| **Libc detection** | Manual | Overlay | default.nix |
| **pkgsCross.filc** | Manual | Manual | Automatic |
| **Effort** | Low | Medium | High |

## Current Filnix Approach (Level 1)

```nix
# flake.nix: Custom stdenv override
filpkgs = import nixpkgs {
  inherit system;
  config.replaceStdenv = { pkgs, ... }:
    pkgs.overrideCC pkgs.stdenv filc-compat;
};

# Works! But doesn't use cross-compilation machinery
# Missing: automatic hook application, compiler detection, etc.
```

## Enhanced Approach (Level 2)

```nix
# flake.nix: Use overlays to extend lib.systems

filc-overlay = final: prev: {
  lib = prev.lib // {
    systems = prev.lib.systems // {
      examples = prev.lib.systems.examples // {
        filc-x86_64 = {
          config = "x86_64-unknown-linux-filc";
          libc = "filc";
        };
        filc = final.lib.systems.examples.filc-x86_64;
      };
    };
  };
};

filpkgs-cross = import nixpkgs {
  inherit system;
  crossSystem = "x86_64-unknown-linux-filc";
  overlays = [filc-overlay];
};

# Now: pkgsCross.filc.hello works!
# Automatically uses cross-compilation stdenv
```

## Full Integration (Level 3)

Apply all 5 patches to nixpkgs, then:

```nix
filpkgs = import nixpkgs {
  inherit system;
  crossSystem = "x86_64-unknown-linux-filc";
};

# pkgsCross.filc.hello automatically available
# Cross-compilation stdenv automatically applied
# All hooks automatically integrated
```

## Key Files to Understand

1. **lib/systems/default.nix** (620 lines)
   - elaborate() function
   - Where libc is computed
   - Why libc != buildPlatform.libc triggers cross mode

2. **lib/systems/parse.nix** (970 lines)
   - ABI definition
   - System string parsing
   - CPU/kernel/vendor/abi registry

3. **pkgs/stdenv/cross/default.nix** (139 lines)
   - Cross-compilation triggering (line 44)
   - Compiler selection (lines 106-128)
   - Hook application (lines 69-86)

4. **pkgs/top-level/stage.nix** (358 lines)
   - pkgsCross construction (line 238)
   - How examples become package sets

## Critical Insights

1. **libc is the key trigger**
   - libc = "filc" vs libc = "glibc" → Different elaboration
   - Different elaboration → crossSystem != localSystem
   - → Uses stagesCross with all its machinery

2. **ABI is semantic, not syntactic**
   - ABI (Application Binary Interface) = how code links/executes
   - Fil-C is ABI-incompatible with glibc
   - This justifies treating it as cross-compilation target

3. **Hooks are automatic**
   - updateAutotoolsGnuConfigScriptsHook applied automatically
   - configure scripts adapted without manual intervention
   - Makes packages "just work" with fil-c

4. **Store paths differentiate**
   - `/nix/store/HASH-hello-x86_64-unknown-linux-filc/`
   - `/nix/store/HASH2-hello-x86_64-unknown-linux-gnu/`
   - Different paths = correct segregation

## Quick Checklist

- [ ] Understand libc != buildPlatform.libc triggers cross-compilation
- [ ] Recognize ABI as the semantic distinction (not just architecture)
- [ ] See how lib.systems.* provides infrastructure
- [ ] Understand that different system strings avoid collisions
- [ ] Know that updateAutotoolsGnuConfigScriptsHook is automatic
- [ ] Appreciate that pkgsCross automatically extends to new targets

## References

Full documentation:
- **NIXPKGS-CROSS-COMPILATION-GUIDE.md** - Detailed technical guide (22 KB)
- **INTEGRATION-STRATEGY.md** - Implementation checklist (11 KB)

Source files analyzed:
- /home/mbrock/nixpkgs/lib/systems/default.nix
- /home/mbrock/nixpkgs/lib/systems/parse.nix
- /home/mbrock/nixpkgs/lib/systems/examples.nix
- /home/mbrock/nixpkgs/lib/systems/inspect.nix
- /home/mbrock/nixpkgs/pkgs/stdenv/cross/default.nix
- /home/mbrock/nixpkgs/pkgs/top-level/stage.nix

Current implementation:
- /home/mbrock/filnix/flake.nix
