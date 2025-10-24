# Fil-C + Nixpkgs: Architecture and Integration Guide

## Overview

This document summarizes how nixpkgs integrates alternative libcs (like musl) and provides a clear roadmap for integrating fil-c as either:
1. A full variant (`pkgsFilC`)
2. An interim solution using `replaceStdenv`

---

## The Nixpkgs Platform System

### Key Concept: Platform Triple Parsing

Every platform in nixpkgs is represented as a triple with three components:
```
cpu-vendor-os-abi
```

Example: `x86_64-unknown-linux-gnu`

The ABI component determines the libc:
- `gnu` -> glibc (default for linux)
- `musl` -> musl libc
- `musleabi`, `musleabihf` -> musl variants
- (future) `filc` -> fil-c libc

### The Flow: Triple -> ABI -> Libc Selection

```
Platform Triple (x86_64-unknown-linux-musl)
    |
    v
Parsed ABI (musl)
    |
    v
Platform Predicate (isMusl)
    |
    v
Libc Attribute (stdenv.hostPlatform.libc = "musl")
    |
    v
Libc Package Selection (libc = musl package)
    |
    v
Compiler Wrapper Configuration (cc-wrapper with musl headers/libs)
    |
    v
All packages rebuilt with this libc
```

---

## How Musl Integration Works (Complete Picture)

### 1. ABI Definition (Systems Library)

**Files:**
- `lib/systems/parse.nix` - Define ABI types
- `lib/systems/inspect.nix` - Define predicates (isMusl, etc.)

**What happens:**
- Musl ABIs are registered: `musl`, `musleabi`, `musleabihf`, etc.
- Predicates recognize these ABIs in platform triples

### 2. Libc Attribute Auto-Derivation

**File:** `lib/systems/default.nix`

```nix
libc =
  if final.isMusl then "musl"
  else if final.isLinux then "glibc"
  # ... other cases ...
```

**What happens:**
- The platform's libc attribute is set based on its ABI predicate
- This is the KEY attribute that drives downstream decisions

### 3. Platform Transformation

**File:** `pkgs/top-level/stage.nix`

```nix
makeMuslParsedPlatform = parsed:
  parsed // {
    abi = {
      gnu = lib.systems.parse.abis.musl;
      # ... map glibc ABIs to musl ABIs ...
    }.${parsed.abi.name} or lib.systems.parse.abis.musl;
  };
```

**What happens:**
- When creating `pkgsMusl`, the platform's ABI is transformed
- `x86_64-unknown-linux-gnu` becomes `x86_64-unknown-linux-musl`
- This causes the libc attribute to become "musl"

### 4. Variant Package Set Creation

**File:** `pkgs/top-level/variants.nix`

```nix
pkgsMusl = nixpkgsFun {
  overlays = [(self': super': { pkgsMusl = super'; })] ++ overlays;
  localSystem = {
    config = lib.systems.parse.tripleFromSystem (
      makeMuslParsedPlatform stdenv.hostPlatform.parsed
    );
  };
};
```

**What happens:**
- Calls `nixpkgsFun` (the entire package set constructor)
- Passes a transformed platform triple
- All packages are re-evaluated with the new platform

### 5. Libc Package Selection

**File:** `pkgs/top-level/all-packages.nix`

```nix
libc = 
  let inherit (stdenv.hostPlatform) libc;
  in if libc == "musl" then musl
     else if libc == "glibc" then glibc
     # ...
```

**What happens:**
- The `libc` package attribute is set based on `stdenv.hostPlatform.libc`
- For musl platforms, this evaluates to the musl package

### 6. Compiler Wrapper Configuration

**File:** `pkgs/build-support/cc-wrapper/default.nix`

The cc-wrapper receives:
- `cc` - the compiler (gcc, clang, etc.)
- `libc` - the libc package with headers and runtime
- `bintools` - linker and binutils

**What happens:**
- Compiler flags are set to point to libc headers
- Linker flags are set to point to libc runtime
- For musl: uses musl's headers and dynamic linker

### 7. Bootstrap Files (Optional)

**File:** `pkgs/stdenv/linux/default.nix`

```nix
bootstrapFiles ?
  let table = {
    glibc = { x86_64-linux = import ./bootstrap-files/...; };
    musl = { x86_64-linux = import ./bootstrap-files/...; };
  };
```

**What happens:**
- Different pre-built bootstrap tools are selected per-libc
- For pure bootstrapping without binary artifacts

---

## How Static Builds Work

**File:** `pkgs/top-level/stage.nix` (lines 310-331)

```nix
pkgsStatic = nixpkgsFun {
  # Uses musl for Linux (static glibc is problematic)
  crossSystem = {
    isStatic = true;  # <-- KEY FLAG
    config = lib.systems.parse.tripleFromSystem (
      makeMuslParsedPlatform stdenv.hostPlatform.parsed
    );
  };
};
```

**Pattern:**
- Combines platform transformation (to musl) with `isStatic` flag
- The `isStatic` flag triggers different build behavior in packages
- All packages are rebuilt as static

---

## Integration Strategies for Fil-C

### Strategy A: Full Integration (pkgsFilC)

**Effort:** Moderate | **Complexity:** Medium | **Scope:** Complete variant

Steps:
1. Add fil-c ABI to systems library
2. Create `makeFilCParsedPlatform` function
3. Add `pkgsFilC` variant definition
4. Route "filc" libc package selection
5. Create bootstrap files (optional)

**Advantages:**
- Systematic like musl
- Can create variants like `pkgsStaticFilC`
- Proper separation of concerns
- Future-proof

**Disadvantages:**
- Requires nixpkgs changes
- Need bootstrap files
- More complex setup

**Result:** `pkgs.pkgsFilC.package` works like `pkgs.pkgsMusl.package`

---

### Strategy B: Interim Approach (Current flake.nix)

**Effort:** Minimal | **Complexity:** Low | **Scope:** Compiler-only swap

```nix
filpkgs = import nixpkgs {
  config.replaceStdenv = { pkgs, ... }:
    pkgs.overrideCC pkgs.stdenv filc-compat;
};
```

**Advantages:**
- No nixpkgs source changes
- Works immediately
- Good for testing
- Can scale with overlays

**Disadvantages:**
- Uses glibc platform/headers
- Not as clean as full variant
- Limited to compiler differences

**Result:** Packages built with fil-c but glibc platform

---

### Strategy C: Hybrid (Recommended for Now)

Use Strategy B for testing/development, but structure flake.nix to eventually transition to Strategy A.

```nix
# flake.nix
filpkgs = import nixpkgs {
  overlays = [filc-overlay];
  config.replaceStdenv = { pkgs, ... }:
    pkgs.overrideCC pkgs.stdenv filc-compat;
};

# Later: move filc-overlay to nixpkgs/pkgs/top-level/variants.nix
filc-overlay = self: super: {
  # fil-c specific configuration
};
```

---

## Key Files to Understand

### Systems Library (lib/systems/)
- **parse.nix** - ABI definitions and parsing
- **inspect.nix** - Platform predicates
- **default.nix** - Auto-derivation of platform attributes

### Package Set Construction (pkgs/top-level/)
- **stage.nix** - Platform transformers, main orchestration
- **variants.nix** - Variant definitions (pkgsMusl, pkgsStatic, etc.)
- **all-packages.nix** - Libc package routing

### Build Infrastructure (pkgs/stdenv/)
- **linux/default.nix** - Linux stdenv and bootstrap
- **adapters.nix** - Stdenv modification functions
- **build-support/cc-wrapper/** - Compiler/libc integration

---

## Critical Abstractions

### nixpkgsFun
The main function that creates a package set. Takes:
- `localSystem` / `crossSystem` - platform configuration
- `overlays` - package overrides
- `config` - feature flags

Calling `nixpkgsFun` with a transformed platform creates a new package set where ALL packages are re-evaluated against the new platform.

### Platform Transformer
A function like `makeMuslParsedPlatform` that:
- Takes a parsed platform
- Transforms the ABI component
- Returns a modified platform

When the ABI changes, `stdenv.hostPlatform.libc` changes, which cascades through all packages.

### cc-wrapper
The integration point where:
- Compiler toolchain (gcc, clang) is wrapped
- Libc package is connected
- Bintools/linker is configured
- All build flags are set up

---

## Data Flow for Package Selection

When you request `pkgsMusl.nginx`:

```
1. nixpkgsFun called with makeMuslParsedPlatform
2. stdenv.hostPlatform is set to musl triple
3. stdenv.hostPlatform.libc = "musl" (auto-derived)
4. all-packages.nix evaluates: libc = musl (package)
5. cc-wrapper configured with musl headers/libs
6. nginx is built using musl instead of glibc
7. nginx binary linked against musl runtime
```

---

## For Fil-C: Minimum Viable Implementation

### To test packages with fil-c immediately:

File: `flake.nix`
```nix
filpkgs = import nixpkgs {
  config.replaceStdenv = { pkgs, ... }:
    pkgs.overrideCC pkgs.stdenv filc-compat;
};
```

Then: `nix build filpkgs#nginx`

### To create full `pkgsFilC` variant:

1. Add to `lib/systems/parse.nix`: filc ABI types
2. Add to `lib/systems/inspect.nix`: isFilC predicate  
3. Add to `pkgs/top-level/stage.nix`: `makeFilCParsedPlatform`
4. Add to `pkgs/top-level/variants.nix`: `pkgsFilC` definition
5. Add to `pkgs/top-level/all-packages.nix`: filc case in libc selection

Then: `nix build (import nixpkgs {}).pkgsFilC.nginx`

---

## Common Pitfalls

### Pitfall 1: Forgetting that platforms cascade
Changing the platform affects EVERY package downstream. Test carefully.

### Pitfall 2: Not understanding nixpkgsFun
Creating a new variant requires understanding that `nixpkgsFun` re-evaluates the entire package set.

### Pitfall 3: Confusing cc (compiler) with libc
- The compiler is the tool (gcc, clang, fil-c)
- The libc is the runtime library (glibc, musl, fil-c)
- Both are needed for proper compilation

### Pitfall 4: Bootstrap vs. final libc
- Bootstrap files are pre-built for bootstrapping the stdenv
- Final libc is built/selected for the final package set
- They don't have to match (musl can bootstrap from glibc)

---

## Testing Strategy

### Phase 1: Test single packages
```bash
nix build filpkgs#package-name
```

### Phase 2: Test building nixpkgs itself
```nix
# filnix/flake.nix
filpkgs-dev = filpkgs.stdenv.mkDerivation {
  # ... build configuration for nixpkgs ...
};
```

### Phase 3: Test pure bootstrap
- Create bootstrap files for fil-c
- Use full variant approach
- Verify no glibc references

---

## References

Key files in nixpkgs:
- `/home/mbrock/nixpkgs/lib/systems/` - Platform definitions
- `/home/mbrock/nixpkgs/pkgs/top-level/` - Package set construction
- `/home/mbrock/nixpkgs/pkgs/stdenv/` - Stdenv and bootstrap
- `/home/mbrock/filnix/flake.nix` - Current fil-c integration

Additional docs:
- `NIXPKGS_INTEGRATION.md` - Detailed integration explanation
- `IMPLEMENTATION_GUIDE.md` - Specific file locations and code examples

---

## Next Steps

1. Understand the current flake.nix approach (Strategy B)
2. Test single packages with `nix build filpkgs#package`
3. Identify any missing dependencies or compatibility issues
4. Gradually move toward Strategy C (hybrid with overlays)
5. When ready, contribute full variant patches to nixpkgs (Strategy A)

