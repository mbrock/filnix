# Fil-C + Nixpkgs Exploration - Complete Index

This directory contains a comprehensive analysis of how musl and static builds are integrated in nixpkgs, and how to integrate fil-c as an alternative libc/platform.

## Documents Overview

### 1. ARCHITECTURE-SUMMARY.md
**Purpose:** High-level overview and architecture guide
**Best for:** Understanding the big picture

**Key sections:**
- The nixpkgs platform system and how libc selection works
- Complete picture of musl integration (7 stages)
- How static builds work
- Three strategies for fil-c integration
- Key files and critical abstractions

**Read this first** to understand the overall approach.

---

### 2. NIXPKGS_INTEGRATION.md
**Purpose:** Detailed explanation of integration mechanisms
**Best for:** Deep understanding of each component

**Key sections:**
- ABI predicates and platform definitions
- Platform triple transformation (makeMuslParsedPlatform)
- Variant package set creation
- Libc selection routing
- Bootstrap integration
- Stdenv adapters pattern
- Cc-wrapper integration

**Reference this** when you need to understand how a specific part works.

---

### 3. IMPLEMENTATION_GUIDE.md
**Purpose:** Concrete file locations and code snippets
**Best for:** Implementing changes

**Key sections:**
- File-by-file reference with line numbers
- Current code examples
- Exact changes needed for fil-c
- Copy-paste ready code blocks

**Use this** when you're ready to make actual changes to nixpkgs or flake.nix.

---

## Quick Navigation

### I want to understand...

**How nixpkgs handles alternative libcs:**
1. Start with ARCHITECTURE-SUMMARY.md (section "How Musl Integration Works")
2. Deep dive: NIXPKGS_INTEGRATION.md (sections 1-6)
3. Reference: IMPLEMENTATION_GUIDE.md (Files 1-6)

**The complete data flow for package selection:**
1. ARCHITECTURE-SUMMARY.md (section "The Flow")
2. NIXPKGS_INTEGRATION.md (section "How Musl Is Integrated")

**What files need to change for fil-c:**
1. ARCHITECTURE-SUMMARY.md (section "For Fil-C: Minimum Viable Implementation")
2. IMPLEMENTATION_GUIDE.md (section "Summary of Changes Required")
3. IMPLEMENTATION_GUIDE.md (Files 1-5, each shows what to change)

**How to implement fil-c today:**
1. ARCHITECTURE-SUMMARY.md (section "Integration Strategies for Fil-C")
2. IMPLEMENTATION_GUIDE.md (File 10: "Current Flake.nix Approach")

**How static builds work:**
1. ARCHITECTURE-SUMMARY.md (section "How Static Builds Work")
2. IMPLEMENTATION_GUIDE.md (File 9)

---

## Key Concepts

### Platform Triple
```
cpu-vendor-os-abi
x86_64-unknown-linux-gnu
x86_64-unknown-linux-musl  <- Different ABI means different libc
```

### ABI Determines Libc
The ABI component (gnu, musl, filc) automatically determines which libc is used.

### Platform Transformation
`makeMuslParsedPlatform` transforms `gnu` ABI to `musl` ABI, causing all packages to rebuild with musl.

### nixpkgsFun
Calling `nixpkgsFun` with a different platform creates a new complete package set where all packages are re-evaluated.

### cc-wrapper
The integration point that connects:
- Compiler (gcc, clang, fil-c)
- Libc (glibc, musl, fil-c)  
- Bintools (linker)

---

## Current Status

### In filnix/flake.nix
Uses **Strategy B (Interim Approach)**:
- No nixpkgs source changes
- Replaces compiler with fil-c
- Reuses glibc headers/runtime
- Works for testing single packages

### Future: Path to Full Integration

1. **Short term:** Keep current flake.nix approach, test more packages
2. **Medium term:** Add fil-c overlay to flake.nix (Strategy C)
3. **Long term:** Contribute full variant support to nixpkgs (Strategy A)

---

## File Structure in Nixpkgs

```
nixpkgs/
  lib/systems/
    parse.nix          - ABI definitions
    inspect.nix        - Platform predicates
    default.nix        - Libc attribute auto-derivation
  
  pkgs/top-level/
    stage.nix          - makeMuslParsedPlatform, main orchestration
    variants.nix       - pkgsMusl, pkgsStatic variant definitions
    all-packages.nix   - Libc package selection
  
  pkgs/stdenv/
    linux/default.nix  - Bootstrap file selection, libc configuration
    adapters.nix       - Stdenv modification (makeStaticBinaries, etc.)
  
  pkgs/build-support/
    cc-wrapper/        - Compiler + libc integration
    bintools-wrapper/  - Linker configuration
```

---

## Critical Files to Know

### 1. lib/systems/default.nix (lines 120-159)
**What:** Libc attribute auto-derivation
**Why:** This is how `stdenv.hostPlatform.libc` gets set

### 2. pkgs/top-level/stage.nix (lines 90-116)
**What:** Platform transformer (makeMuslParsedPlatform)
**Why:** This is how platforms are transformed for variants

### 3. pkgs/top-level/variants.nix (lines 74-91)
**What:** Variant creation (pkgsMusl)
**Why:** This is the pattern to follow for pkgsFilC

### 4. pkgs/top-level/all-packages.nix (lines 7361-7400)
**What:** Libc package selection
**Why:** This is where "filc" gets routed to the filc package

### 5. pkgs/build-support/cc-wrapper/default.nix
**What:** Compiler wrapper integration
**Why:** This connects everything together

---

## Integration Strategies Comparison

| Aspect | Strategy A (Full) | Strategy B (Interim) | Strategy C (Hybrid) |
|--------|------------------|---------------------|-------------------|
| Effort | Medium | Minimal | Low-Medium |
| Complexity | Medium | Low | Low |
| Nixpkgs Changes | Yes (6+ files) | No | Minimal (overlays) |
| Bootstrap Files | Optional | No | No |
| Time to Use | Weeks | Now | Now |
| Maintainability | High | Low | Medium |
| Future-proof | Yes | No | Yes |
| Test Coverage | Complete | Package-specific | Package-specific |

**Current Recommendation:** Start with Strategy B (works now), move to Strategy C (cleaner), eventually to Strategy A (production-ready).

---

## Common Questions Answered

**Q: Can fil-c just be a compiler swap?**
A: Yes! Strategy B in flake.nix does this. Packages build with fil-c compiler but glibc headers/libs.

**Q: Do we need bootstrap files for fil-c?**
A: Optional. Only needed if you want pure fil-c bootstrapping (no glibc dependency). For testing, reuse existing bootstraps.

**Q: How does the libc attribute cascade?**
A: When you change `stdenv.hostPlatform.libc`, it affects all downstream packages because they all reference it.

**Q: Can pkgsFilC coexist with other variants?**
A: Yes! Like pkgsMusl, pkgsStatic, pkgsLLVM coexist. Each uses nixpkgsFun with different configurations.

**Q: What's the difference between cc-wrapper libc and the actual libc?**
A: cc-wrapper takes a libc package (headers + runtime). The platform determines which libc package is selected.

---

## Testing Checklist

For each new package with fil-c:
- [ ] Does it build?
- [ ] Are there any reference to glibc symbols?
- [ ] Does it link correctly against fil-c libc?
- [ ] Do the binaries work at runtime?
- [ ] Any fil-c specific alignment/memory safety issues?

---

## Useful Commands

```bash
# See what packages are in filpkgs
nix eval --json filnix#filpkgs.callPackage
nix flake show filnix

# Build a single package with fil-c
nix build filnix#filpkgs.nginx

# Enter a fil-c shell
nix develop filnix

# See a package's dependencies
nix flake show nixpkgs | grep nginx

# Check if a package exists
nix eval --json nixpkgs.nginx
```

---

## References

### Nixpkgs Documentation
- NixOS manual: https://nixos.org/manual/
- Nixpkgs source: https://github.com/NixOS/nixpkgs

### Related Integrations in Nixpkgs
- Musl libc: Used for pkgsMusl and pkgsStatic
- LLVM/Clang: Uses platform transformation similar to musl
- Cross-compilation: Uses similar platform system

### Fil-C References
- Fil-C repo: https://github.com/pizlonator/fil-c
- Current flake.nix: /home/mbrock/filnix/flake.nix

---

## Document Changelog

**2025-10-22:**
- Created comprehensive exploration documents
- 3 main documents + 1 index
- Complete coverage of musl integration
- Detailed fil-c integration strategies
- File-specific implementation guide

---

## For Contributors

If you're working on fil-c integration:

1. **For understanding:** Start with ARCHITECTURE-SUMMARY.md
2. **For implementation:** Reference IMPLEMENTATION_GUIDE.md
3. **For deep dives:** Use NIXPKGS_INTEGRATION.md
4. **For specific changes:** Cross-reference all three documents

All documents use absolute file paths to `/home/mbrock/nixpkgs/` for easy reference.

---

## Next Steps

1. Read ARCHITECTURE-SUMMARY.md (overview)
2. Review current flake.nix implementation
3. Run `nix build filpkgs#package-name` to test
4. Identify compatibility issues
5. Plan transition to Strategy C or A when ready

