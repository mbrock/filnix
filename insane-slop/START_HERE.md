# Fil-C + Nixpkgs Integration: START HERE

This is your guide to understanding how to integrate fil-c as an alternative libc in nixpkgs.

## TL;DR

Nixpkgs integrates alternative libcs (like musl) by:
1. Defining ABI types
2. Creating platform predicates
3. Transforming platform triples (gnu -> musl)
4. Calling `nixpkgsFun` to rebuild all packages with the new platform
5. Routing libc selection based on the platform

Fil-c can follow the same pattern. The current implementation uses a simpler interim approach that works today.

---

## 5-Minute Overview

### The Flow
```
Triple (x86_64-unknown-linux-gnu)
  -> ABI (gnu) 
    -> Predicate (isMusl) 
      -> Libc Attribute (musl)
        -> Package Selection (musl package)
          -> All Packages Rebuild
```

### Key Files to Know
1. `lib/systems/default.nix` - Sets `stdenv.hostPlatform.libc` attribute
2. `pkgs/top-level/stage.nix` - Has `makeMuslParsedPlatform` function
3. `pkgs/top-level/variants.nix` - Defines `pkgsMusl` variant
4. `pkgs/top-level/all-packages.nix` - Routes libc packages
5. `pkgs/build-support/cc-wrapper/` - Connects compiler + libc

### For Fil-C Today
```nix
filpkgs = import nixpkgs {
  config.replaceStdenv = { pkgs, ... }:
    pkgs.overrideCC pkgs.stdenv filc-compat;
};
```

This swaps the compiler without changing the platform.

---

## Document Guide

### Start With These (In Order)

1. **RESEARCH_SUMMARY.md** (This is your elevator pitch)
   - 5 key findings
   - 7-stage integration process
   - 3 integration strategies
   - Recommendations

2. **ARCHITECTURE-SUMMARY.md** (Your first deep dive)
   - Platform system explained
   - Complete musl integration walkthrough
   - How static builds work
   - Integration strategies compared

3. **IMPLEMENTATION_GUIDE.md** (When you need to code)
   - File-by-file reference
   - Actual code examples
   - Line numbers
   - Copy-paste ready

### Reference These As Needed

- **NIXPKGS_INTEGRATION.md** - Detailed technical explanations
- **EXPLORATION_INDEX.md** - Navigation and quick reference
- **NIX_WRAPPER_ANALYSIS.md** - Cc-wrapper deep dive (if needed)

### Existing Documentation

- **QUICK-REFERENCE.md** - Cheat sheet
- **INTEGRATION-STRATEGY.md** - Detailed strategy comparison
- **ARCHITECTURE_DIAGRAM.md** - Visual diagrams
- **WRAPPER_PLAN_SUMMARY.md** - Wrapper implementation notes
- **NIXPKGS-CROSS-COMPILATION-GUIDE.md** - Cross-compilation details

---

## Reading Paths

### Path 1: "I need to understand this fast" (15 minutes)
1. This document (you are here)
2. RESEARCH_SUMMARY.md
3. EXPLORATION_INDEX.md section "Key Concepts"

### Path 2: "I want to understand it properly" (1 hour)
1. ARCHITECTURE-SUMMARY.md
2. RESEARCH_SUMMARY.md
3. EXPLORATION_INDEX.md

### Path 3: "I'm going to implement changes" (2 hours)
1. ARCHITECTURE-SUMMARY.md
2. IMPLEMENTATION_GUIDE.md (all files)
3. NIXPKGS_INTEGRATION.md (for context)

### Path 4: "I want to know everything" (4+ hours)
1. All documents in order
2. Cross-reference code in nixpkgs
3. Trace through specific examples

---

## Quick Facts

**Current Status:**
- Fil-c is built from source
- Works for individual packages
- Uses glibc headers/runtime
- No nixpkgs source changes needed

**To Scale Up:**
- Create fil-c overlay (Strategy C)
- Or integrate into nixpkgs (Strategy A)

**Files Modified:**
- Current: 0 (uses flake.nix)
- Strategy A: 6-9 (adds nixpkgs support)

**Bootstrap Approach:**
- Current: None needed
- Full: Optional (accelerates builds)

---

## Key Concepts (Minimal Explanation)

### Platform Triple
The way nixpkgs identifies a system:
```
cpu-vendor-os-abi
x86_64-unknown-linux-gnu
x86_64-unknown-linux-musl  <- Different ABI
```

**Why it matters:** The ABI determines which libc is used.

### Variant
A complete package set with a modified platform:
- `pkgsMusl` - All packages built with musl libc
- `pkgsStatic` - All packages built statically
- (future) `pkgsFilC` - All packages built with fil-c

**How it works:** Uses `nixpkgsFun` with a transformed platform.

### cc-wrapper
Connects three things together:
- Compiler (gcc, clang, fil-c)
- Libc (glibc, musl, fil-c)
- Bintools (linker, binutils)

**Why it matters:** This is where the magic happens.

---

## The Three Strategies

### Strategy A: Full (Production)
- Modify nixpkgs with 6+ files
- Create dedicated ABI for fil-c
- Supports variants like `pkgsStaticFilC`
- 2-4 weeks to implement
- Result: `pkgs.pkgsFilC.nginx` works seamlessly

### Strategy B: Interim (Now)
- No nixpkgs changes
- Compiler swap only
- Works immediately
- Limited to compiler differences
- Result: Packages build with fil-c but use glibc platform

### Strategy C: Hybrid (Recommended)
- Start with Strategy B
- Add fil-c overlay to flake.nix
- Prepare for Strategy A
- Good incremental path
- Result: Clean, extensible, future-proof

**Current Implementation:** Strategy B

---

## Common Questions

**Q: Can I test fil-c right now?**
A: Yes! `nix build filnix#filpkgs.nginx` or any package.

**Q: Do I need to modify nixpkgs?**
A: Not required for Strategy B or C. Only for Strategy A.

**Q: How long until full integration?**
A: Strategy A is 2-4 weeks once the core fil-c libc package is solid.

**Q: Will fil-c variant coexist with musl?**
A: Yes, like pkgsMusl, pkgsStatic, pkgsLLVM all coexist.

**Q: Is this approach stable?**
A: Yes, it's how musl/static/llvm work in nixpkgs.

---

## What To Do Next

### Immediate (Today)
1. Read RESEARCH_SUMMARY.md
2. Run `nix build filnix#filpkgs.gawk` to verify it works
3. Pick a package to test: `nix build filnix#filpkgs.nginx`

### Short Term (This Week)
1. Read ARCHITECTURE-SUMMARY.md
2. Test 5-10 packages
3. Document any build failures
4. Identify missing dependencies

### Medium Term (Next Weeks)
1. Read IMPLEMENTATION_GUIDE.md
2. Start with Strategy C (create overlay)
3. Systematize package definitions
4. Build test suite

### Long Term (Later)
1. Decide: Stay with C or move to A?
2. Contribute patches to nixpkgs (if choosing A)
3. Maintain fil-c integration

---

## File Locations (Quick Reference)

**Key Nixpkgs Files:**
```
/home/mbrock/nixpkgs/
  lib/systems/
    parse.nix              <- ABI definitions
    inspect.nix            <- Predicates
    default.nix            <- Libc auto-derive
  pkgs/top-level/
    stage.nix              <- Transformers
    variants.nix           <- Variants
    all-packages.nix       <- Package selection
  pkgs/stdenv/
    linux/default.nix      <- Bootstrap
  pkgs/build-support/
    cc-wrapper/            <- Compiler integration
```

**Fil-C Implementation:**
```
/home/mbrock/filnix/
  flake.nix                <- Current approach
  /documentation/          <- All guides (you are here)
```

---

## Success Criteria

You understand this when you can:
- [ ] Explain what ABI means and why it matters
- [ ] Draw the platform -> libc flow
- [ ] Explain nixpkgsFun's role
- [ ] Compare the three strategies
- [ ] Know which files need changes for each strategy
- [ ] Build a package with fil-c
- [ ] Identify what needs to change for full integration

---

## Getting Help

If you're stuck:
1. Check EXPLORATION_INDEX.md for navigation
2. Search IMPLEMENTATION_GUIDE.md for specific files
3. Look at ARCHITECTURE-SUMMARY.md for concept explanations
4. Reference the actual nixpkgs files using absolute paths

All documents include file paths and line numbers for easy lookup.

---

## Document Map

```
START_HERE.md (this)
  |
  +- RESEARCH_SUMMARY.md (key findings + recommendations)
  |
  +- ARCHITECTURE-SUMMARY.md (complete architecture)
  |    |
  |    +- IMPLEMENTATION_GUIDE.md (file-by-file reference)
  |    |
  |    +- NIXPKGS_INTEGRATION.md (detailed explanations)
  |
  +- EXPLORATION_INDEX.md (navigation guide)
  |
  +- [Other docs for specific topics]
```

---

## Final Thoughts

Nixpkgs integration of alternative libcs is **elegant and systematic**. The patterns are **clean and reusable**. Fil-c can follow the same approach.

You have two immediate options:
1. **Keep using Strategy B** - Works now, good for testing
2. **Move to Strategy C** - Clean, extensible, future-proof

Either way, the documentation shows exactly how to proceed.

**Ready to begin? Start with RESEARCH_SUMMARY.md next.**

