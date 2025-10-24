================================================================================
                    FIL-C CROSS-COMPILATION INTEGRATION
                         Implementation Summary
================================================================================

THOROUGHLY EXPLORED NIXPKGS INFRASTRUCTURE:

1. PLATFORM DEFINITION & PARSING
   File: /home/mbrock/nixpkgs/lib/systems/parse.nix (970 lines)
   - System triple/quadruple parsing (lines 776-875)
   - CPU type definitions (lines 121-400)
   - ABI definitions registry (lines 649-748)
   - Kernel and vendor definitions
   
   KEY INSIGHT: ABIs are designed to distinguish binary interfaces exactly
   like needed for fil-c. Pattern matches existing ABIs: musl, uclibc, bionic.

2. PLATFORM ELABORATION
   File: /home/mbrock/nixpkgs/lib/systems/default.nix (620 lines)
   - elaborate() function (lines 71-620)
   - libc detection logic (lines 120-159)
   - Computed platform attributes
   - Predicate generation
   
   KEY INSIGHT: libc != buildPlatform.libc triggers cross-compilation mode.
   This is how Fil-C becomes a "pseudo-cross target" despite same architecture.

3. PLATFORM EXAMPLES
   File: /home/mbrock/nixpkgs/lib/systems/examples.nix (444 lines)
   - Example system definitions (lines 8-444)
   - Pattern: config triple + optional attributes
   
   PATTERN FOR FIL-C:
   filc-x86_64 = {
     config = "x86_64-unknown-linux-filc";
     libc = "filc";  # CRITICAL: Different from "glibc"
   };

4. CROSS-COMPILATION INFRASTRUCTURE
   File: /home/mbrock/nixpkgs/pkgs/stdenv/cross/default.nix (139 lines)
   - Triggered when: crossSystem != localSystem (line 44)
   - stdenvNoCC creation (lines 54-88)
   - Compiler selection (lines 106-128)
   - Hook application (lines 69-86)
   
   KEY INSIGHT: Automatically applies updateAutotoolsGnuConfigScriptsHook
   and other cross-compilation machinery when platforms differ.

5. PACKAGE SET CONSTRUCTION
   File: /home/mbrock/nixpkgs/pkgs/top-level/stage.nix (358 lines)
   - pkgsCross construction (line 238)
   - Maps lib.systems.examples to package sets
   
   PATTERN: pkgsCross.filc.hello automatically builds hello with Fil-C
   if filc target is registered in lib.systems.examples

6. PLATFORM INSPECTION PREDICATES
   File: /home/mbrock/nixpkgs/lib/systems/inspect.nix (489 lines)
   - Pattern matching infrastructure (lines 30-440)
   - Predicate generation for platforms
   
   PATTERN: isFilC pattern can match on libc or abi name

================================================================================
                           RECOMMENDED APPROACH
================================================================================

IMPLEMENTATION STRATEGY: Create Fil-C as ABI-based cross target

1. DEFINE FIL-C ABI IN PARSE.NIX
   Location: /home/mbrock/nixpkgs/lib/systems/parse.nix (after line 748)
   
   abis = setTypes types.openAbi {
     # ... existing entries ...
     filc = {
       assertions = [{
         assertion = platform: platform.isLinux && platform.isx86_64;
         message = "Fil-C ABI only available on x86_64-linux";
       }];
     };
   };

2. ADD LIBC DETECTION IN DEFAULT.NIX
   Location: /home/mbrock/nixpkgs/lib/systems/default.nix (line ~140)
   
   Insert before existing cases:
   else if final.parsed.abi.name == "filc" then "filc"

3. ADD INSPECT PREDICATE IN INSPECT.NIX
   Location: /home/mbrock/nixpkgs/lib/systems/inspect.nix (line ~430)
   
   patterns = rec {
     # ... existing patterns ...
     isFilC = { abi = abis.filc; };
   };

4. ADD EXAMPLE IN EXAMPLES.NIX
   Location: /home/mbrock/nixpkgs/lib/systems/examples.nix (line ~444)
   
   rec {
     # ... existing ...
     filc-x86_64 = {
       config = "x86_64-unknown-linux-filc";
     };
     filc = filc-x86_64;
   }

5. ADD COMPILER SELECTION IN CROSS/DEFAULT.NIX
   Location: /home/mbrock/nixpkgs/pkgs/stdenv/cross/default.nix (line ~107)
   
   cc =
     if crossSystem.isFilC then
       buildPackages.filc-wrapped
     else if crossSystem.isDarwin then
       buildPackages.llvmPackages.systemLibcxxClang
     # ... rest ...

================================================================================
                           PRACTICAL PATTERNS
================================================================================

SYSTEM STRING PATTERNS:

Method 1 - Custom ABI (RECOMMENDED):
  Triple: x86_64-unknown-linux-filc
  Parsed: { cpu=x86_64, vendor=unknown, kernel=linux, abi=filc }
  Benefits: Clear ABI semantics, matches existing patterns
  Implementation: Requires parse.nix changes ONCE

Method 2 - Pseudo-vendor:
  Triple: x86_64-filc-linux-gnu
  Parsed: { cpu=x86_64, vendor=filc, kernel=linux, abi=gnu }
  Benefits: No parse.nix changes
  Drawbacks: Vendor not standard interpretation

CROSS-COMPILATION TRIGGERING:

The key mechanism in pkgs/stdenv/default.nix line 44:

if crossSystem != localSystem || crossOverlays != [ ] then
  stagesCross

This works by:
1. Setting different config triple strings
   OR
2. Setting different libc values on same system

Example for Fil-C (Method A - config triple):
  localSystem = { config = "x86_64-unknown-linux-gnu"; }
  crossSystem = { config = "x86_64-unknown-linux-filc"; }
  Result: crossSystem != localSystem → triggers stagesCross

Example for Fil-C (Method B - libc marker):
  localSystem = { system = "x86_64-linux"; libc = "glibc"; }
  crossSystem = { system = "x86_64-linux"; libc = "filc"; }
  Result: Different elaboration → triggers cross-compilation mode

================================================================================
                         KEY CODE LOCATIONS
================================================================================

File Analysis Summary:

1. lib/systems/default.nix
   - Lines 71-620: elaborate() function
   - Lines 120-159: libc inference
   - Lines 86-120: canExecute logic
   
   What happens: Takes { system, config, libc, ... } and produces full
   platform definition with all computed attributes

2. lib/systems/parse.nix
   - Lines 649-748: ABI definitions
   - Lines 121-400: CPU type definitions  
   - Lines 776-875: System string parsing
   - Lines 934: mkSystemFromString() entry point
   
   What happens: Parses "x86_64-unknown-linux-filc" into structured data

3. lib/systems/examples.nix
   - Lines 1-444: Platform definitions for pkgsCross
   - Line 238: pkgsCross construction pattern
   
   What happens: Associates system definitions with names like
   pkgsCross.filc.nginx → builds nginx with Fil-C

4. pkgs/stdenv/cross/default.nix
   - Lines 44-50: Cross-compilation triggering
   - Lines 54-88: stdenvNoCC construction
   - Lines 106-128: Compiler selection
   
   What happens: When crossSystem != localSystem, uses special
   cross-compilation environment with extra hooks

5. pkgs/top-level/stage.nix
   - Line 238: pkgsCross = lib.mapAttrs(...lib.systems.examples...)
   - Lines 232-332: otherPackageSets definition
   
   What happens: Maps each entry in examples to a complete pkgs set

================================================================================
                     INTEGRATION COMPLEXITY LEVELS
================================================================================

LEVEL 1: CURRENT APPROACH (Already Working)
  - Custom stdenv override in flake.nix
  - Manual withFilC() helper function
  - No infrastructure changes needed
  - Files: Only filnix/flake.nix
  
LEVEL 2: ENHANCED APPROACH (Recommended)
  - Create overlay adding fil-c example to lib.systems.examples
  - Define via overlay, not core nixpkgs
  - Gets pkgsCross.filc for free
  - Files: filnix/flake.nix (enlarged overlay)
  
LEVEL 3: FULL INTEGRATION (Upstream)
  - Patch nixpkgs with all 5 changes above
  - Register fil-c ABI and libc permanently
  - Upstream-able patches
  - Files: 5 nixpkgs files modified, testable standalone

================================================================================
                           CRITICAL INSIGHTS
================================================================================

1. CROSS-COMPILATION DETECTION
   The system is triggered by: crossSystem != localSystem
   This comparison uses the full elaborate() result, not just config string.
   Key difference that triggers: libc attribute
   
   Pattern: libc = "glibc" vs libc = "filc" → Different elaboration

2. ABI vs LIBC DISTINCTION
   - ABI (Application Binary Interface): How code is linked/called
   - libc (C library): Runtime library implementation
   
   Fil-C is an ABI-incompatible way to run code on same CPU
   Different ABI → Different libc → Triggers cross-compilation mode

3. WHY LIBC MATTERS FOR CROSS-COMPILATION
   Lines 44-50 of pkgs/stdenv/default.nix show stdenv selection:
   - If crossSystem != localSystem: use stagesCross
   - stagesCross (cross/default.nix) handles ABI incompatibilities
   - Applies updateAutotoolsGnuConfigScriptsHook automatically
   - Selects correct compiler, linker, headers
   
4. HOOK APPLICATION IS AUTOMATIC
   When cross-compilation is triggered, hooks like
   updateAutotoolsGnuConfigScriptsHook are applied (line 72-86)
   This fixes configure scripts to handle the different platform

5. PACKAGE CACHE IMPLICATIONS
   Once registered with config string "x86_64-unknown-linux-filc",
   all packages get DIFFERENT store paths:
   - /nix/store/HASH-hello-x86_64-unknown-linux-filc/
   vs
   - /nix/store/HASH2-hello-x86_64-unknown-linux-gnu/
   
   This is correct: they're different binaries with different guarantees

================================================================================
                        FILES TO REFERENCE
================================================================================

Analyzed and documented source files (readable, not modified):

/home/mbrock/nixpkgs/lib/systems/default.nix
/home/mbrock/nixpkgs/lib/systems/parse.nix
/home/mbrock/nixpkgs/lib/systems/examples.nix
/home/mbrock/nixpkgs/lib/systems/inspect.nix
/home/mbrock/nixpkgs/lib/systems/architectures.nix
/home/mbrock/nixpkgs/lib/systems/doubles.nix
/home/mbrock/nixpkgs/pkgs/stdenv/cross/default.nix
/home/mbrock/nixpkgs/pkgs/stdenv/default.nix
/home/mbrock/nixpkgs/pkgs/top-level/stage.nix

Current filnix implementation:

/home/mbrock/filnix/flake.nix (already uses custom stdenv override)
/home/mbrock/filnix/README.md
/home/mbrock/filnix/patches/bash-5.2.32-filc.patch

================================================================================

END OF SUMMARY

For detailed information, see the comprehensive guide in:
/tmp/filc-cross-compilation-guide.md
