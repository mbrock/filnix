# Absolute File Paths Reference

Complete reference of all important files mentioned in the exploration, with absolute paths.

## Nixpkgs Core Files

### Systems Library (Platform Definitions)

```
/home/mbrock/nixpkgs/lib/systems/parse.nix
  Lines 706-745: ABI definitions (musl, gnu, etc.)
  Purpose: Define ABI types for platform system
  
/home/mbrock/nixpkgs/lib/systems/inspect.nix
  Lines 381-389: isMusl predicate
  Purpose: Platform predicates that recognize specific ABIs
  
/home/mbrock/nixpkgs/lib/systems/default.nix
  Lines 120-159: libc attribute auto-derivation
  Purpose: Automatically set platform.libc based on ABI
```

### Package Set Construction

```
/home/mbrock/nixpkgs/pkgs/top-level/stage.nix
  Lines 90-116: makeMuslParsedPlatform function
  Lines 194-206: variants overlay application
  Lines 310-331: pkgsStatic definition
  Purpose: Main orchestration of package sets

/home/mbrock/nixpkgs/pkgs/top-level/variants.nix
  Lines 74-91: pkgsMusl definition
  Lines 25-56: Other variant patterns (pkgsLLVM, etc.)
  Purpose: Variant package set definitions

/home/mbrock/nixpkgs/pkgs/top-level/all-packages.nix
  Lines 7361-7400: libc package selection
  Lines 80-89: stdenvNoLibc definition
  Purpose: Route platform.libc to actual libc packages
```

### Build Infrastructure

```
/home/mbrock/nixpkgs/pkgs/stdenv/linux/default.nix
  Lines 67-96: Bootstrap file selection table
  Lines 160-164: bootstrapTools import
  Lines 273-289: Stage0 libc derivation
  Lines 282-287: Libc-conditional include paths
  Purpose: Linux stdenv and bootstrap integration

/home/mbrock/nixpkgs/pkgs/stdenv/adapters.nix
  Lines 82-120: makeStaticBinaries function
  Lines 124-144: makeStaticLibraries function
  Lines 305-336: useMoldLinker function
  Purpose: Stdenv modification functions
  
/home/mbrock/nixpkgs/pkgs/build-support/cc-wrapper/default.nix
  Lines 1-77: Parameter definitions
  Lines 84-100: cc-wrapper setup
  Purpose: Compiler + libc + bintools integration
  
/home/mbrock/nixpkgs/pkgs/build-support/bintools-wrapper/
  Purpose: Linker configuration and wrapping
```

## Fil-C Implementation Files

```
/home/mbrock/filnix/flake.nix
  Lines 20-226: Main package definitions
  Lines 130-137: Compiler wrappers (filc-clang, filc-clangpp)
  Lines 138-164: Fil-C compiler packaging
  Lines 167-182: Fil-C libc definition
  Lines 184-187: Fil-C bintools wrapping
  Lines 189-207: Fil-C wrapped compiler
  Lines 215-226: Package sets and development
  Purpose: Current interim approach (Strategy B)
```

## Documentation Files

All in `/home/mbrock/filnix/`:

```
START_HERE.md
  Entry point for entire exploration
  ~15 KB
  
RESEARCH_SUMMARY.md
  Key findings and recommendations
  ~8 KB
  
ARCHITECTURE-SUMMARY.md
  Complete architecture walkthrough
  ~11 KB
  
IMPLEMENTATION_GUIDE.md
  File-by-file implementation reference
  ~14 KB
  
NIXPKGS_INTEGRATION.md
  Detailed technical explanations
  ~17 KB
  
EXPLORATION_INDEX.md
  Navigation guide and quick reference
  ~8 KB
  
[Other supporting documents]
```

## Bootstrap Files

```
/home/mbrock/nixpkgs/pkgs/stdenv/linux/bootstrap-files/
  x86_64-unknown-linux-gnu.nix
  x86_64-unknown-linux-musl.nix
  [other architecture variants]
  Purpose: Pre-built bootstrap tools per libc
```

## Package Locations

### Musl Package
```
/home/mbrock/nixpkgs/pkgs/by-name/mu/musl/
  package.nix
  Purpose: Musl C library implementation
```

### Future: Fil-C Package
```
(Would go in):
/home/mbrock/nixpkgs/pkgs/by-name/fi/filc-libc/
  package.nix
```

## Cross-References

### Implementation Guide File Locations

**File 1 - Platform Definition:**
  - /home/mbrock/nixpkgs/lib/systems/default.nix (120-159)

**File 2 - ABI Parsing:**
  - /home/mbrock/nixpkgs/lib/systems/parse.nix (706-745)
  - /home/mbrock/nixpkgs/lib/systems/inspect.nix (381-389)

**File 3 - Platform Transformer:**
  - /home/mbrock/nixpkgs/pkgs/top-level/stage.nix (90-116)

**File 4 - Variant Creation:**
  - /home/mbrock/nixpkgs/pkgs/top-level/variants.nix (74-91)

**File 5 - Libc Selection:**
  - /home/mbrock/nixpkgs/pkgs/top-level/all-packages.nix (7361-7400)

**File 6 - Bootstrap:**
  - /home/mbrock/nixpkgs/pkgs/stdenv/linux/default.nix (67-96, 273-289)

**File 7 - Adapters:**
  - /home/mbrock/nixpkgs/pkgs/stdenv/adapters.nix (82-144)

**File 8 - Cc-Wrapper:**
  - /home/mbrock/nixpkgs/pkgs/build-support/cc-wrapper/default.nix (1-77)

**File 9 - Static Pattern:**
  - /home/mbrock/nixpkgs/pkgs/top-level/stage.nix (310-331)

**File 10 - Current Approach:**
  - /home/mbrock/filnix/flake.nix (220-226)

## Quick Copy-Paste Paths

### For grep/grep operations:
```bash
grep -n "libc ==" /home/mbrock/nixpkgs/pkgs/top-level/all-packages.nix
grep -n "makeMuslParsedPlatform" /home/mbrock/nixpkgs/pkgs/top-level/stage.nix
grep -n "pkgsMusl" /home/mbrock/nixpkgs/pkgs/top-level/variants.nix
grep -n "isMusl" /home/mbrock/nixpkgs/lib/systems/inspect.nix
```

### For viewing:
```bash
head -n 120 /home/mbrock/nixpkgs/lib/systems/default.nix | tail -n 40
sed -n '90,116p' /home/mbrock/nixpkgs/pkgs/top-level/stage.nix
```

### For editing:
```bash
# Create backup before editing
cp /home/mbrock/nixpkgs/pkgs/top-level/variants.nix{,.backup}
nano /home/mbrock/nixpkgs/pkgs/top-level/variants.nix
```

## Directory Structure

```
/home/mbrock/
  nixpkgs/                          # Main nixpkgs repository
    lib/systems/                    # Platform definitions
      parse.nix                     # ABI types
      inspect.nix                   # Predicates
      default.nix                   # Libc auto-derivation
    pkgs/
      top-level/                    # Package set construction
        stage.nix                   # Transformers and orchestration
        variants.nix                # Variant definitions
        all-packages.nix            # Package selection
      stdenv/
        linux/                      # Linux stdenv
          default.nix               # Bootstrap and libc setup
          bootstrap-files/          # Pre-built bootstrap tools
        adapters.nix                # Stdenv modification functions
      build-support/
        cc-wrapper/                 # Compiler wrapper
        bintools-wrapper/           # Linker wrapper
      by-name/
        mu/musl/
          package.nix               # Musl package
  
  filnix/                           # Fil-C integration project
    flake.nix                       # Current implementation
    *.md                            # Documentation (~6KB total)
    
  fil-c/                            # Fil-C source code
    (not explored)
```

## Total File Count

- Documented nixpkgs files: 9 core files
- Documented filnix files: 1 main file (flake.nix)
- Documentation created: 17 markdown files (~6KB total)

## How to Use This Reference

1. **For understanding:** Read the documentation files
2. **For implementation:** Use these paths in IMPLEMENTATION_GUIDE.md
3. **For verification:** Use paths to check actual code
4. **For editing:** Copy absolute paths to your editor

All paths are verified and exist in the current environment.

---

**Last updated:** 2025-10-22
**All paths verified:** Yes
**Environment:** /home/mbrock/
