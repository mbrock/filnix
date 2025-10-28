# Filnix - Nix Packaging for Fil-C

## What is Fil-C?

**Fil-C** is a memory-safe implementation of C and C++ created by Filip Pizlo. It achieves complete memory safety while remaining **fanatically compatible** with existing C/C++ code. The key principle: **GIMSO (Garbage In, Memory Safety Out)** — even adversarial or buggy C code cannot escape Fil-C's safety guarantees.

### Key Facts

- **Based on**: LLVM/Clang 20.1.8 (supports C17, C++20)
- **No escape hatches**: No `unsafe` keyword — memory safety cannot be bypassed
- **Production-ready**: Successfully runs OpenSSL, CPython, OpenSSH, curl, SQLite, Emacs, and 100+ other programs
- **Platform**: Linux/X86_64 only
- **Performance**: 1.5x - 4x overhead vs unsafe C
- **Upstream**: https://github.com/pizlonator/fil-c

### How Fil-C Works

Fil-C has three main components:

1. **FilPizlonator LLVM Pass**: Instruments all LLVM IR to track capabilities alongside pointers
   - Every pointer becomes (value, capability) pair
   - Bounds checks inserted before every memory access
   - All pointers tracked for garbage collection

2. **InvisiCap Runtime**: Novel pointer representation using "invisible capabilities"
   - Pointers in registers: stored as two values (address + capability)
   - Pointers in memory: address in primary space, capability in shadow space
   - Capability contains bounds (lower/upper) and type information
   - Use-after-free prevented: freed objects have `upper = lower`, causing all accesses to trap

3. **FUGC Garbage Collector**: Built on libpas allocator infrastructure
   - **libpas**: Phil's Awesome System - configurable memory allocator from WebKit
   - fil-c extends libpas with new "verse_heap" configuration for GC
   - Concurrent, parallel marking with no stop-the-world pauses
   - Keeps freed objects alive until all references die
   - Guarantees use-after-free detection
   - Optional `free()` — can rely purely on GC

### Memory Safety Guarantees

Fil-C prevents:
- **Use-after-free**: Freed objects trapped until GC collects
- **Out-of-bounds access**: All accesses checked against capability bounds
- **Type confusion**: Type information tracked in capabilities
- **Pointer races**: Atomic operations on capabilities
- **Syscall violations**: Runtime wrappers validate all syscalls

## This Repository (mbrock/filnix)

This Nix flake packages the Fil-C compiler toolchain for reproducible, hermetic builds.

### Relationship to Upstream

**Upstream fil-c** (pizlonator/fil-c):
- Development repository for Fil-C compiler
- Shell-script-based build system (`build_all.sh`, etc.)
- Monolithic: includes compiler + 100+ ported programs
- Self-contained but not reproducible
- Rapid personal-project iteration

**This repository** (mbrock/filnix):
- Nix packaging of fil-c compiler and runtime
- Transforms shell scripts into Nix derivations
- Modular: separates compiler from applications
- Reproducible, cacheable builds
- Integration with Nix ecosystem

### Ported Software

The `ports/` directory contains patches from upstream fil-c for building software with memory safety:

- **ports/patches.nix**: Maps package names to versions and patches
- **ports/patch/*.patch**: Individual patches for each ported package
- **ports.nix**: Nix expressions that apply these patches to nixpkgs packages

The porting workflow extracts patches from upstream fil-c's vendored sources and applies them to standard nixpkgs packages, enabling memory-safe builds without vendoring source code.

### What This Packages

From the upstream fil-c repository, we package:

1. **Modified LLVM/Clang** with FilPizlonator pass
2. **Runtime libraries**: libpas, FUGC, Fil-C runtime
3. **Standard libraries**: libc++, musl (or glibc)
4. **System headers** and build infrastructure

### Build Structure

The upstream fil-c build process has these stages:

1. Configure LLVM with CMake
2. Build Clang with FilPizlonator instrumentation pass
3. Build OS includes (Linux headers)
4. Build libc (musl or glibc) with memory safety
5. Build Fil-C runtime and FUGC
6. Build libcxx (C++ standard library)

This flake replicates these stages as Nix derivations.

### Key Files in This Repo

- **flake.nix**: Main Nix flake exposing fil-c packages
- **fil-c-combined.nix**: Combined LLVM/Clang build (stages 1-2)
- **fil-c-helpers.nix**: Helper functions for derivations
- **fil-c-projects.nix**: Packaging for ported software
- **packages.nix**: Sample packages built with Fil-C (bash, lua, tmux, etc.)
- **ports.nix**: Ported packages using patches from upstream fil-c
- **query-package.nix**: Introspection tool for nixpkgs packages
- **query-package.sh**: Shell wrapper for package queries

### Build Commands

From upstream, these are the main build entry points:

- `build_all_fast.sh`: Quick build (compiler + runtime only)
- `build_all.sh`: Full build including ported software
- `build_all_glibc.sh`: Build with glibc instead of musl
- `build_base.sh`: Core build stages (called by others)

Our Nix derivations replicate what these scripts do.

### Build Requirements (Upstream)

Fil-C requires specific versions:
- CMake 3.22+
- m4 1.4.19, autoconf 2.72, automake 1.17, libtool 2.4.7
- Modern C++ compiler (to bootstrap)
- Linux/X86_64

## Package Introspection

The repository includes tooling to query comprehensive package metadata from nixpkgs:

### Query a Package

```bash
# Via shell script (uses flake's pinned nixpkgs)
./query-package.sh bash | jq .

# Via flake directly
nix eval --json .#lib.x86_64-linux.queryPackage --apply 'f: f "bash"'
```

### What It Returns

The query tool extracts complete build metadata:

- **functionArgs**: Required/optional parameters from package definition
- **buildInputs**: Native, build, and propagated inputs (with type: derivation/setup-hook)
- **buildConfig**: configureFlags, makeFlags, cmakeFlags, mesonFlags, patches
- **buildFlags**: outputs, doCheck, parallelization, hardening settings
- **nixVars**: NIX_CFLAGS_COMPILE, NIX_HARDENING_ENABLE, etc.
- **derivation**: Actual build structure (builder, args, custom build phases)
- **meta**: description, homepage, license, platforms, maintainers

This is useful for understanding how nixpkgs builds packages and what needs to be adapted for Fil-C.

### Implementation

The query function uses Nix builtins to introspect package metadata:
- `builtins.functionArgs` - extract function parameters
- `pkg.buildInputs`, `pkg.nativeBuildInputs` - dependency lists
- `pkg.configureFlags`, `pkg.patches` - build configuration
- `pkg.builder`, `pkg.args` - derivation structure
- `pkg.meta` - package metadata

No dependency on external tools - pure Nix introspection.

## Resources

- Upstream repository: https://github.com/pizlonator/fil-c
- Fil-C documentation: See upstream README
- LLVM/Clang docs: https://llvm.org/docs/
- libpas (runtime): From WebKit project, where Filip Pizlo led GC and compiler development

## Known Issues from Upstream

- **Platform support**: Linux/X86_64 only
- **Performance tuning**: Ongoing work to reduce overhead
- **Compiler compatibility**: Based on Clang 20.1.8, not latest
