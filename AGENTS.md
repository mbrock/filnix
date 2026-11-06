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

### Continuous Integration Delivery

- Treat `main` as the continuously integrated work branch, not a production release gate. Commit and push verified, scoped work to `origin` at coherent milestones without waiting for a separate user request.
- Keep commits limited to the work you own. This standing permission does not authorize force-pushing, publishing someone else's unreviewed changes, or triggering deployments and releases.
- Push with `scripts/ship`. It requires the complete foundation closures in `scripts/ship-outputs.txt` (including `filcc-staging`) through Cachix + cache.nixos.org before main advances. It checks first and builds/publishes only missing outputs, through the existing swa publisher; hosts with SSH/sudo access can publish through swa, building there if they cannot build x86_64-linux. Cache hits need no publisher. Missing outputs without a publisher stop the push; `--no-publish` skips publication, never the gate. There is no uncached-main bypass. `scripts/ship --publish-only --rev REV` repairs caches without changing refs, including an already-pushed main. Wider distributions in `scripts/ci-outputs.txt` and ports remain campaign work; follow `docs/port-campaign-operations.md`.
- Nanofil workers hand the swa lander a branch/bundle at full SHA X and `results.json` from `scripts/nanofil-fleet run --rev X --shards 6 --roots nanofil-rocq` (plus other affected roots). The lander checks out X and uses `scripts/ship --exact X --fleet-results FILE`; `--roots LIST` adds required checks, or `--roots all` requires all roots. This verifies the receipt and fast-forwards exactly X, without rebasing or repeating its fleet. If main diverges, stop, rebase before testing, and obtain a new fleet at the new SHA. Keep one normal lander on swa. Plain `scripts/ship` still rebases for work without an exact-head handoff; pre-rebase evidence does not transfer to its new SHA.
- Shipping works without `nix develop` and installs `scripts/git-hooks`: pre-commit runs treefmt; pre-push checks the committed tip in a clean worktree (foundation availability, workflow lint, Python compilation, and importer tests when ports change). Cache misses fail updates to `refs/heads/main` unconditionally; feature branches may be pushed before publication. Do not bypass these checks with Git's `--no-verify`; local hooks are accidental-push guards, not server-side authorization.
- Releases (`scripts/release`, which tags `origin/main` and triggers `.github/workflows/release.yml`) publish to GitHub and ghcr.io; cut one only when the user asks.

### Relationship to Upstream

**Upstream fil-c** (pizlonator/fil-c):

- Development repository for Fil-C compiler
- Shell-script-based build system (`build_all.sh`, etc.)
- Monolithic: includes compiler + 100+ ported programs

**This repository** (mbrock/filnix):

- Nix packaging of fil-c compiler and runtime
- Transforms shell scripts into Nix derivations
- Modular: separates compiler from applications
- Reproducible, cacheable builds
- Integration with Nix ecosystem

### Ported Software

The `ports/` directory contains patches from upstream fil-c for building software with memory safety:

- **ports/patches.nix**: Maps package names to versions and patches
- **ports/patch/\*.patch**: Individual patches for each ported package
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

### Compiler and Runtime Review

- Before adopting changes to Fil-C compiler semantics, capability tracking, GC, or glibc/runtime behavior, develop the proposed approach and consult Oracle about soundness and alternatives. Give it the relevant code and invariants while leaving room for independent analysis.
- Resolve review findings and run targeted regressions before updating the toolchain pin. Passing package tests alone does not establish memory safety. This review requirement does not apply to ordinary package-local build fixes.

### NixOS and finix: the whole system is the product

- The unit is a whole system whose `pkgs` is pkgsFilc (`nixosModules.default`, `finixModules.default`, one core in `lib/filc-system.nix`). Services are Fil-C because modules pick `pkgs.X`, not because filnix names them.
- Exceptions are the only knob. Each is a whole native package, written as a Nix value (`filc.native = native: { inherit (native) x; }`), never a string list. The built-in ones are data with a reason in `lib/native-exceptions.nix`, and the docs table is generated from it.
- No per-service or per-tool switches. If a service needs a Fil-C fix, put it in its port.
- Prove the negative: tests and machines pass when every native process is an allowed exception (`filc-ps`), not when a hand-listed set is Fil-C.
- Anything a user downloads or boots is a flake output that the campaign builds and caches. CI only substitutes it and smoke-tests it. Images ship their pinned flake and the binary cache.
- Keep the module small and readable; one Fil-C daemon on a stock NixOS is a docs recipe, not module support.

### Key Files in This Repo

- **flake.nix**: Main Nix flake exposing fil-c packages
- **ports.nix**: Main ports definition file - list of packages ported to Fil-C
- **pyports.nix**: Python packages ported to Fil-C
- **ports/**: Port infrastructure
  - **default.nix**: DSL for configuring package builds and overlay machinery
  - **overlay.nix**: Converts ports.nix to a nixpkgs overlay
  - **patch/**: Patches extracted from upstream fil-c for each ported package
- **scripts/query-package.nix**: Introspection tool for nixpkgs packages
- **scripts/query-package.sh**: Shell wrapper for package queries
- **emacs/emacs.nix**: Emacs configuration bundle for Fil-C development

## Package Introspection

The repository includes tooling to query comprehensive package metadata from nixpkgs:

### Query a Package

```bash
# Via shell script (uses flake's pinned nixpkgs)
./scripts/query-package.sh nethack
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

## Resources

- Upstream repository: https://github.com/pizlonator/fil-c
- Fil-C documentation: See upstream README
- LLVM/Clang docs: https://llvm.org/docs/
- libpas (runtime): From WebKit project, where Filip Pizlo led GC and compiler development
