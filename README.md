# Fil-C as a Nix C/C++ toolchain and cross platform

<table>
  <tr>
    <td width="50%">
      <img src="screenshots/filc-lighttpd.png" alt="Lighttpd demo homepage">
      <p align="center"><i>Lighttpd demo homepage</i></p>
    </td>
    <td width="50%">
      <img src="screenshots/filc-cgi-bug.png" alt="Memory safety in action">
      <p align="center"><i>Fil-C thwarting out-of-bounds access</i></p>
    </td>
  </tr>
  <tr>
    <td width="50%">
      <img src="screenshots/filc-figlet-cgi.png" alt="Figlet font gallery">
      <p align="center"><i>Figlet font gallery (streaming ASCII art)</i></p>
    </td>
    <td width="50%">
      <img src="screenshots/filc-qemu-boot.png" alt="QEMU boot">
      <p align="center"><i>QEMU VM boot sequence</i></p>
    </td>
  </tr>
</table>

## What's This Repo?

This repository packages [Fil-C](https://github.com/pizlonator/fil-c) (memory-safe C/C++) as Nix derivations. It contains:

1. **Core toolchain packaging** - the Fil-C compiler, runtime, and build infrastructure
2. **Ports overlay** - minimal changes to build 100+ nixpkgs packages with memory safety
3. **Playground** - demos, integration tests, and experiments (web servers, VMs, dev environments)

Parts 1 and 2 are designed for eventual nixpkgs integration. Part 3 is where we explore what's possible.

## What is Fil-C?

[Fil-C](https://github.com/pizlonator/fil-c) by [Filip Pizlo](https://twitter.com/filpizlo) is a memory-safe C/C++ compiler. It prevents use-after-free, buffer overflows, and type confusion through runtime bounds checking and garbage collection - no code changes, no unsafe escape hatches. See [fil-c.org](https://fil-c.org) and the [upstream repo](https://github.com/pizlonator/fil-c) for details on how it works.

## Binary Cache

The `filc` Cachix cache has prebuilt binaries for the toolchain and many ported packages:

```bash
cachix use filc
```

Building from source on a fresh system means waiting for LLVM to compile, then glibc twice, coreutils, Perl, bash, and so on and on. This can be fascinating and inspiring but you may prefer to use the cache and see results immediately.

Most packages mentioned `ports.nix` should have binaries available. If you're building something that's not cached yet, it'll fall back to building from source automatically.

Please note that the binary cache and the artifacts cached thereupon are provided by yours truly for entertainment purposes only, with absolutely no kind of implicit warranty and no actual security auditing or any kind of rigorous principled approach at all.

## Why Nix?

This repository packages Fil-C as reproducible Nix derivations. The [upstream](https://github.com/pizlonator/fil-c) is a development repo with shell-script builds and 100+ vendored projects. This flake takes a different approach: it's modular (compiler separate from applications), reproducible (hermetic builds, binary caching), and integrates with the ecosystem (port any nixpkgs package via cross-compilation). Memory-safe and regular packages coexist peacefully via `/nix/store` paths, everything stays moisturized and flourishing.

### Why Cross-Compilation Integration?

By treating Fil-C as a cross-compilation target, nixpkgs dependency resolution works automatically. When you port one package, you accidentally port its entire dependency tree.

**Transitive dependencies**: Want Python with a web stack? Write this:

```nix
python3.withPackages (ps: with ps; [
  uvicorn starlette msgspec pycairo
  networkx pyvis ipython
])
```

You get 40+ Python packages plus their C dependencies built with Fil-C automatically. CPython itself, pycairo, msgspec, markupsafe - but also cairo, pixman, fontconfig, freetype, libpng, glib, sqlite, gdbm, bzip2, brotli, xz, and the entire X11 graphics stack (libX11, libXext, libXrender, libxcb). You didn't set out to port fontconfig or pixman or libXdmcp - they came along because pycairo needs cairo needs fontconfig needs freetype needs libpng. Check [demo/python-web-demo-deps.graphml](demo/python-web-demo-deps.graphml) for the full transitive dependency graph (spoiler: it includes dejavu-fonts-minimal, mailcap, and tzdata).

Sure, to make `pycairo` work you need a `ports.nix` entry that disables some tests and adds cairo as a dependency. But once you do, everything that depends on it builds automatically. The [demo/app.py](demo/) web app with SQLite, JSON, graphics rendering, and more builds by listing 8 top-level packages - the transitive closure brings in dozens more.

**Language ecosystems**: Perl with XS modules works the same way. Port `perl` once (with tests disabled, some configure flags tweaked), and the [demo/perl/](demo/perl/) shows JSON::XS, XML::LibXML, DBD::SQLite, Compress::Zlib, and Inline::C all working. Each C extension needs its own `ports.nix` entry (pin version, apply patch, skip incompatible tests), but once defined, they compose freely.

**System composition**: Building a container with bash, coreutils, git, OpenSSL, lighttpd, SQLite, Lua, Perl, Python? List the top-level packages, let dependency resolution handle the rest. Everything links against the same memory-safe libc and runtime because it's cross-compilation - not ad-hoc wrappers.

Yes, most packages need *some* porting work (check `ports.nix` - it's full of `skipTests`, configure flags, dependency tweaks). But you do that work once per package, not once per composition. That's the win: porting effort is proportional to the number of unique packages, not the number of ways you combine them.

### Repository Structure

This repo has three distinct parts with different purposes:

**1. Core Toolchain** (`compiler/`, `toolchain/`, `runtime/`)

The foundation: packaging the Fil-C compiler (modified LLVM/Clang), binutils, sysroot, runtime libraries (libpas, FUGC), and build wrappers as Nix derivations. This is the "hard" part that transforms upstream fil-c's shell scripts into reproducible Nix builds.

**2. Ports Overlay** (`ports/`, `ports.nix`, `pyports.nix`)

A clean DSL and overlay machinery that makes nixpkgs packages build with Fil-C. The philosophy: apply the *smallest possible changes* - pin versions to match upstream fil-c patches, apply those patches, tweak build flags, skip incompatible tests. The DSL (`for`, `pin`, `patch`, etc.) makes porting readable and maintainable.

The `ports/patch/` directory contains auto-generated patches extracted from upstream fil-c's monorepo. A script diffs each project subdirectory in upstream's `projects/` tree (with filtering logic) and generates patch files. This bridges the gap: upstream vendors entire source trees, we apply patches to nixpkgs packages. As coverage expands, the goal is to need fewer and fewer manual interventions.

**3. Playground & Demos** (`httpd/`, `virt/`, `demo/`, `emacs/`, `ttyd-demo/`)

Integration tests, experiments, and explorations of what memory-safe systems can look like. Web servers with CGI scripts, QEMU VMs, Docker containers, development environments, terminal demos. This is where we test if the toolchain actually works for realistic use cases and where interesting/fun/valuable applications emerge.

**Path to Nixpkgs**: Parts 1 and 2 are designed for upstream integration. Hacking in this dedicated repo is more convenient and intelligible than working in the massive nixpkgs tree, but the architecture (cross-compilation, minimal patches, overlay structure) is built to merge. If the community finds this valuable, it could mean first-class platform support, Hydra CI, official binary caching, and more. Part 3 stays here as the laboratory.

### Cross-Compilation Architecture

Fil-C uses Nix's cross-compilation infrastructure (`x86_64-unknown-linux-gnufilc0`) with a lightly-patched nixpkgs fork that recognizes the `gnufilc0` ABI tag. The flake imports nixpkgs with `crossSystem.config` set and uses `replaceCrossStdenv` to inject a custom `stdenv` wrapping the Fil-C compiler. The ports overlay applies patches and configuration to nixpkgs packages, allowing most packages to build with minimal changes. The fork's patches are minimal (gnu-config awareness, ABI tag recognition), making future nixpkgs integration straightforward.

## What's Fun Here

### Interactive Memory Safety Demo

The [lighttpd demo](httpd/) runs a complete memory-safe web stack:

```bash
nix run .#lighttpd-demo
```

It's lighttpd compiled with Fil-C, serving CGI scripts in bash and C (both memory-safe), with WebDAV (digest auth), compression (brotli, zstd, bzip2, gzip — all Fil-C). The interactive demo invites you to trigger out-of-bounds access.

The [demo.c](httpd/src/demo.c) CGI has an array of 5 fruits. Try `?index=999` — Fil-C traps it instead of crashing:

```c
const char *fruits[] = {"apple", "banana", "cherry", "date", "elderberry"};
// This will trap with Fil-C:
const char *result = fruits[index];  // index=999
```

The [figlet.sh](httpd/src/figlet.sh) script demonstrates memory-safe bash calling memory-safe figlet, processing results with memory-safe sed/awk, and escaping output with a memory-safe C program.

### Containers & VMs

I'm experimenting with defining a minimal "Linux distribution"
with `runit` as PID1 and a `/bin` full of memory safe goodies.

It's not exactly NixOS, but it's fun and might somehow be useful
for something.

```bash
nix run .#run-filc-docker     # Docker container
nix run .#run-filc-sandbox    # systemd-nspawn
nix run .#run-filc-qemu       # QEMU VM (builds disk image)
```

Each boots into a curated environment with bash, coreutils, tmux, git, curl, OpenSSL, lighttpd web server, SQLite, Lua, Perl, Prolog, and more — all memory-safe.

### Novel Ports

Packages ported here that aren't in upstream fil-c:

| Package | Description |
|---------|-------------|
| lighttpd | HTTP server with mod_cgi, WebDAV, compression |
| nethack | Nobody's ascended in Fil-C Nethack yet... |
| kitty-doom | Console DOOM |
| wasm3 | WebAssembly runtime (see [CVE demos](#cve-prevention-wasm3)) |
| trealla | ISO Prolog with Fil-C FFI integration |
| figlet | ASCII art generator |

### Ports Analysis

The [ports/analysis.md](ports/analysis.md) document is a technical deep-dive generated by squads of Claude AI agents that analyzed every patch from upstream fil-c's 100+ ported projects. Each agent analyzed a subset of patches, then another agent synthesized the findings into a comprehensive guide. It covers systematic porting patterns (pointer tables, tagged pointers, alignment), case studies of major refactors (Python GC, Emacs memory manager, Perl XS), common mistakes and how to avoid them. The scale: 21,000 lines of analyzed changes across projects from dash to systemd. It's both a practical porting guide and a view into what real-world C code assumes about memory.

### Port Configuration DSL

The [ports.nix](ports.nix) file uses a clean DSL for porting packages. It's now structured as a list that gets automatically converted to an overlay:

```nix
# Simple list-based port definitions
[
  # Basic port with version pinning and patches
  (for pkgs.zlib [
    (pin "1.3" "sha256-/wukwpIBPbwnUws6geH5qBPNOd4Byl4Pi/NVcC76WT4=")
    (patch ./ports/patch/zlib-1.3.patch)
  ])

  # Port with explicit name and dependencies
  {
    lighttpd = for ./ports/lighttpd.nix [
      (patch ./ports/patch/lighttpd-6a4880a.patch)
      (addCFlag "-Wno-unused-but-set-variable")
    ];
  }

  # Port with tests disabled
  (for pkgs.sqlite [
    (patch ./ports/patch/sqlite.patch)
    (skipCheck "TCL test harness needs adaptation")
  ])
]
```

The DSL includes helpers for version pinning (`pin`), patching (`patch`), configure flags (`configure`, `addCFlag`, `addCMakeFlag`), and test control (`skipTests`, `skipCheck`). The [ports/default.nix](ports/default.nix) file implements the overlay machinery that converts these declarations into working package overrides.
