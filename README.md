# filnix — Fil-C as a Nix toolchain

[Fil-C](https://github.com/pizlonator/fil-c) is Filip Pizlo's memory-safe implementation of C and C++. Every
pointer carries an invisible capability, every access is bounds-checked, and a
concurrent garbage collector turns use-after-free into a clean trap. Ordinary
C code compiles unchanged, or nearly so, and there is no `unsafe` escape hatch.

This flake builds the Fil-C toolchain with Nix and plugs it into nixpkgs as a
cross-compilation target. You get `pkgsFilc`: a package set in which
everything, including libc, is compiled with Fil-C.

The ordinary `filcc` compiler and `pkgsFilc` package set track official Fil-C
releases, currently [0.686](https://github.com/pizlonator/fil-c/releases/tag/v0.686). Compiler/runtime experiments are opt-in through
`filcc-staging` and `pkgsFilcStaging`, on the same Filnix `main` branch.

The flake exports `x86_64-linux` and `aarch64-linux` outputs. ARM64 remains
experimental; see [the toolchain notes](docs/upstream-updates.md) for validation limits.

## Quick start

Use the binary cache to avoid building LLVM and glibc yourself:

``` bash
cachix use filc
```

Compile a program directly:

``` bash
nix run github:mbrock/filnix#filcc -- hello.c -o hello
nix run github:mbrock/filnix#filc++ -- hello.cc -o hello
```

Build a package from nixpkgs with Fil-C:

``` bash
nix build github:mbrock/filnix#pkgsFilc.sqlite
nix build github:mbrock/filnix#pkgsFilc.python3
```

Or open a shell with a curated set of memory-safe tools:

``` bash
nix run github:mbrock/filnix#baseline
```

### Installing the compiler

`filcc` is a self-contained toolchain: a wrapped Clang with the Fil-C runtime,
libc and libc++, plus binutils. Install it into your profile:

``` bash
nix profile add github:mbrock/filnix#filcc
cc hello.c -o hello
c++ hello.cc -o hello
```

It provides `cc`, `c++`, `clang`, `clang++`, `ld` and the other binutils, so
it will shadow any compiler already on your `PATH`. Binaries it produces load
Fil-C's own dynamic linker and libc from the Nix store, so they run on any
x86_64 Linux machine that has those store paths.

### Experimental staging toolchain

Use staging explicitly for compiler experiments and package-build campaigns:

``` bash
nix run github:mbrock/filnix#filcc-staging -- hello.c -o hello
nix run github:mbrock/filnix#filc++-staging -- hello.cc -o hello
nix build github:mbrock/filnix#pkgsFilcStaging.sqlite
```

In a consuming flake, select `filnix.legacyPackages.x86_64-linux.pkgsFilcStaging`
instead of `pkgsFilc`. Campaigns using `lib.${system}.mkPkgsFilc` can pass
`staging = true;` alongside their existing options. Compiler, runtime, libc,
libc++ and assembler all come from that variant; do not mix libraries from
the two package sets. Ordinary packages, demos and NixOS modules stay on the
release toolchain, with no automatic fallback to staging.

Staging preserves our fork's union/varargs experiments and residual runtime
fixes, including the local cancellation patches. It is not a supported release
or a memory-safety guarantee. The current snapshot even predates 0.686's tighter
`zunsafe_*` opt-in. See [the release/fork comparison and update workflow](docs/upstream-updates.md).

### Using it in your own project

Build your project with `pkgsFilc` and its libraries come from `pkgsFilc`
too, so the whole program is memory safe:

``` nix
{
  inputs.filnix.url = "github:mbrock/filnix";

  outputs = { filnix, ... }:
    let
      pkgsFilc = filnix.legacyPackages.x86_64-linux.pkgsFilc;
    in {
      packages.x86_64-linux.default = pkgsFilc.stdenv.mkDerivation {
        pname = "hello";
        version = "0.1";
        src = ./.;
        nativeBuildInputs = [ pkgsFilc.buildPackages.pkg-config ];
        buildInputs = [ pkgsFilc.zlib ];
        buildPhase = ''
          $CC -O2 hello.c -o hello $(pkg-config --cflags --libs zlib)
        '';
        installPhase = "install -Dm755 hello $out/bin/hello";
      };

      devShells.x86_64-linux.default = pkgsFilc.mkShell {
        nativeBuildInputs = [ pkgsFilc.buildPackages.pkg-config ];
        buildInputs = [ pkgsFilc.zlib ];
      };
    };
}
```

Projects that use CMake, Meson or Autotools work the same way. Add the tool to
`nativeBuildInputs` and let the usual `stdenv` phases run. Tools in
`nativeBuildInputs` come from `pkgsFilc.buildPackages` and run natively.
Everything in `buildInputs` is compiled with Fil-C.

### NixOS

`nixosModules.filc` swaps chosen NixOS services and programs for their Fil-C
builds and leaves the rest of the system alone:

``` nix
{
  imports = [ filnix.nixosModules.filc ];
  filc.enable = true;                   # sshd, Bash, Tor, Unbound, lighttpd, Nix
  filc.tools = [ "coreutils" "curl" ];  # Fil-C programs on PATH
  services.openssh.enable = true;
}
```

A demo VM runs the Fil-C sshd, Bash, Unbound, lighttpd and Nix:

``` bash
nix run github:mbrock/filnix#nixosConfigurations.filc-demo.config.system.build.vm
ssh -p 2222 demo@localhost   # password "demo"
```

See [docs/nixos.md](docs/nixos.md). `pkgsFilc.nix` is Nix itself built
with Fil-C; it passes Nix's unit and functional tests.

## How it works

### The toolchain

`toolchain.nix` turns upstream's shell-script build into a chain of
derivations:

| Stage | File | What it is |
|----|----|----|
| `filc0` | `compiler/filc0.nix` | Clang 20 with the FilPizlonator pass |
| `yolo-glibc` | `runtime/yolo-glibc.nix` | Unsafe glibc underneath the runtime |
| `compiler-rt` | `runtime/compiler-rt.nix` | CRT files and builtins |
| `libpizlo` | `runtime/libpizlo.nix` | Runtime: libpas, FUGC collector, syscall wrappers |
| `filc-glibc` | `runtime/filc-glibc.nix` | glibc compiled with Fil-C |
| `libcxx` | `compiler/libcxx.nix` | libc++ and libc++abi compiled with Fil-C |
| sysroot, binutils | `toolchain/` | Headers, libraries and the Fil-C dynamic loader |
| `filcc` | `toolchain/wrappers.nix` | A standard nixpkgs `cc-wrapper` around all of it |

`filcc` is an ordinary nixpkgs C compiler that happens to emit memory-safe
code, so `pkgs.overrideCC stdenv filcc` works as you would expect.

Each toolchain uses one Fil-C monorepo revision. `lib/filc-upstream.json` pins
the exact official release commit; `lib/filc-staging.json` independently pins
our [fork](https://github.com/mbrock/fil-c). The same derivations build both. The official toolchain retains Nix
path, wrapper and locale integration, but not our unmerged compiler/runtime
semantic changes. Only the relevant subtrees are hashed, so changes elsewhere
in upstream do not rebuild the compiler. To work on the compiler without
rebuilding it from scratch, see [docs/llvm-dev.md](docs/llvm-dev.md).

### pkgsFilc

The flake imports nixpkgs as a cross build for
`x86_64-unknown-linux-gnufilc0`, with `filcc` as the cross `stdenv`:

``` nix
pkgsFilc = import nixpkgs {
  localSystem = "x86_64-linux";
  crossSystem.config = "x86_64-unknown-linux-gnufilc0";
  config.replaceCrossStdenv = { baseStdenv, ... }:
    baseStdenv.override { cc = filcc; };
  crossOverlays = [ (import ./ports/overlay.nix pkgs) ];
};
```

The `gnufilc0` ABI tag is recognized by a lightly patched nixpkgs,
[lessrest/filnixpkgs](https://github.com/lessrest/filnixpkgs), which adds only
the platform definition and gnu-config support.

Because Fil-C is a cross target, nixpkgs does the dependency resolution. Build
tools such as Perl, CMake, Meson and Python still run natively. Everything
that ends up in a runtime closure is compiled with Fil-C and linked against
the same Fil-C glibc. Porting a library therefore ports it for every package
that depends on it: `python3.withPackages (ps: [ ps.pycairo ])` also builds
cairo, fontconfig, freetype, libpng, glib and the X11 client libraries with
Fil-C.

The flake exports `legacyPackages.x86_64-linux.pkgsFilc`, and
`overlays.default` if you want to build your own package set.

### Ports

Most C code builds unchanged. The rest gets the smallest adjustment that
works, declared in `ports.nix` with a small DSL from `ports/default.nix`:

``` nix
(for pkgs.zlib [
  (pin "1.3" "sha256-/wukwpIBPbwnUws6geH5qBPNOd4Byl4Pi/NVcC76WT4=")
  (patch ./ports/patch/zlib-1.3.patch)
])
```

The helpers pin versions, apply patches, adjust C/configure/CMake/Meson flags,
and skip tests that probe unsupported behavior, recording the reason for each
skip. `ports/overlay.nix` turns the list into an overlay. Python and Ruby
extensions have their own lists in `pyports.nix` and `rubyports.nix`.

Upstream Fil-C ports software by vendoring whole source trees. `ports/patch/`
holds those changes extracted as patches against the release tarballs, so they
apply to nixpkgs' own sources. The extraction revision is pinned separately
from the compiler in `ports/upstream.json`; see [docs/upstream-updates.md](docs/upstream-updates.md).

## Status

A continuous build campaign tries to build all of nixpkgs with Fil-C. Its live
dashboard is at <https://nix.swa.sh/>. The current campaign builds the
nixos-26.05 package set (14,647 attributes) with Fil-C `eb534be`.

Many blocked packages wait on the same few shared dependencies, so fixing one
of those can unblock a large group at once. The dashboard's Blockers tab ranks
failures by how many packages they block, and links each result to its logs,
test evidence and dependency graph.

## Binary cache

`cachix use filc` gives you prebuilt outputs for the toolchain and for
everything the campaign has built. A cached output only shows that a package
built. It does not show that its tests pass. These binaries are provided for
fun, without warranty and without any security audit.

## Development

``` bash
nix develop               # formatting and Nix tooling
nix develop .#world       # a shell with filcc and many Fil-C libraries
nix flake check           # focused runtime tests under tests/
```

The rest of the repository contains experiments built on top of the toolchain:
demos, VM and container images, an Emacs build, campaign infrastructure, and
porting notes. The notes live in [docs/](docs/).
