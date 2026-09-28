# A Fil-C userland for finix

`finixModules.filc-userland` ([finix/userland.nix](../finix/userland.nix))
builds a [finix](https://github.com/finix-community/finix) system's whole
userland with Fil-C. finix modules take their packages from `pkgs`, which is
just `config.nixpkgs.pkgs`; the module sets that to a Fil-C package set, so
finit, busybox, bash, coreutils, util-linux, OpenSSH, sudo, Linux-PAM, D-Bus,
dhcpcd, mdevd, sysklogd, Python, Perl, git and the rest become Fil-C builds
without a per-service override.

```nix
nixosConfigurations.host = finix.lib.finixSystem {
  inherit (nixpkgs) lib;
  modules = [
    filnix.finixModules.filc-userland
    {
      filc.userland = {
        enable = true;
        system = "aarch64-linux";
        # Your own Nixpkgs: native packages come from its binary cache.
        nativePackages = import nixpkgs { system = "aarch64-linux"; };
        native = [ "tailscale" ];
      };
    }
    ./configuration.nix
  ];
};
```

## What stays native

A process is either all Fil-C or all native: a Fil-C program cannot load a
native library, nor the other way round. So exceptions are whole packages,
listed by top-level attribute in `filc.userland.native` and taken from
`filc.userland.nativePackages`. The module always adds:

| Attribute | Why |
| --- | --- |
| `linuxKernel`, `linuxPackages*` | Fil-C cannot build the kernel |
| `limine`, `sbctl`, `efibootmgr` | the bootloader and its install hook |
| `userborn` | finix creates users with it during activation; Rust |
| `pkgsStatic` | the setuid wrappers are static; Fil-C does not link statically |
| `glibc` | only the wrappers use it, for a header from its source |
| `nix` | unless `nativeNix = false`: the Fil-C Nix cannot sandbox builds |

Everything else is Fil-C, and nothing Rust or Go can slip in unnoticed:
`mkPkgsFilc { blockRustGo = true; }` ([lib/block-rust-go.nix](../lib/block-rust-go.nix))
gives every derivation built with rustc, cargo or go a `broken` problem, so
evaluation stops with

```
error: Refusing to evaluate package 'ripgrep-15.1.0' … because it has problems:
- filc (kind "broken"): Rust has no Fil-C target. Use the native build instead (filc.userland.native in finix), or leave it out.
```

The adapter only touches `meta`, so derivations hash the same as in the
plain `pkgsFilc`. Haskell (cachix, pandoc) and Zig (ghostty) are not
detected; name them in `native` too.

## Checking the result

[finix/filc-audit.sh](../finix/filc-audit.sh) classifies every ELF file in a
closure by whether it uses the Fil-C loader or libpizlo:

```sh
finix/filc-audit.sh ./result
```

It also finds packages built by the Fil-C stdenv that came out native. filcc
has no target prefix, so a build that runs plain `cc` or `gcc` can pick up the
build platform's compiler from `depsBuildBuild`. busybox did, until its port
named the compiler; any Fil-C-named package in the "native" list deserves a
look.

## Nixpkgs revisions

`nativePackages` defaults to `pkgsFilc.pkgsBuildBuild`, the fully native stage
of filnix's own Nixpkgs. Not `buildPackages`: its target platform is Fil-C,
which matters for any package that is itself a compiler (Emacs' native
compilation pulled in a Fil-C-targeted libgccjit that way). Passing your own
Nixpkgs, as above, keeps the kernel and the other native packages identical to
the rest of your machines.
