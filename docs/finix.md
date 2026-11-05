# A Fil-C userland for finix

`finixModules.filc-userland` ([finix/userland.nix](../finix/userland.nix))
builds a [finix](https://github.com/finix-community/finix) system's whole
userland with Fil-C. finix modules take their packages from `pkgs`, which is
just `config.nixpkgs.pkgs`; the module sets that to a Fil-C package set, so
finit, busybox, bash, coreutils, util-linux, OpenSSH, sudo, Linux-PAM, D-Bus,
dhcpcd, mdevd, sysklogd, Python, Perl, git and the rest become Fil-C builds
without a per-service override.

This is the last step of the scale in [Fil-C on NixOS](nixos.md#how-far-to-go).
`nixosModules.filc` adds Fil-C services and programs to a native NixOS one at
a time. Here everything starts as Fil-C, and `filc.userland.native` names the
exceptions. `nixosModules.filc-userland` does the same for NixOS, under the
same `filc.userland` options.

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

## Example machine

[finix/demo.nix](../finix/demo.nix) is a small finix machine with this
userland, the finix counterpart of `nixosConfigurations.filc-demo`: finit as
PID 1, mdevd, sysklogd, dhcpcd, OpenSSH, sudo, the Nix daemon (native, as
above), Bash and the usual tools. It boots the kernel directly in QEMU, with a
tmpfs root and the host's Nix store over 9p:

```sh
nix run .#finixConfigurations.filc-demo.config.system.build.vm
```

Log in as root on the serial console (no password), or
`ssh -p 2222 demo@localhost` with password `demo` once dhcpcd has its lease
from QEMU. Ctrl-a x quits QEMU. It needs KVM to be usable; the first boot of
a fresh store builds the whole Fil-C userland.

The flake pins finix (the `finix` input) to the last revision before it
required finit 5; filnix's Nixpkgs has finit 4.17.

Booting it found these, now fixed:

- Fil-C's glibc stopped the program in `nftw`, `scandirat` and `fts`, which
  finit (switch_root, tmpfiles), libmount, agetty and login use, and in
  `sbrk`, `sched_setattr` and `pidfd_spawn`
  ([filc-findings.md](filc-findings.md));
- finit's `clone3` call stopped PID 1; the port uses its fork fallback;
- finit's keventd wrote one byte past its uevent buffer, which Fil-C stopped
  during coldplug;
- dhcpcd's vendored rbtree kept its parent pointer in an integer; the
  upstream Fil-C port had not followed the file to `vendor/`;
- the busybox port had no applet links, so the initrd had no `sh`;
- libbsd, which ifupdown-ng (finix's test network) needs, did not build;
  its port is in [filc-findings.md](filc-findings.md).

## The check

`checks.x86_64-linux.finix-filc-demo` ([finix/test.nix](../finix/test.nix))
boots the same machine with finix's own VM test driver (its `tests/lib`, the
NixOS driver with finit support) and checks, from inside the machine:

- no finit service crashed, and dhcpcd, keventd, sshd and syslogd run;
- ifupdown-ng gave eth0 its test-network address;
- PID 1 (finit), the test shell and sshd map libpizlo, the Fil-C runtime;
- an ssh login as root gets a Bash that maps libpizlo;
- every process with a memory map maps libpizlo, except the native Nix daemon;

and, from the host, that every native ELF file in the system closure belongs
to an expected exception: the native Nix and its closure, userborn, the static
setuid wrappers, and the native Bash that Fil-C's glibc names in the shebangs
of its scripts (ldd and friends) together with its glibc.

```sh
nix build -L .#checks.x86_64-linux.finix-filc-demo
```

## Checking the result

[finix/filc-audit.sh](../finix/filc-audit.sh), also `packages.<system>.filc-audit`,
classifies every ELF file in a closure by its program headers and dynamic
section: a Fil-C executable names the Fil-C loader (ld-fil1-*.so) as its
interpreter, and a Fil-C executable or library needs libpizlo.so. That is
what the loader acts on, so a native program that merely contains those
names is not counted as Fil-C. The runtime underneath (libpizlo, the loader
and its yolo glibc) is native code that only Fil-C programs load; it is
counted apart, as are kernel modules.

```sh
nix run .#filc-audit -- ./result
nix run .#filc-audit -- --paths store-paths --allow expected-native-paths
```

With `--allow`, native files outside the listed store paths are marked
`UNEXPECTED` and the exit status is 1; the check uses that. On a running
machine the processes are the better evidence: a Fil-C process maps
libpizlo (`grep -c libpizlo /proc/PID/maps`).

The audit also finds packages built by the Fil-C stdenv that came out native.
filcc has no target prefix, so a build that runs plain `cc` or `gcc` can pick
up the build platform's compiler from `depsBuildBuild`. busybox did, until its
port named the compiler; any Fil-C-named package in the native list deserves a
look.

## Nixpkgs revisions

`nativePackages` defaults to filnix's own Nixpkgs, imported natively. Not
`buildPackages`: its target platform is Fil-C, which matters for any package
that is itself a compiler (Emacs' native compilation pulled in a
Fil-C-targeted libgccjit that way). Not `pkgsBuildBuild` either: it carries
the Fil-C set's `replaceCrossStdenv`, so its `pkgsStatic`, which finix's
setuid wrappers use, built with filcc and failed to link. Passing your own
Nixpkgs, as above, keeps the kernel and the other native packages identical to
the rest of your machines.
